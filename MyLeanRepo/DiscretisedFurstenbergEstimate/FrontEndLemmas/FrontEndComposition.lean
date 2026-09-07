module

/-
  FrontEndLemmas.FrontEndComposition

  Composition of front-end extraction pieces to prove `appendix_a_main`.

  ## Proof route (source-first exact-scale normalization)

  1. **Parameter selection**: `parameter_selection` → ε, A, η_axiom, δ₀_axiom,
     η_upper, δ₀, numerical bounds, QTTC, RKP.
  2. **Public exponent**: εA = ε/50. Internal εA_int = εA + ρ_scale = ε/25.
  3. **Exact even dyadic scale ABOVE public δ**:
     `exists_even_dyadic_scale_above` → even n, δ ≤ δ_n ≤ 4δ.
     Set m = n/2, Δ = dyadicDelta m, δ_n = dyadicDelta n = Δ².
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
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.HDyadicBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.NumericalBoundsApplication
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.FrontEndCompositionHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.RefFinTransport
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.GLemma
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.HLemma
public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.FrontLemmaI
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

set_option maxHeartbeats 1000000

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
open DirecretisedFurstenbergEstimate.AssemblyNumerical
open DirecretisedFurstenbergEstimate.AppendixA5

theorem front_end_composition
    (s t : ℝ)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (ht_pos : 0 < t) (ht_lt_two : t < 2)
    (hst : s < t) :
    ∃ (εA : ℝ), εA < 1 ∧
      UniformAppendixAAlternative (fun ℓ : AffineLine => ℓ.1) s t εA := by
  -- ========================================================================
  -- Step 1: Parameter selection
  -- ========================================================================
  rcases parameter_selection s t hs_pos hs_lt_one ht_pos ht_lt_two hst with
    ⟨ε, A, η_axiom, δ₀_axiom, η_upper, δ₀,
     hε_pos, h12ε, h576ε_lt, hε_lt_one, hε_le_one,
     hA_pos, hA_one, hη_axiom_pos, hδ₀_axiom_pos,
     hη_upper_pos, h214ε_lt, hη_upper_lt, hδ₀_pos,
     hA7, hQTTC, hRKP_data, h_num_bounds⟩

  -- ========================================================================
  -- Parameter chain (5-term ledger)
  -- 2εA + 2ρ_thin + 2ρ_config_mass + ρ_scale + ρ_orientation ≤ ε/4
  -- εA = ε/50, ρ_thin = ε/50, ρ_config_mass = ε/50, ρ_scale = ε/50, ρ_orientation = ε/100
  -- Total: 2ε/50 + 2ε/50 + 2ε/50 + ε/50 + ε/100 = 13ε/100 < ε/4 = 25ε/100 ✓
  -- ========================================================================
  let εA : ℝ := ε / 50
  let ρ_scale : ℝ := ε / 50
  let εA_int : ℝ := εA + ρ_scale  -- internal exponent after scale transfer = ε/25
  let ε_tube : ℝ := ε / 4
  let lam : ℝ := ε / 2
  let reserved_budget : ℝ := ε / 20

  have hεA_pos : 0 < εA := by positivity
  have hεA_lt_one : εA < 1 := by
    dsimp only [εA]
    have h1 : ε / 50 < 1 := by
      have h2 : ε < 1 := hε_lt_one
      have h3 : 0 < ε := hε_pos
      calc ε / 50 < 1 / 50 := by gcongr
        _ < 1 := by norm_num
    exact h1
  have hρ_scale_pos : 0 < ρ_scale := by positivity
  have hεA_int_pos : 0 < εA_int := by positivity
  have hεA_int_lt_tube : εA_int < ε_tube := by
    dsimp only [εA_int, εA, ρ_scale, ε_tube]
    have h1 : 0 < ε := hε_pos
    linarith
  have hε_tube_pos : 0 < ε_tube := by positivity
  have hε_tube_lt_lam : ε_tube < lam := by
    dsimp only [ε_tube, lam]
    have h1 : 0 < ε := hε_pos
    linarith
  have hlam_pos : 0 < lam := by positivity
  have hbudget_pos : 0 < reserved_budget := by positivity

  -- RKP data (uniform wrapper: instantiate at local u in the Appendix branch)
  rcases hRKP_data with ⟨δ₀_RKP, hδ₀_RKP_pos, hδ₀_RKP_le_one, hRKP_uniform⟩

  -- Obtain δ₀_nice from source_to_nice_configuration early so it can be
  -- incorporated into the δA threshold.
  rcases source_to_nice_configuration reserved_budget hbudget_pos
      lam hlam_pos ε_tube hε_tube_pos hε_tube_lt_lam with
    ⟨δ₀_nice, hδ₀_nice_pos, h_nice_main⟩

  -- Threshold for UniformAppendixAAlternative.
  -- With δ_n ≤ 4δ: Δ = √δ_n ≤ 2√δ ≤ 2√δA.
  -- Choose δA = δ₀²/16 so Δ ≤ δ₀/2 < δ₀.
  -- Worst-case exponent for M lower bound (when ρ_M is maximal)
  let e_max : ℝ := -s + lam + reserved_budget
  have he_max_neg : e_max < 0 := by
    dsimp only [e_max, lam, reserved_budget]
    linarith [h12ε, hs_pos]
  -- Threshold ensuring δ_n^e_max ≥ 2: need 4*δA ≤ 2^(1/e_max)
  let δA_M : ℝ := (1 / 4 : ℝ) * Real.rpow 2 (1 / e_max)
  have hδA_M_pos : 0 < δA_M := by
    dsimp only [δA_M]
    have h1 : 0 < Real.rpow 2 (1 / e_max) := Real.rpow_pos_of_pos (by norm_num) _
    exact mul_pos (by norm_num) h1
  -- Additional smallness terms for Δ bounds (M-independent)
  let δA_RKP : ℝ := δ₀_RKP^2 / 4
  let δA_small : ℝ := (1 / 100 : ℝ)^(8 / ε) / 4
  let δA_tube : ℝ := (4000 * (44 : ℝ)^s)^(-2 / ε) / 4
  let δA_log1 : ℝ := (ε / (8 * (3 : ℝ)^ε))^(1 / ε) / 4
  let δA_log2 : ℝ := (1 / 2 : ℝ)^(2 / (3 * ε)) / 4
  -- Scale absorption: δ_n^(-ρ_scale) ≥ 10000 * 81 * K_pack^2 * 4^εA
  -- K_pack^2 needed for AffineLine tube S-set doubling (two steps δ→2δ→4δ)
  let δA_scale : ℝ := (10000 * 81 * (MainAppendix.affineLine_packing_constant : ℝ)^2 * (4 : ℝ)^εA)^(-1 / ρ_scale) / 4
  let δA_nice : ℝ := δ₀_nice / 4
  -- B1 assembly smallness: ensure Δ^{ε/5 - 2εA - 2ρ_mass} ≤ (1/810000) * 4^{-εA}
  let e_B1 : ℝ := ε / 5 - 2 * εA - 2 * reserved_budget
  have he_B1_pos : 0 < e_B1 := by
    dsimp only [e_B1, εA, reserved_budget]
    have h1 : 0 < ε := hε_pos
    linarith
  let C_B1 : ℝ := (1 / 810000 : ℝ) * Real.rpow 4 (-εA)
  have hC_B1_pos : 0 < C_B1 := by
    dsimp only [C_B1]
    have h1 : 0 < Real.rpow 4 (-εA) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  let δA_B1 : ℝ := (1 / 4 : ℝ) * C_B1^(2 / e_B1)
  have hδA_B1_pos : 0 < δA_B1 := by positivity
  let δA : ℝ := min (δ₀^2 / 16) (min δA_M (min δA_RKP
    (min δA_small (min δA_tube (min δA_log1 (min δA_log2 (min δA_scale (min δA_nice (min δA_B1 (1 / 37))))))))))
  have hδA_scale_pos : 0 < δA_scale := by
    dsimp only [δA_scale]
    have hK_pos : 0 < (MainAppendix.affineLine_packing_constant : ℝ) :=
      Nat.cast_pos.mpr MainAppendix.affineLine_packing_constant_pos
    set B := (10000 * 81 * (MainAppendix.affineLine_packing_constant : ℝ)^2 * (4 : ℝ)^εA) with hB_def
    have hB_pos : 0 < B := by
      simp only [hB_def]
      have h1 : 0 < (MainAppendix.affineLine_packing_constant : ℝ)^2 := by positivity
      have h2 : 0 < (4 : ℝ)^εA := by positivity
      positivity
    have h_rpow_pos : 0 < B ^ (-1 / ρ_scale) := Real.rpow_pos_of_pos hB_pos _
    exact mul_pos h_rpow_pos (by norm_num)
  have hmin_pos : ∀ {a b : ℝ}, 0 < a → 0 < b → 0 < min a b := by
    intro a b ha hb
    by_cases h : a ≤ b
    · rw [min_eq_left h]; exact ha
    · rw [min_eq_right (by linarith)]; exact hb
  have hδA_pos : 0 < δA := by
    dsimp only [δA]
    have h1 : 0 < δ₀^2 / 16 := by positivity
    have h3 : 0 < δA_RKP := by positivity
    have h4 : 0 < δA_small := by positivity
    have h5 : 0 < δA_tube := by positivity
    have h6 : 0 < δA_log1 := by positivity
    have h7 : 0 < δA_log2 := by positivity
    have h9 : 0 < δA_nice := by positivity
    have h10 : 0 < (1 / 37 : ℝ) := by norm_num
    have h_posB1 : 0 < min δA_B1 (1 / 37 : ℝ) := hmin_pos hδA_B1_pos h10
    have h_pos9 : 0 < min δA_nice (min δA_B1 (1 / 37 : ℝ)) := hmin_pos h9 h_posB1
    have h_pos8 : 0 < min δA_scale (min δA_nice (min δA_B1 (1 / 37 : ℝ))) := hmin_pos hδA_scale_pos h_pos9
    have h_pos7 : 0 < min δA_log2 (min δA_scale (min δA_nice (min δA_B1 (1 / 37 : ℝ)))) := hmin_pos h7 h_pos8
    have h_pos6 : 0 < min δA_log1 (min δA_log2 (min δA_scale (min δA_nice (min δA_B1 (1 / 37 : ℝ))))) := hmin_pos h6 h_pos7
    have h_pos5 : 0 < min δA_tube (min δA_log1 (min δA_log2 (min δA_scale (min δA_nice (min δA_B1 (1 / 37 : ℝ)))))) := hmin_pos h5 h_pos6
    have h_pos4 : 0 < min δA_small (min δA_tube (min δA_log1 (min δA_log2 (min δA_scale (min δA_nice (min δA_B1 (1 / 37 : ℝ))))))) := hmin_pos h4 h_pos5
    have h_pos3 : 0 < min δA_RKP (min δA_small (min δA_tube (min δA_log1 (min δA_log2 (min δA_scale (min δA_nice (min δA_B1 (1 / 37 : ℝ)))))))) := hmin_pos h3 h_pos4
    have h_pos2 : 0 < min δA_M (min δA_RKP (min δA_small (min δA_tube (min δA_log1 (min δA_log2 (min δA_scale (min δA_nice (min δA_B1 (1 / 37 : ℝ))))))))) := hmin_pos hδA_M_pos h_pos3
    exact hmin_pos h1 h_pos2
  have hδA_le_δ₀_sq : δA ≤ δ₀^2 / 16 := by
    exact min_le_left _ _
  have hδA_le_RKP_sq : δA ≤ δA_RKP := by
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδA_le_small : δA ≤ δA_small := by
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδA_le_tube : δA ≤ δA_tube := by
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδA_le_log1 : δA ≤ δA_log1 := by
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hδA_le_log2 : δA ≤ δA_log2 := by
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
  have hδA_le_scale : δA ≤ δA_scale := by
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))))
  have hδA_le_nice : δA ≤ δA_nice := by
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))))
  have hδA_le_third_const : δA ≤ (1 / 37 : ℝ) := by
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))))))
  have hδA_le_one : δA ≤ 1 := by
    have h1 : δA ≤ (1 / 37 : ℝ) := hδA_le_third_const
    linarith

  refine' ⟨εA, hεA_lt_one, _⟩

  -- ========================================================================
  -- Prove UniformAppendixAAlternative body
  -- ========================================================================
  refine' ⟨hεA_pos, δA, hδA_pos, hδA_le_one, _⟩

  intro u hu_t hu_two δ hδ_pos hδ_le_δA P hP_subset hP_sset hNcover_sqrt
    tubeFamily hT_sset hIncidence

  -- ========================================================================
  -- Endpoint adapter: select running exponent u_run ≤ u with u_run < 2.
  -- Split ledger:
  --   Point S-set: exponent u_run, constant δ^{-εA} (exponent-only weakening)
  --   Point sqrt-cover: exponent u_run/2 + εA_run (identity transfer, MANDATORY)
  --   Tube/failure ledger: original εA unchanged
  -- ========================================================================
  let ρ_endpoint := (EndpointAdapter.endpointAdapter u εA t).1
  let u_run := (EndpointAdapter.endpointAdapter u εA t).2.1
  let εA_run := (EndpointAdapter.endpointAdapter u εA t).2.2
  have h_endpoint := EndpointAdapter.endpointAdapter_spec hεA_pos ht_pos ht_lt_two hu_t hu_two
  have h_t_le_run : t ≤ u_run := h_endpoint.1
  have h_run_lt_two : u_run < 2 := h_endpoint.2.1
  have h_run_le_u : u_run ≤ u := h_endpoint.2.2.1
  have h_cover_identity : u_run / 2 + εA_run = u / 2 + εA := h_endpoint.2.2.2
  have hδ_lt_one : δ < 1 := by
    have h1 : δ ≤ δA := hδ_le_δA
    have h2 : δA ≤ (1 / 37 : ℝ) := hδA_le_third_const
    linarith
  have hC_one : 1 ≤ Real.rpow δ (-εA) := by
    have hδ_lt_one' : δ < 1 := by linarith [hδ_le_δA, hδA_le_third_const]
    have h_pos : 0 < Real.rpow δ εA := Real.rpow_pos_of_pos hδ_pos εA
    have h_lt_one : Real.rpow δ εA < 1 := Real.rpow_lt_one hδ_pos.le hδ_lt_one' hεA_pos
    have h_eq : Real.rpow δ (-εA) = 1 / Real.rpow δ εA := by
      have h_neg : Real.rpow δ (-εA) = (Real.rpow δ εA)⁻¹ := Real.rpow_neg hδ_pos.le εA
      rw [h_neg] <;> ring
    rw [h_eq]
    exact (one_lt_one_div h_pos h_lt_one).le
  have h_run_nonneg : 0 ≤ u_run := by linarith
  -- Point S-set: weaken exponent only, keep stronger constant δ^{-εA}
  have hP_sset_run : IsDeltaSSet δ u_run (Real.rpow δ (-εA)) P :=
    EndpointAdapter.weakenSSetEndpoint hP_sset h_run_nonneg h_run_le_u hC_one
  -- Point sqrt-cover: identity transfer gives exponent u_run/2 + εA_run
  have hNcover_sqrt_run : Ncover (Real.sqrt δ) P ≤
      ENNReal.ofReal (Real.rpow δ (-(u_run / 2 + εA_run))) :=
    EndpointAdapter.transferSqrtCoverEndpoint hδ_pos h_cover_identity hNcover_sqrt
  -- Shadow u so downstream code uses u_run
  let u : ℝ := u_run
  have hu_t : t ≤ u := h_t_le_run
  have hu_two : u ≤ 2 := by linarith
  have hP_sset : IsDeltaSSet δ u (Real.rpow δ (-εA)) P := hP_sset_run
  -- sqrt-cover uses εA_run (compensation for exponent reduction)
  have hNcover_sqrt : Ncover (Real.sqrt δ) P ≤
      ENNReal.ofReal (Real.rpow δ (-(u / 2 + εA_run))) := hNcover_sqrt_run

  let allTubes : Set AffineLine := ⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp
  let NcoverAL : ℝ → Set AffineLine → ENNReal := fun δ S => Metric.externalCoveringNumber δ.toNNReal S

  -- ========================================================================
  -- Proof by contradiction: assume both bounds fail
  -- ========================================================================
  by_cases h_fine : ENNReal.ofReal (Real.rpow δ (-(2 * s + εA))) ≤
      NcoverAL δ allTubes
  · exact Or.inl h_fine
  · by_cases h_coarse : ENNReal.ofReal (Real.rpow δ (-(s + εA))) ≤
        NcoverAL (Real.sqrt δ) allTubes
    · exact Or.inr h_coarse
    · -- Both bounds fail
      exfalso

      -- ====================================================================
      -- Step 3: Select exact even dyadic scale ABOVE public δ
      -- ====================================================================
      have hδ_le_one : δ ≤ 1 := by linarith
      rcases exists_even_dyadic_scale_above δ hδ_pos hδ_le_one with
        ⟨n, hn_even, hδ_le_δ_n_raw, hδ_n_le_4δ_raw⟩
      let m : ℕ := n / 2
      have hn_eq : n = 2 * m := by omega
      have hnm : m ≤ n := by omega
      let Δ : ℝ := dyadicDelta m
      let δ_n : ℝ := dyadicDelta n
      have h_dyadic_eq : ∀ (k : ℕ), dyadicDelta k = DiscretisedFurstenbergEstimate.dyadicDelta k := by
        intro k
        have h1 : Real.rpow 2 (-(k : ℝ)) = (Real.rpow 2 (k : ℝ))⁻¹ := Real.rpow_neg (by norm_num) (k : ℝ)
        have h2 : Real.rpow 2 (k : ℝ) = (2 : ℝ)^k := by
          have h3 : (2 : ℝ) ^ (k : ℝ) = (2 : ℝ)^k := by simp
          exact h3
        have h3 : DiscretisedFurstenbergEstimate.dyadicDelta k = 1 / (2 : ℝ)^k := by
          simp [DiscretisedFurstenbergEstimate.dyadicDelta] <;> ring
        have h4 : dyadicDelta k = Real.rpow 2 (-(k : ℝ)) := by
          simp [dyadicDelta]
        rw [h4, h1, h2, h3] <;> ring
      have hδ_le_δ_n' : δ ≤ δ_n := by
        have h_eq : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n := h_dyadic_eq n
        rw [h_eq]
        exact hδ_le_δ_n_raw
      have hδ_n_le_4δ' : δ_n ≤ 4 * δ := by
        have h_eq : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n := h_dyadic_eq n
        rw [h_eq]
        exact hδ_n_le_4δ_raw
      have hΔ_pos : 0 < Δ := InductionOnScales.dyadicDelta_pos m
      have hδ_n_pos : 0 < δ_n := InductionOnScales.dyadicDelta_pos n
      have hΔ_le_one : Δ ≤ 1 := by
        dsimp only [Δ, dyadicDelta]
        have h2 : Real.rpow 2 (-↑m) ≤ 1 := by
          have h3 : Real.rpow 2 (-↑m) = 1 / Real.rpow 2 (↑m) := by
            simp [Real.rpow_neg]
            <;> ring
          rw [h3]
          have h4 : 1 ≤ Real.rpow 2 (↑m) := by
            have h5 : Real.rpow 2 (0 : ℝ) ≤ Real.rpow 2 (↑m) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast Nat.zero_le m)
            simpa using h5
          have h6 : 0 < Real.rpow 2 (↑m) := by positivity
          exact (div_le_one h6).mpr h4
        exact h2
      have hδ_n_eq2 : δ_n = Δ ^ 2 := by
        dsimp only [δ_n, Δ, dyadicDelta]
        have h1 : (n : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hn_eq
        rw [h1]
        have h2 : Real.rpow 2 (-(2 * (m : ℝ))) = (Real.rpow 2 (-(m : ℝ))) ^ 2 := by
          calc Real.rpow 2 (-(2 * (m : ℝ)))
            = Real.rpow 2 ((-(m : ℝ)) * 2) := by rw [show (-(2 * (m : ℝ))) = (-(m : ℝ)) * 2 by ring]
          _ = (Real.rpow 2 (-(m : ℝ))) ^ (2 : ℝ) := Real.rpow_mul (by norm_num) (-(m : ℝ)) (2 : ℝ)
          _ = (Real.rpow 2 (-(m : ℝ))) ^ 2 := by simp [Real.rpow_two]
        exact h2
      have hδ_le_D : δ_n ≤ Δ := by
        rw [hδ_n_eq2]
        have h : Δ ^ 2 ≤ Δ := by
          nlinarith [hΔ_pos, hΔ_le_one]
        exact h
      have hΔ_le_2sqrtδA : Δ ≤ 2 * Real.sqrt δA := by
        have h3 : δ_n ≤ 4 * δA := by linarith
        have h4 : Δ^2 ≤ 4 * δA := by
          have h5 : Δ^2 = δ_n := by rw [hδ_n_eq2] <;> ring
          rw [h5]; exact h3
        have h_posΔ : 0 ≤ Δ := by positivity
        have h6 : Δ ≤ Real.sqrt (4 * δA) := by
          rw [← Real.sqrt_sq h_posΔ]
          exact Real.sqrt_le_sqrt h4
        have h8 : Real.sqrt (4 * δA) = 2 * Real.sqrt δA := by
          have h9 : Real.sqrt (4 * δA) = Real.sqrt 4 * Real.sqrt δA := by
            rw [Real.sqrt_mul (by positivity)]
          rw [h9]
          have h10 : Real.sqrt 4 = 2 := by
            rw [Real.sqrt_eq_cases] <;> norm_num
          rw [h10] <;> ring
        rw [h8] at h6
        exact h6
      have h2sqrt_lt_half : 2 * Real.sqrt δA < 1 / 2 := by
        have h10 : δA ≤ (1 / 37 : ℝ) := hδA_le_third_const
        have h11 : Real.sqrt δA ≤ Real.sqrt (1 / 37) := Real.sqrt_le_sqrt h10
        have h12 : (1 / 37 : ℝ) < (1 / 4 : ℝ)^2 := by norm_num
        have h13 : Real.sqrt (1 / 37) < 1 / 4 := (Real.sqrt_lt' (by norm_num)).mpr h12
        have h14 : Real.sqrt δA < 1 / 4 := by
          calc Real.sqrt δA ≤ Real.sqrt (1 / 37) := h11
               _ < 1 / 4 := h13
        have h15 : 2 * Real.sqrt δA < 2 * (1 / 4 : ℝ) :=
          mul_lt_mul_of_pos_left h14 (by norm_num)
        have h16 : 2 * (1 / 4 : ℝ) = 1 / 2 := by ring
        rw [h16] at h15
        exact h15
      have hΔ_lt_half : Δ < 1 / 2 := by
        have h1 : Δ ≤ 2 * Real.sqrt δA := hΔ_le_2sqrtδA
        have h2 : 2 * Real.sqrt δA < 1 / 2 := h2sqrt_lt_half
        exact lt_of_le_of_lt h1 h2
      have hΔ_lt_one : Δ < 1 := by
        have h : Δ < 1 / 2 := hΔ_lt_half
        have h' : (1 / 2 : ℝ) < 1 := by norm_num
        exact lt_trans h h'
      have h2sqrt_lt_third : 2 * Real.sqrt δA < 1 / 3 := by
        have h10 : δA ≤ (1 / 37 : ℝ) := hδA_le_third_const
        have h11 : Real.sqrt δA ≤ Real.sqrt (1 / 37) := Real.sqrt_le_sqrt h10
        have h12 : (1 / 37 : ℝ) < (1 / 6 : ℝ)^2 := by norm_num
        have h13 : Real.sqrt (1 / 37) < 1 / 6 := (Real.sqrt_lt' (by norm_num)).mpr h12
        have h14 : Real.sqrt δA < 1 / 6 := by
          calc Real.sqrt δA ≤ Real.sqrt (1 / 37) := h11
               _ < 1 / 6 := h13
        have h15 : 2 * Real.sqrt δA < 2 * (1 / 6 : ℝ) :=
          mul_lt_mul_of_pos_left h14 (by norm_num)
        have h16 : 2 * (1 / 6 : ℝ) = 1 / 3 := by ring
        rw [h16] at h15
        exact h15
      have hΔ_lt_third : Δ < 1 / 3 := by
        calc Δ ≤ 2 * Real.sqrt δA := hΔ_le_2sqrtδA
             _ < 1 / 3 := h2sqrt_lt_third
      have h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100 := by
        have h9 : Δ ≤ (1 / 100 : ℝ)^(4 / ε) := by
          have h10 : 2 * Real.sqrt δA ≤ (1 / 100 : ℝ)^(4 / ε) := by
            have h11 : δA ≤ δA_small := hδA_le_small
            have h12 : (2 * Real.sqrt δA)^2 ≤ ((1 / 100 : ℝ)^(4 / ε))^2 := by
              have h13 : (2 * Real.sqrt δA)^2 = 4 * δA := by
                calc (2 * Real.sqrt δA)^2 = 4 * (Real.sqrt δA)^2 := by ring
                  _ = 4 * δA := by rw [Real.sq_sqrt (by positivity)] <;> ring
              have h14 : 4 * δA ≤ 4 * δA_small := by gcongr
              have h15 : 4 * δA_small = ((1 / 100 : ℝ)^(4 / ε))^2 := by
                dsimp only [δA_small]
                have h_base_pos : 0 < (1 / 100 : ℝ) := by norm_num
                have h16 : ((1 / 100 : ℝ)^(4 / ε))^2 = (1 / 100 : ℝ)^(8 / ε) := by
                  have h17 : ((1 / 100 : ℝ)^(4 / ε))^2 = ((1 / 100 : ℝ)^(4 / ε)) * ((1 / 100 : ℝ)^(4 / ε)) := by ring
                  rw [h17]
                  have h18 : ((1 / 100 : ℝ)^(4 / ε)) * ((1 / 100 : ℝ)^(4 / ε)) = (1 / 100 : ℝ)^(4 / ε + 4 / ε) := by
                    rw [← Real.rpow_add h_base_pos] <;> ring
                  rw [h18] <;> ring_nf
                rw [h16] <;> ring
              rw [h13, ←h15]; exact h14
            have h15 : 0 ≤ 2 * Real.sqrt δA := by positivity
            have h16 : 0 ≤ (1 / 100 : ℝ)^(4 / ε) := by positivity
            have h17 : (2 * Real.sqrt δA)^2 ≤ ((1 / 100 : ℝ)^(4 / ε))^2 := h12
            have h18 : 2 * Real.sqrt δA ≤ (1 / 100 : ℝ)^(4 / ε) := by
              by_contra h19
              set a := 2 * Real.sqrt δA with ha_def
              set b := (1 / 100 : ℝ)^(4 / ε) with hb_def
              have h20 : b < a := by linarith
              have hb_pos : 0 < b := by positivity
              have ha_nonneg : 0 ≤ a := by positivity
              have h21 : b^2 < a^2 := by
                calc b^2 = b * b := by ring
                  _ < a * b := by gcongr
                  _ ≤ a * a := by gcongr <;> linarith
                  _ = a^2 := by ring
              have h22 : a^2 ≤ b^2 := h12
              linarith
            exact h18
          calc Δ ≤ 2 * Real.sqrt δA := hΔ_le_2sqrtδA
               _ ≤ (1 / 100 : ℝ)^(4 / ε) := h10
        have h10 : Real.rpow Δ (ε / 4) ≤ Real.rpow ((1 / 100 : ℝ)^(4 / ε)) (ε / 4) :=
          Real.rpow_le_rpow (by positivity) h9 (by linarith [hε_pos])
        have h11 : Real.rpow ((1 / 100 : ℝ)^(4 / ε)) (ε / 4) = (1 / 100 : ℝ) := by
          let x : ℝ := 1 / 100
          let y : ℝ := 4 / ε
          let z : ℝ := ε / 4
          have hx : 0 ≤ x := by norm_num
          have h_mul : y * z = 1 := by
            dsimp only [y, z]
            field_simp [hε_pos.ne'] <;> ring
          have h_eq : Real.rpow (Real.rpow x y) z = Real.rpow x (y * z) :=
            (Real.rpow_mul hx y z).symm
          have h_main : Real.rpow (Real.rpow x y) z = x := by
            rw [h_eq, h_mul]
            exact Real.rpow_one x
          exact h_main
        rw [h11] at h10; exact h10
      have hΔ_lt_δ₀ : Δ < δ₀ := by
        have h9 : 2 * Real.sqrt δA ≤ δ₀ / 2 := by
          have h10 : δA ≤ δ₀^2 / 16 := hδA_le_δ₀_sq
          have h11 : Real.sqrt δA ≤ Real.sqrt (δ₀^2 / 16) := Real.sqrt_le_sqrt h10
          have h12 : Real.sqrt (δ₀^2 / 16) = δ₀ / 4 := by
            have h13 : 0 ≤ δ₀ := hδ₀_pos.le
            have h14 : δ₀^2 / 16 = (δ₀ / 4)^2 := by ring
            rw [h14, Real.sqrt_sq (by positivity)] <;> ring
          have h15 : 2 * Real.sqrt δA ≤ 2 * (δ₀ / 4) := by
            calc 2 * Real.sqrt δA ≤ 2 * Real.sqrt (δ₀^2 / 16) := by gcongr
                 _ = 2 * (δ₀ / 4) := by rw [h12]
          have h16 : 2 * (δ₀ / 4) = δ₀ / 2 := by ring
          rw [h16] at h15
          exact h15
        have h10 : Δ ≤ δ₀ / 2 := by
          calc Δ ≤ 2 * Real.sqrt δA := hΔ_le_2sqrtδA
               _ ≤ δ₀ / 2 := h9
        have h11 : δ₀ / 2 < δ₀ := by linarith [hδ₀_pos]
        linarith
      have hΔ_le_δ₀ : Δ ≤ δ₀ := le_of_lt hΔ_lt_δ₀
      have hΔ_le_RKP : Δ ≤ δ₀_RKP := by
        have h9 : 2 * Real.sqrt δA ≤ δ₀_RKP := by
          have h10 : δA ≤ δA_RKP := hδA_le_RKP_sq
          have h11 : Real.sqrt δA ≤ Real.sqrt δA_RKP := Real.sqrt_le_sqrt h10
          have h12 : 2 * Real.sqrt δA ≤ 2 * Real.sqrt δA_RKP := by gcongr
          have h13 : 4 * δA_RKP = δ₀_RKP^2 := by
            dsimp only [δA_RKP] <;> ring
          have h14 : 0 ≤ δ₀_RKP := hδ₀_RKP_pos.le
          have h15 : Real.sqrt δA_RKP = δ₀_RKP / 2 := by
            have h16 : Real.sqrt (4 * δA_RKP) = δ₀_RKP := by
              rw [h13, Real.sqrt_sq h14]
            have h17 : Real.sqrt (4 * δA_RKP) = 2 * Real.sqrt δA_RKP := by
              rw [Real.sqrt_mul (by positivity)]
              have h18 : Real.sqrt 4 = 2 := by
                rw [Real.sqrt_eq_cases] <;> norm_num
              rw [h18] <;> ring
            have h19 : 2 * Real.sqrt δA_RKP = δ₀_RKP := by
              rw [←h17, h16]
            calc Real.sqrt δA_RKP
              = (2 * Real.sqrt δA_RKP) / 2 := by ring
            _ = δ₀_RKP / 2 := by rw [h19]
          rw [h15] at h12
          have h18 : 2 * Real.sqrt δA ≤ δ₀_RKP := by
            calc 2 * Real.sqrt δA ≤ 2 * (δ₀_RKP / 2) := h12
                 _ = δ₀_RKP := by ring
          exact h18
        calc Δ ≤ 2 * Real.sqrt δA := hΔ_le_2sqrtδA
             _ ≤ δ₀_RKP := h9
      have hm_pos : 1 ≤ m := by
        have hδ_n_lt_quarter : δ_n < 1 / 4 := by
          calc δ_n ≤ 4 * δ := hδ_n_le_4δ'
               _ ≤ 4 * δA := by linarith [hδ_le_δA]
               _ ≤ 4 * (1 / 37) := by linarith [hδA_le_third_const]
               _ < 1 / 4 := by norm_num
        have h_eq : δ_n = Real.rpow 2 (-(n : ℝ)) := by
          simp [δ_n, dyadicDelta]
        rw [h_eq] at hδ_n_lt_quarter
        have h2 : (n : ℝ) > 2 := by
          by_contra h
          have h3 : (n : ℝ) ≤ 2 := by linarith
          have h4 : Real.rpow 2 (-2 : ℝ) ≤ Real.rpow 2 (-(n : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          have h5 : Real.rpow 2 (-2 : ℝ) = 1 / 4 := by norm_num
          rw [h5] at h4
          linarith
        have h6 : n > 2 := by exact_mod_cast h2
        omega

      -- ====================================================================
      -- Step 4: Scale transfer (δ → δ_n) — all data to exact dyadic scale
      -- ====================================================================

      -- 4a. Transfer S-set P: two-step coarsen δ → 2δ → δ_n
      have hP_sset_scale : IsDeltaSSet δ_n u (81 * Real.rpow δ (-εA)) P := by
        by_cases h_case : δ_n ≤ 2 * δ
        · -- One step: δ → δ_n ≤ 2δ
          have h1 := hP_sset.coarsen_scale hδ_pos hδ_n_pos hδ_le_δ_n' h_case
          have h2 : (9 : ℝ) * Real.rpow δ (-εA) ≤ 81 * Real.rpow δ (-εA) := by
            have h3 : 0 < Real.rpow δ (-εA) := by positivity
            linarith
          exact IsDeltaSSet.weaken_C h1 h2
        · -- Two steps: δ → 2δ → δ_n
          have h_2δ_le : 2 * δ ≤ δ_n := by linarith
          have h1 : IsDeltaSSet (2 * δ) u (9 * Real.rpow δ (-εA)) P :=
            hP_sset.coarsen_scale hδ_pos (by positivity) (by linarith) (by linarith)
          have h2 : IsDeltaSSet δ_n u (9 * (9 * Real.rpow δ (-εA))) P :=
            h1.coarsen_scale (by positivity) hδ_n_pos h_2δ_le (by linarith)
          have h3 : (9 : ℝ) * (9 * Real.rpow δ (-εA)) = 81 * Real.rpow δ (-εA) := by ring
          exact IsDeltaSSet.weaken_C h2 (le_of_eq h3)

      -- 4b. Transfer sqrt covering bound (not needed: DeltasSet extraction provides Ncover lower)
      -- Shared rpow absorption: δ^{-εA} ≤ 4^{εA} · δ_n^{-εA}
      have h_absorb3_shared : Real.rpow δ (-εA) ≤ (4 : ℝ)^εA * Real.rpow δ_n (-εA) := by
        have h4 : δ_n / 4 ≤ δ := by linarith
        have h5 : 0 < δ_n / 4 := by positivity
        have h6 : Real.rpow (δ_n / 4) εA ≤ Real.rpow δ εA :=
          Real.rpow_le_rpow h5.le h4 hεA_pos.le
        have h7 : Real.rpow δ (-εA) ≤ Real.rpow (δ_n / 4) (-εA) := by
          have h81 : Real.rpow δ (-εA) = (Real.rpow δ εA)⁻¹ := Real.rpow_neg hδ_pos.le εA
          have h8 : Real.rpow δ (-εA) = 1 / Real.rpow δ εA := by rw [h81] <;> ring
          have h91 : Real.rpow (δ_n / 4) (-εA) = (Real.rpow (δ_n / 4) εA)⁻¹ := Real.rpow_neg h5.le εA
          have h9 : Real.rpow (δ_n / 4) (-εA) = 1 / Real.rpow (δ_n / 4) εA := by rw [h91] <;> ring
          rw [h8, h9]
          have h_pos_small : 0 < Real.rpow (δ_n / 4) εA := Real.rpow_pos_of_pos h5 εA
          exact one_div_le_one_div_of_le h_pos_small h6
        have h10 : Real.rpow (δ_n / 4) (-εA) = (4 : ℝ)^εA * Real.rpow δ_n (-εA) := by
          have h101 : (δ_n / 4 : ℝ) = δ_n * (4 : ℝ)⁻¹ := by ring
          rw [h101]
          have h102 : Real.rpow (δ_n * (4 : ℝ)⁻¹) (-εA) =
              Real.rpow δ_n (-εA) * Real.rpow ((4 : ℝ)⁻¹) (-εA) :=
            Real.mul_rpow hδ_n_pos.le (by norm_num)
          rw [h102]
          have h103 : Real.rpow ((4 : ℝ)⁻¹) (-εA) = (4 : ℝ)^εA := by
            have h104 : (4 : ℝ)⁻¹ = Real.rpow 4 (-1 : ℝ) := by norm_num
            rw [h104]
            have h105 : Real.rpow (Real.rpow 4 (-1 : ℝ)) (-εA) =
                Real.rpow 4 ((-1 : ℝ) * (-εA)) :=
              (Real.rpow_mul (by norm_num) (-1 : ℝ) (-εA)).symm
            rw [h105]
            have h106 : (-1 : ℝ) * (-εA) = εA := by ring
            rw [h106] <;> rfl
          rw [h103] <;> ring
        rw [h10] at h7; exact h7
      -- 4c. Transfer tube S-sets: AffineLine doubling (K_pack^2 for δ→4δ), absorb into εA_int
      have hT_sset_n : ∀ (p : EuclideanPlane) (hp : p ∈ P),
          IsDeltaSSet δ_n s (Real.rpow δ_n (-εA_int)) (tubeFamily p hp) := by
        intro p hp
        let K_pack := MainAppendix.affineLine_packing_constant
        let T := tubeFamily p hp
        have hT_orig : IsDeltaSSet δ s (Real.rpow δ (-εA)) T := hT_sset p hp
        -- Coarsen S-set from δ to δ_n using AffineLine doubling: K_pack^2 for δ→4δ≥δ_n
        have h_doubling : NcoverAL δ T ≤ (K_pack : ENNReal)^2 * NcoverAL δ_n T := by
          have h3 := Snapping.affineLine_doubling_iter δ hδ_pos 2 (S := T)
          have h3' : NcoverAL δ T ≤ (K_pack : ENNReal)^2 * NcoverAL (4 * δ) T := by
            simpa [pow_two] using h3
          have h5 : NcoverAL (4 * δ) T ≤ NcoverAL δ_n T := by
            have h6 : δ_n.toNNReal ≤ (4 * δ).toNNReal := by exact Real.toNNReal_mono hδ_n_le_4δ'
            have h7 : Metric.externalCoveringNumber (4 * δ).toNNReal T ≤ Metric.externalCoveringNumber δ_n.toNNReal T :=
              Metric.externalCoveringNumber_anti h6
            simpa [NcoverAL] using h7
          exact le_trans h3' (by gcongr)
        have hT_sset_scale : IsDeltaSSet δ_n s ((K_pack : ℝ)^2 * Real.rpow δ (-εA)) T := by
          rcases hT_orig with ⟨hT_nonempty, _, hC_pos, hs_nonneg, h_main⟩
          have hK_pos : 0 < (K_pack : ℝ)^2 := by
            have hK : 0 < (K_pack : ℝ) := Nat.cast_pos.mpr MainAppendix.affineLine_packing_constant_pos
            positivity
          have hC_pos' : 0 < (K_pack : ℝ)^2 * Real.rpow δ (-εA) := mul_pos hK_pos hC_pos
          refine' ⟨hT_nonempty, hδ_n_pos, hC_pos', hs_nonneg, _⟩
          intro x r hr
          have hδ_le_r : δ ≤ r := by linarith
          have h_anti1 : NcoverAL δ_n (T ∩ Metric.closedBall x r) ≤ NcoverAL δ (T ∩ Metric.closedBall x r) := by
            have h : δ.toNNReal ≤ δ_n.toNNReal := by exact Real.toNNReal_mono hδ_le_δ_n'
            have h' : Metric.externalCoveringNumber δ_n.toNNReal (T ∩ Metric.closedBall x r) ≤
                Metric.externalCoveringNumber δ.toNNReal (T ∩ Metric.closedBall x r) :=
              Metric.externalCoveringNumber_anti h
            simpa [NcoverAL] using h'
          have h2 := h_main x r hδ_le_r
          calc NcoverAL δ_n (T ∩ Metric.closedBall x r)
            ≤ NcoverAL δ (T ∩ Metric.closedBall x r) := h_anti1
          _ ≤ ENNReal.ofReal (Real.rpow δ (-εA)) * (ENNReal.ofReal r) ^ s * NcoverAL δ T := h2
          _ ≤ ENNReal.ofReal (Real.rpow δ (-εA)) * (ENNReal.ofReal r) ^ s *
                ((K_pack : ENNReal)^2 * NcoverAL δ_n T) := by gcongr
          _ = ENNReal.ofReal (((K_pack : ℝ)^2 * Real.rpow δ (-εA))) * (ENNReal.ofReal r) ^ s * NcoverAL δ_n T := by
            have h_pos : 0 ≤ Real.rpow δ (-εA) := by positivity
            simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
        -- Absorb K_pack^2 * δ^(-εA) into δ_n^(-εA_int)
        have h_absorb3 := h_absorb3_shared
        have h_extra : Real.rpow δ_n (-εA) ≤ Real.rpow δ_n (-εA_int) := by
          have hδ_n_le_one : δ_n ≤ 1 := by linarith [hΔ_lt_one]
          exact Real.rpow_le_rpow_of_exponent_ge hδ_n_pos hδ_n_le_one (by linarith [hρ_scale_pos])
        have h11 : (K_pack : ℝ)^2 * Real.rpow δ (-εA) ≤
            (K_pack : ℝ)^2 * (4 : ℝ)^εA * Real.rpow δ_n (-εA) := by
          calc (K_pack : ℝ)^2 * Real.rpow δ (-εA)
            ≤ (K_pack : ℝ)^2 * ((4 : ℝ)^εA * Real.rpow δ_n (-εA)) :=
              mul_le_mul_of_nonneg_left h_absorb3 (by positivity)
          _ = (K_pack : ℝ)^2 * (4 : ℝ)^εA * Real.rpow δ_n (-εA) := by ring
        have h14 : (K_pack : ℝ)^2 * (4 : ℝ)^εA ≤ Real.rpow δ_n (-ρ_scale) := by
          set X : ℝ := 10000 * 81 * (K_pack : ℝ)^2 * (4 : ℝ)^εA with hX_def
          have hK_pos : 0 < (K_pack : ℝ) := Nat.cast_pos.mpr MainAppendix.affineLine_packing_constant_pos
          have h4p : 0 < (4 : ℝ)^εA := Real.rpow_pos_of_pos (by norm_num) εA
          have hX_pos : 0 < X := by
            dsimp only [X]
            exact mul_pos (mul_pos (mul_pos (by norm_num) (by norm_num)) (pow_pos hK_pos 2)) h4p
          set B : ℝ := Real.rpow X (-1 / ρ_scale) with hB_def
          have hB_pos : 0 < B := Real.rpow_pos_of_pos hX_pos _
          have h15 : δ_n ≤ 4 * δA := by linarith
          have h161 : 4 * δA ≤ 4 * δA_scale := by gcongr
          have h162 : 4 * δA_scale = B := by
            dsimp only [δA_scale]
            have h9 : 4 * ((10000 * 81 * (MainAppendix.affineLine_packing_constant : ℝ)^2 * (4 : ℝ)^εA)^(-1 / ρ_scale) / 4) =
                (10000 * 81 * (MainAppendix.affineLine_packing_constant : ℝ)^2 * (4 : ℝ)^εA)^(-1 / ρ_scale) := by ring
            rw [h9]
            have h10 : (10000 * 81 * (MainAppendix.affineLine_packing_constant : ℝ)^2 * (4 : ℝ)^εA)^(-1 / ρ_scale) = Real.rpow X (-1 / ρ_scale) := by
              congr 1
            rw [h10, hB_def]
          have h16 : 4 * δA ≤ B := by
            calc 4 * δA ≤ 4 * δA_scale := h161
                 _ = B := h162
          have h19 : δ_n ≤ B := le_trans h15 h16
          have h20 : Real.rpow δ_n (-ρ_scale) ≥ Real.rpow B (-ρ_scale) := by
            have h1 : Real.rpow δ_n (-ρ_scale) = (Real.rpow δ_n ρ_scale)⁻¹ :=
              Real.rpow_neg hδ_n_pos.le ρ_scale
            have h2 : Real.rpow B (-ρ_scale) = (Real.rpow B ρ_scale)⁻¹ :=
              Real.rpow_neg hB_pos.le ρ_scale
            rw [h1, h2]
            have h3 : Real.rpow δ_n ρ_scale ≤ Real.rpow B ρ_scale :=
              Real.rpow_le_rpow hδ_n_pos.le h19 hρ_scale_pos.le
            have h4 : 0 < Real.rpow δ_n ρ_scale := Real.rpow_pos_of_pos hδ_n_pos _
            have h5 : (Real.rpow B ρ_scale)⁻¹ ≤ (Real.rpow δ_n ρ_scale)⁻¹ := by
              have h6 : 1 / (Real.rpow B ρ_scale) ≤ 1 / (Real.rpow δ_n ρ_scale) :=
                one_div_le_one_div_of_le h4 h3
              simpa [one_div] using h6
            exact h5
          have h21 : Real.rpow B (-ρ_scale) = X := by
            have h_eq1 : (-1 / ρ_scale) * (-ρ_scale) = 1 := by
              field_simp [hρ_scale_pos.ne'] <;> ring
            have h : Real.rpow B (-ρ_scale) = Real.rpow X ((-1 / ρ_scale) * (-ρ_scale)) := by
              rw [hB_def]
              exact (Real.rpow_mul hX_pos.le (-1 / ρ_scale) (-ρ_scale)).symm
            have h' : Real.rpow B (-ρ_scale) = Real.rpow X 1 := by
              rw [h, h_eq1]
            rw [h']
            simp
          rw [h21] at h20
          have h22 : (K_pack : ℝ)^2 * (4 : ℝ)^εA ≤ X := by
            have hX_eq : X = 10000 * 81 * (K_pack : ℝ)^2 * (4 : ℝ)^εA := hX_def
            rw [hX_eq]
            have h_pos : 0 ≤ (K_pack : ℝ)^2 * (4 : ℝ)^εA := by positivity
            have h_one : (1 : ℝ) ≤ 10000 * 81 := by norm_num
            have h_mult : (K_pack : ℝ)^2 * (4 : ℝ)^εA ≤ (10000 * 81) * ((K_pack : ℝ)^2 * (4 : ℝ)^εA) :=
              le_mul_of_one_le_left h_pos h_one
            have h_final : (10000 * 81) * ((K_pack : ℝ)^2 * (4 : ℝ)^εA) = 10000 * 81 * (K_pack : ℝ)^2 * (4 : ℝ)^εA := by ring
            rw [h_final] at h_mult
            exact h_mult
          exact le_trans h22 h20
        have h12 : (K_pack : ℝ)^2 * (4 : ℝ)^εA * Real.rpow δ_n (-εA) ≤ Real.rpow δ_n (-εA_int) := by
          have h13 : Real.rpow δ_n (-εA_int) = Real.rpow δ_n (-ρ_scale) * Real.rpow δ_n (-εA) := by
            have h_sum : -εA_int = (-ρ_scale) + (-εA) := by
              simp only [εA_int] <;> ring
            rw [h_sum]
            exact Real.rpow_add hδ_n_pos (-ρ_scale) (-εA)
          rw [h13]
          exact mul_le_mul_of_nonneg_right h14 (Real.rpow_nonneg hδ_n_pos.le _)
        have h11_simple : (K_pack : ℝ)^2 * Real.rpow δ (-εA) ≤
            (K_pack : ℝ)^2 * (4 : ℝ)^εA * Real.rpow δ_n (-εA) := by
          have h : (K_pack : ℝ)^2 * Real.rpow δ (-εA) ≤ (K_pack : ℝ)^2 * ((4 : ℝ)^εA * Real.rpow δ_n (-εA)) :=
            mul_le_mul_of_nonneg_left h_absorb3 (by positivity)
          ring_nf at h ⊢
          exact h
        have h_const_le : (K_pack : ℝ)^2 * Real.rpow δ (-εA) ≤ Real.rpow δ_n (-εA_int) := by
          calc (K_pack : ℝ)^2 * Real.rpow δ (-εA)
            ≤ (K_pack : ℝ)^2 * (4 : ℝ)^εA * Real.rpow δ_n (-εA) := h11_simple
          _ ≤ Real.rpow δ_n (-εA_int) := h12
        exact IsDeltaSSet.weaken_C hT_sset_scale h_const_le

      -- 4d. Transfer incidence: automatic since δ_n ≥ δ
      have hIncidence_n : ∀ (p : EuclideanPlane) (hp : p ∈ P),
          ∀ (T : AffineLine), T ∈ tubeFamily p hp →
            p ∈ Metric.cthickening δ_n (T.1 : Set EuclideanPlane) := by
        intro p hp T hT
        let S : Set EuclideanPlane := (T.1 : Set EuclideanPlane)
        have h1 : p ∈ Metric.cthickening δ S := hIncidence p hp T hT
        have h2 : δ ≤ δ_n := hδ_le_δ_n'
        have h3 : Metric.cthickening δ S ⊆ Metric.cthickening δ_n S := Metric.cthickening_mono h2 S
        exact h3 h1

      -- 4e. Transfer failure of fine alternative (absorb K_scale into εA_int)
      have h_scale_absorb_general : Real.rpow δ_n (-ρ_scale) ≥ (10000 * 81 * (4 : ℝ)^εA) := by
        let K_pack := MainAppendix.affineLine_packing_constant
        set X : ℝ := 10000 * 81 * (K_pack : ℝ)^2 * (4 : ℝ)^εA with hX_def
        have hK_pos : 0 < (K_pack : ℝ) := Nat.cast_pos.mpr MainAppendix.affineLine_packing_constant_pos
        have h4p : 0 < (4 : ℝ)^εA := Real.rpow_pos_of_pos (by norm_num) εA
        have hX_pos : 0 < X := by
          dsimp only [X]
          exact mul_pos (mul_pos (mul_pos (by norm_num) (by norm_num)) (pow_pos hK_pos 2)) h4p
        set B : ℝ := Real.rpow X (-1 / ρ_scale) with hB_def
        have hB_pos : 0 < B := Real.rpow_pos_of_pos hX_pos _
        have h15 : δ_n ≤ 4 * δA := by linarith
        have h161 : 4 * δA ≤ 4 * δA_scale := by gcongr
        have h162 : 4 * δA_scale = B := by
          dsimp only [δA_scale]
          have h9 : 4 * ((10000 * 81 * (MainAppendix.affineLine_packing_constant : ℝ)^2 * (4 : ℝ)^εA)^(-1 / ρ_scale) / 4) =
              (10000 * 81 * (MainAppendix.affineLine_packing_constant : ℝ)^2 * (4 : ℝ)^εA)^(-1 / ρ_scale) := by ring
          rw [h9]
          have h10 : (10000 * 81 * (MainAppendix.affineLine_packing_constant : ℝ)^2 * (4 : ℝ)^εA)^(-1 / ρ_scale) = Real.rpow X (-1 / ρ_scale) := by
            congr 1
          rw [h10, hB_def]
        have h16 : 4 * δA ≤ B := by
          calc 4 * δA ≤ 4 * δA_scale := h161
               _ = B := h162
        have h19 : δ_n ≤ B := le_trans h15 h16
        have h20 : Real.rpow δ_n ρ_scale ≤ Real.rpow B ρ_scale :=
          Real.rpow_le_rpow hδ_n_pos.le h19 hρ_scale_pos.le
        have h21 : Real.rpow B (-ρ_scale) = X := by
          have h_eq1 : (-1 / ρ_scale) * (-ρ_scale) = 1 := by
            field_simp [hρ_scale_pos.ne'] <;> ring
          have h : Real.rpow B (-ρ_scale) = Real.rpow X ((-1 / ρ_scale) * (-ρ_scale)) := by
            rw [hB_def]
            exact (Real.rpow_mul hX_pos.le (-1 / ρ_scale) (-ρ_scale)).symm
          have h' : Real.rpow B (-ρ_scale) = Real.rpow X 1 := by
            rw [h, h_eq1]
          rw [h']
          simp
        have h22 : Real.rpow δ_n (-ρ_scale) ≥ Real.rpow B (-ρ_scale) := by
          have h1 : Real.rpow δ_n (-ρ_scale) = (Real.rpow δ_n ρ_scale)⁻¹ :=
            Real.rpow_neg hδ_n_pos.le ρ_scale
          have h2 : Real.rpow B (-ρ_scale) = (Real.rpow B ρ_scale)⁻¹ :=
            Real.rpow_neg hB_pos.le ρ_scale
          rw [h1, h2]
          have h3 : Real.rpow δ_n ρ_scale ≤ Real.rpow B ρ_scale := h20
          have h4 : 0 < Real.rpow δ_n ρ_scale := Real.rpow_pos_of_pos hδ_n_pos _
          have h5 : (Real.rpow B ρ_scale)⁻¹ ≤ (Real.rpow δ_n ρ_scale)⁻¹ := by
            have h6 : 1 / (Real.rpow B ρ_scale) ≤ 1 / (Real.rpow δ_n ρ_scale) :=
              one_div_le_one_div_of_le h4 h3
            simpa [one_div] using h6
          exact h5
        rw [h21] at h22
        have h23 : X ≥ (10000 * 81 * (4 : ℝ)^εA) := by
          have hK1 : 1 ≤ (K_pack : ℝ) := by exact_mod_cast MainAppendix.affineLine_packing_constant_pos
          have hK2 : (K_pack : ℝ)^2 ≥ 1 := by
            have h : (1 : ℝ) ≤ (K_pack : ℝ) := hK1
            have h2 : (1 : ℝ)^2 ≤ (K_pack : ℝ)^2 := by gcongr
            have h3 : (1 : ℝ)^2 = 1 := by norm_num
            rw [h3] at h2
            exact h2
          have h4p : 0 ≤ (4 : ℝ)^εA := by positivity
          have h5 : (K_pack : ℝ)^2 * (4 : ℝ)^εA ≥ (4 : ℝ)^εA := by
            have h6 : (K_pack : ℝ)^2 * (4 : ℝ)^εA ≥ 1 * (4 : ℝ)^εA :=
              mul_le_mul_of_nonneg_right hK2 h4p
            have h7 : (1 : ℝ) * (4 : ℝ)^εA = (4 : ℝ)^εA := by ring
            rw [h7] at h6
            exact h6
          have h8 : (10000 * 81 : ℝ) * ((K_pack : ℝ)^2 * (4 : ℝ)^εA) ≥ (10000 * 81 : ℝ) * (4 : ℝ)^εA :=
            mul_le_mul_of_nonneg_left h5 (by norm_num)
          have h9 : X = (10000 * 81 : ℝ) * ((K_pack : ℝ)^2 * (4 : ℝ)^εA) := by
            rw [hX_def] <;> ring
          rw [h9]
          exact h8
        exact le_trans h23 h22
      have h_exp_transfer : ∀ (a : ℝ), 0 ≤ a → a ≤ 3 →
          Real.rpow δ (-a) ≤ Real.rpow δ_n (-(a + ρ_scale)) :=
        scale_transfer_exp_helper δ δ_n ρ_scale εA hδ_pos hδ_n_pos hδ_n_le_4δ' hεA_pos h_scale_absorb_general
      have h_fine_fail_n : ¬(ENNReal.ofReal (Real.rpow δ_n (-(2 * s + εA_int))) ≤
          NcoverAL δ_n allTubes) := by
        have h_a1 : 0 ≤ 2 * s + εA := by positivity
        have h_a2 : 2 * s + εA ≤ 3 := by linarith
        have h_exp1 : Real.rpow δ (-(2 * s + εA)) ≤
            Real.rpow δ_n (-(2 * s + εA + ρ_scale)) := h_exp_transfer (2 * s + εA) h_a1 h_a2
        have h_eq : (2 * s + εA + ρ_scale) = (2 * s + εA_int) := by
          dsimp only [εA_int] <;> ring
        rw [h_eq] at h_exp1
        have h_ncover_mono : NcoverAL δ_n allTubes ≤ NcoverAL δ allTubes := by
          have h : δ.toNNReal ≤ δ_n.toNNReal := by exact Real.toNNReal_mono hδ_le_δ_n'
          have h' : Metric.externalCoveringNumber δ_n.toNNReal allTubes ≤ Metric.externalCoveringNumber δ.toNNReal allTubes :=
            Metric.externalCoveringNumber_anti h
          simpa [NcoverAL] using h'
        have h9 : ENNReal.ofReal (Real.rpow δ (-(2 * s + εA))) ≤
            ENNReal.ofReal (Real.rpow δ_n (-(2 * s + εA_int))) :=
          ENNReal.ofReal_le_ofReal h_exp1
        intro h10
        have h11 : ENNReal.ofReal (Real.rpow δ (-(2 * s + εA))) ≤ NcoverAL δ allTubes :=
          le_trans h9 (le_trans h10 h_ncover_mono)
        exact h_fine h11
      have h_coarse_fail_n : ¬(ENNReal.ofReal (Real.rpow δ_n (-(s + εA_int))) ≤
          NcoverAL (Real.sqrt δ_n) allTubes) := by
        have h_a1 : 0 ≤ s + εA := by positivity
        have h_a2 : s + εA ≤ 3 := by linarith
        have h_exp1 : Real.rpow δ (-(s + εA)) ≤
            Real.rpow δ_n (-(s + εA + ρ_scale)) := h_exp_transfer (s + εA) h_a1 h_a2
        have h_eq : (s + εA + ρ_scale) = (s + εA_int) := by
          dsimp only [εA_int] <;> ring
        rw [h_eq] at h_exp1
        have h_sqrt_mono : Real.sqrt δ ≤ Real.sqrt δ_n := Real.sqrt_le_sqrt hδ_le_δ_n'
        have h_ncover_mono : NcoverAL (Real.sqrt δ_n) allTubes ≤ NcoverAL (Real.sqrt δ) allTubes := by
          have h : (Real.sqrt δ).toNNReal ≤ (Real.sqrt δ_n).toNNReal := by exact Real.toNNReal_mono h_sqrt_mono
          have h' : Metric.externalCoveringNumber (Real.sqrt δ_n).toNNReal allTubes ≤ Metric.externalCoveringNumber (Real.sqrt δ).toNNReal allTubes :=
            Metric.externalCoveringNumber_anti h
          simpa [NcoverAL] using h'
        have h9 : ENNReal.ofReal (Real.rpow δ (-(s + εA))) ≤
            ENNReal.ofReal (Real.rpow δ_n (-(s + εA_int))) :=
          ENNReal.ofReal_le_ofReal h_exp1
        intro h10
        have h11 : ENNReal.ofReal (Real.rpow δ (-(s + εA))) ≤ NcoverAL (Real.sqrt δ) allTubes :=
          le_trans h9 (le_trans h10 h_ncover_mono)
        exact h_coarse h11

      -- ====================================================================
      -- Step 5: DeltasSet extraction at δ_n (replaces cardP_thinning)
      -- Produces Pbar with S-set property and Ncover lower bound
      -- ====================================================================
      have hP_bounded : Bornology.IsBounded P :=
        Bornology.IsBounded.subset Metric.isBounded_closedBall hP_subset
      have h_eq_n : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n := h_dyadic_eq n
      have hP_sset_scale' : IsDeltaSSet (DiscretisedFurstenbergEstimate.dyadicDelta n) u (81 * Real.rpow δ (-εA)) P := by
        rw [←h_eq_n]
        exact hP_sset_scale
      rcases deltasSet_extraction_dyadic_main hP_sset_scale' hP_bounded hP_subset
          (by linarith) (by linarith) with
        ⟨Pbar, hPbar_subset, hPbar_sep_deltas, hPbar_sset_scale, hPbar_card, hPbar_ncover_lower⟩

      -- (hPbar_card_t removed: unused dead code)

      -- ====================================================================
      -- Step 6: source_to_nice_configuration at δ_n (exact dyadic scale)
      -- ====================================================================
      let Pbar_set : Set EuclideanPlane := (Pbar : Set EuclideanPlane)
      -- Local abstraction to avoid dependent-type unification timeouts:
      -- Tp p hp is the tube family at p, where hp proves p ∈ Pbar_set.
      let Tp (p : EuclideanPlane) (hp : p ∈ Pbar_set) : Set AffineLine :=
        tubeFamily p (hPbar_subset hp)
      let allTubes_bar : Set AffineLine :=
        ⋃ p, ⋃ hp : p ∈ Pbar_set, Tp p hp

      -- Transfer hypotheses from P to Pbar at δ_n
      let K_pack := MainAppendix.affineLine_packing_constant
      have hPbar_subset_ball : Pbar_set ⊆ Metric.closedBall 0 1 :=
        Set.Subset.trans hPbar_subset hP_subset
      have hPbar_sset_n : IsDeltaSSet δ_n u (Real.rpow δ_n (-εA_int)) Pbar_set := by
        -- hPbar_sset_scale has constant 10000 * (81 * δ^(-εA))
        -- Absorb into εA_int: need 10000 * 81 * δ^(-εA) ≤ δ_n^(-εA_int)
        have h_absorb1 : δ_n ≤ 4 * δ := hδ_n_le_4δ'
        have h_absorb2 : δ ≥ δ_n / 4 := by linarith
        have h_absorb3 := h_absorb3_shared
        have h_absorb4 : (10000 : ℝ) * 81 * Real.rpow δ (-εA) ≤
            (10000 : ℝ) * 81 * (4 : ℝ)^εA * Real.rpow δ_n (-εA) := by
          have h : (10000 : ℝ) * 81 * Real.rpow δ (-εA) ≤
              (10000 : ℝ) * 81 * ((4 : ℝ)^εA * Real.rpow δ_n (-εA)) :=
            mul_le_mul_of_nonneg_left h_absorb3 (by positivity)
          have h_eq : (10000 : ℝ) * 81 * ((4 : ℝ)^εA * Real.rpow δ_n (-εA)) =
              (10000 : ℝ) * 81 * (4 : ℝ)^εA * Real.rpow δ_n (-εA) := by ring
          rw [h_eq] at h
          exact h
        have h_absorb5 : δ_n ≤ (10000 * 81 * (4 : ℝ)^εA)^(-1 / ρ_scale) := by
          let C : ℝ := 10000 * 81 * (4 : ℝ)^εA
          have hC_pos : 0 < C := by positivity
          have h1 : C ≤ Real.rpow δ_n (-ρ_scale) := h_scale_absorb_general
          have h_exp_nonpos : -1 / ρ_scale ≤ 0 := by
            have h2 : 0 ≤ 1 / ρ_scale := by positivity
            have h3 : -(1 / ρ_scale) ≤ 0 := Left.neg_nonpos_iff.mpr h2
            have h4 : -1 / ρ_scale = -(1 / ρ_scale) := by ring
            rw [h4]
            exact h3
          have h2 : Real.rpow (Real.rpow δ_n (-ρ_scale)) (-1 / ρ_scale) ≤ Real.rpow C (-1 / ρ_scale) :=
            Real.rpow_le_rpow_of_nonpos hC_pos h1 h_exp_nonpos
          have h3 : Real.rpow (Real.rpow δ_n (-ρ_scale)) (-1 / ρ_scale) = δ_n := by
            have h_rpow_mul : Real.rpow (Real.rpow δ_n (-ρ_scale)) (-1 / ρ_scale) = Real.rpow δ_n ((-ρ_scale) * (-1 / ρ_scale)) := by
              exact (Real.rpow_mul hδ_n_pos.le (-ρ_scale) (-1 / ρ_scale)).symm
            rw [h_rpow_mul]
            have h4 : (-ρ_scale) * (-1 / ρ_scale) = 1 := by
              field_simp [hρ_scale_pos.ne'] <;> ring
            rw [h4]
            simp
          rw [h3] at h2
          exact h2
        have h_absorb6 : Real.rpow δ_n (-ρ_scale) ≥ (10000 * 81 * (4 : ℝ)^εA) :=
          h_scale_absorb_general
        have h_absorb7 : (10000 : ℝ) * 81 * (4 : ℝ)^εA * Real.rpow δ_n (-εA) ≤
            Real.rpow δ_n (-εA_int) := by
          have h14 : -εA_int = (-εA) + (-ρ_scale) := by
            simp only [εA_int] <;> ring
          have h13 : Real.rpow δ_n (-εA_int) = Real.rpow δ_n (-εA) * Real.rpow δ_n (-ρ_scale) := by
            rw [h14]
            exact Real.rpow_add hδ_n_pos (-εA) (-ρ_scale)
          rw [h13]
          have h16 : 0 ≤ Real.rpow δ_n (-εA) := Real.rpow_nonneg hδ_n_pos.le _
          have h17 : (10000 : ℝ) * 81 * (4 : ℝ)^εA * Real.rpow δ_n (-εA) =
              Real.rpow δ_n (-εA) * ((10000 : ℝ) * 81 * (4 : ℝ)^εA) := by ring
          rw [h17]
          gcongr
        have h_const_le : (10000 : ℝ) * (81 * Real.rpow δ (-εA)) ≤
            Real.rpow δ_n (-εA_int) := by
          have h1 : (10000 : ℝ) * (81 * Real.rpow δ (-εA)) = (10000 : ℝ) * 81 * Real.rpow δ (-εA) :=
            (mul_assoc (10000 : ℝ) 81 (Real.rpow δ (-εA))).symm
          rw [h1]
          exact le_trans h_absorb4 h_absorb7
        have hPbar_sset_n : IsDeltaSSet δ_n u (10000 * (81 * Real.rpow δ (-εA))) Pbar_set := by
          dsimp only [Pbar_set]
          exact h_eq_n.symm ▸ hPbar_sset_scale
        exact IsDeltaSSet.weaken_C hPbar_sset_n h_const_le
      let hTbar_sset_n : ∀ (p : EuclideanPlane) (hp : p ∈ Pbar_set),
          IsDeltaSSet δ_n s (Real.rpow δ_n (-εA_int)) (Tp p hp) := by
        intro p hp
        have h_orig : IsDeltaSSet δ_n s (Real.rpow δ_n (-εA_int)) (tubeFamily p (hPbar_subset hp)) :=
          hT_sset_n p (hPbar_subset hp)
        have h_eq : Tp p hp = tubeFamily p (hPbar_subset hp) := by rfl
        exact h_eq.symm ▸ h_orig
      have h_offset_simple : ∀ (p : EuclideanPlane) (hp : p ∈ Pbar_set),
          ∀ (ℓ : AffineLine), ℓ ∈ tubeFamily p (hPbar_subset hp) →
            ℓ.offset ∈ Metric.closedBall (0 : EuclideanPlane) 2 := by
        intro p hp ℓ hℓ
        have h_p_in_ball : ‖p‖ ≤ 1 := by
          have h : p ∈ Metric.closedBall (0 : EuclideanPlane) 1 := hPbar_subset_ball hp
          have hdist : dist p (0 : EuclideanPlane) ≤ 1 := Metric.mem_closedBall.mp h
          have heq : dist p (0 : EuclideanPlane) = ‖p‖ := by simp [dist_comm]
          rw [heq] at hdist; exact hdist
        have h_inc : p ∈ Metric.cthickening δ_n (ℓ.1 : Set EuclideanPlane) :=
          hIncidence_n p (hPbar_subset hp) ℓ hℓ
        have hδ_n_le_one : δ_n ≤ 1 := delta_n_le_one hδ_n_le_4δ' hδ_le_δA hδA_le_third_const
        have h3 : ‖ℓ.offset‖ ≤ 2 := affine_line_offset_bound p ℓ h_p_in_ball hδ_n_pos hδ_n_le_one h_inc
        simpa [Metric.mem_closedBall, dist_zero_right] using h3
      have h_offset : ∀ (p : EuclideanPlane) (hp : p ∈ Pbar_set),
          ∀ (ℓ : AffineLine), ℓ ∈ Tp p hp →
            ℓ.offset ∈ Metric.closedBall (0 : EuclideanPlane) 2 := by
        intro p hp ℓ hℓ
        have hTp : Tp p hp = tubeFamily p (hPbar_subset hp) := by rfl
        rw [hTp] at hℓ
        exact h_offset_simple p hp ℓ hℓ
      have hT_bounded : Bornology.IsBounded allTubes_bar :=
        tubes_bounded (Tp := Tp) h_offset allTubes_bar rfl

      -- C_T bound for source_to_nice: δ_n^{-εA_int} ≤ δ_n^{-ε_tube}
      have hC_T_bound : Real.rpow δ_n (-εA_int) ≤ Real.rpow δ_n (-ε_tube) := by
        have h1 : εA_int ≤ ε_tube := hεA_int_lt_tube.le
        have h2 : -ε_tube ≤ -εA_int := neg_le_neg h1
        have hδ_n_le_one : δ_n ≤ 1 := delta_n_le_one hδ_n_le_4δ' hδ_le_δA hδA_le_third_const
        have h_main : Real.rpow δ_n (-εA_int) ≤ Real.rpow δ_n (-ε_tube) :=
          Real.rpow_le_rpow_of_exponent_ge (x := δ_n) (y := -εA_int) (z := -ε_tube)
            hδ_n_pos hδ_n_le_one h2
        exact h_main

      have hδ_n_le_nice : δ_n ≤ δ₀_nice := delta_n_le_nice hδ_n_le_4δ' hδ_le_δA hδA_le_nice

      -- Section 9 instantiated at local u (preserve exponent chain: u → B1 → A1/A2/A4)
      have hsu : s < u := lt_of_lt_of_le hst hu_t

      have hC_P_pos' : 0 < Real.rpow δ_n (-εA_int) := rpow_pos_helper δ_n (-εA_int) hδ_n_pos
      have hC_T_pos' : 0 < Real.rpow δ_n (-εA_int) := rpow_pos_helper δ_n (-εA_int) hδ_n_pos
      let hSub : ∀ (p : EuclideanPlane) (hp : p ∈ Pbar_set), Tp p hp ⊆ allTubes_bar :=
        fun p hp => Set.subset_iUnion₂ p hp
      have hInc : ∀ (p : EuclideanPlane) (hp : p ∈ Pbar_set),
          ∀ (T : AffineLine), T ∈ Tp p hp →
            p ∈ Metric.cthickening δ_n (T.1 : Set EuclideanPlane) := by
        intro p hp T hT
        simpa [Tp] using hIncidence_n p (hPbar_subset hp) T hT

      rcases h_nice_main δ_n hδ_n_pos hδ_n_le_nice s u hs_pos hs_lt_one hsu
          (Real.rpow δ_n (-εA_int)) (Real.rpow δ_n (-εA_int))
          hC_P_pos' hC_T_pos' hC_T_bound
          Pbar_set hPbar_subset_ball hPbar_sset_n
          allTubes_bar hT_bounded
          Tp hSub hTbar_sset_n hInc h_offset with
        ⟨n_cfg, M, config, P_ret, P_oriented, T_oriented, swapped,
         ρ_mass, ρ_M, ρ_T,
         hδ_n_le, hδ_lt_2δ_n, hρ_mass_nonneg, hρ_M_nonneg, hρ_T_nonneg,
         hρ_sum, hM_pos, hM_dyadic, hP_ret_subset, h_swapped_false, h_swapped_true,
         hNcover_T_eq, h_squares_meet, hP_oriented_subset,
         hNcover_pointSet_lower, hM_lower, hM_upper, hT₀_upper,
         h_tubes_strip, h_tubes_intercept, h_tubes_bounded, h_section9_prov⟩

      -- ====================================================================
      -- Step 7: Prove n_cfg = n by dyadic uniqueness
      -- ====================================================================
      have h1 : dyadicDelta n_cfg ≤ dyadicDelta n := by
        have h_a : DiscretisedFurstenbergEstimate.dyadicDelta n_cfg ≤ DiscretisedFurstenbergEstimate.dyadicDelta n := by
          rw [←h_eq_n]; exact hδ_n_le
        have h_b : dyadicDelta n_cfg = DiscretisedFurstenbergEstimate.dyadicDelta n_cfg := h_dyadic_eq n_cfg
        have h_c : dyadicDelta n = DiscretisedFurstenbergEstimate.dyadicDelta n := h_dyadic_eq n
        rw [h_b, h_c]; exact h_a
      have h2 : dyadicDelta n < 2 * dyadicDelta n_cfg := by
        have h_a : DiscretisedFurstenbergEstimate.dyadicDelta n < 2 * DiscretisedFurstenbergEstimate.dyadicDelta n_cfg := by
          rw [←h_eq_n]; exact hδ_lt_2δ_n
        have h_b : dyadicDelta n_cfg = DiscretisedFurstenbergEstimate.dyadicDelta n_cfg := h_dyadic_eq n_cfg
        have h_c : dyadicDelta n = DiscretisedFurstenbergEstimate.dyadicDelta n := h_dyadic_eq n
        rw [h_b, h_c]; exact h_a
      have h_step : ∀ k : ℕ, dyadicDelta (k + 1) = (1 / 2 : ℝ) * dyadicDelta k :=
        dyadicDelta_step'
      have h_anti : ∀ a b : ℕ, a ≤ b → dyadicDelta b ≤ dyadicDelta a :=
        dyadicDelta_anti'
      have h_ncfg_le_n : n_cfg ≤ n :=
        ncfg_le_n_from_dyadic n n_cfg h1 h2 h_step h_anti
      have h_n_le_ncfg : n ≤ n_cfg :=
        n_le_ncfg_from_dyadic n n_cfg h1 h_step h_anti
      have hn_cfg_eq : n_cfg = n := le_antisymm h_ncfg_le_n h_n_le_ncfg

      -- ====================================================================
      -- Step 8: Set up C₁ and M
      -- Define C₁ to match config's C parameter after subst n_cfg
      -- ====================================================================
      let C₁ : ℝ := (DiscretisedFurstenbergEstimate.dyadicDelta n)^(-lam)
      have hlam_pos : 0 < lam := half_pos hε_pos
      have hC₁ : 1 ≤ C₁ := by
        dsimp only [C₁]
        have h_dyadic_pos : 0 < DiscretisedFurstenbergEstimate.dyadicDelta n := by
          rw [←h_eq_n]; exact hδ_n_pos
        have h_dyadic_lt_one : DiscretisedFurstenbergEstimate.dyadicDelta n < 1 := by
          rw [←h_eq_n]; exact lt_of_le_of_lt hδ_le_D hΔ_lt_one
        exact one_le_rpow_neg h_dyadic_pos h_dyadic_lt_one hlam_pos
      have hC_fine_bound : C₁ ≤ Real.rpow δ_n (-ε / 2) := by
        dsimp only [C₁]
        have h_lam : lam = ε / 2 := rfl
        rw [h_lam]
        have h_exp : -(ε / 2) = -ε / 2 := by ring
        rw [h_exp]
        rw [h_eq_n] <;> rfl
      have hC₁_eq_delta : C₁ = Real.rpow δ_n (-lam) := by
        dsimp only [C₁]
        rw [h_eq_n] <;> rfl
      have hδA_tube_pos : 0 < δA_tube := by
        dsimp only [δA_tube]
        positivity
      have h9 : δ_n ≤ 4 * δA_tube :=
        le_trans hδ_n_le_4δ'
          (le_trans (mul_le_mul_of_nonneg_left hδ_le_δA (by norm_num))
            (mul_le_mul_of_nonneg_left hδA_le_tube (by norm_num)))
      have h_tube_sset_absorb : (4000 : ℝ) * 44^s ≤ Real.rpow δ_n (-ε / 2) :=
        tube_sset_absorb_helper δ_n δA_tube ε s hδ_n_pos hδA_tube_pos hε_pos hs_pos.le h9 rfl

      subst n_cfg
      -- After subst: config, hM_lower, hM_upper, hM_dyadic, h_squares_meet,
      -- h_tubes_strip, etc. all have types involving n instead of n_cfg.
      -- Clear uniqueness-proof hypotheses to reduce context size.
      clear h1 h2 h_ncfg_le_n h_n_le_ncfg h_step h_anti

      have hM_lower' : (M : ℝ) ≥ δ_n ^ (-s + lam + ρ_M) := by
        rw [h_eq_n.symm] at hM_lower
        exact hM_lower
      have hM_upper' : (M : ℝ) ≤ 28 * Real.rpow δ_n (-s) := by
        rw [h_eq_n.symm] at hM_upper
        exact hM_upper
      have hδ_n_lt_one : δ_n < 1 := lt_of_le_of_lt hδ_le_D hΔ_lt_one
      have h4pos : (0 : ℝ) ≤ 4 := by norm_num
      have hδ_n_le_4δA : δ_n ≤ 4 * δA := by
        calc δ_n ≤ 4 * δ := hδ_n_le_4δ'
             _ ≤ 4 * δA := mul_le_mul_of_nonneg_left hδ_le_δA h4pos
      have hδA_le_M : δA ≤ (1 / 4 : ℝ) * Real.rpow 2 (1 / e_max) := by
        have h1 : δA ≤ δA_M := le_trans (min_le_right _ _) (min_le_left _ _)
        exact h1
      have hρ_M_le_budget : ρ_M ≤ reserved_budget := by linarith [hρ_sum]
      have h_exponent_le : (-s + lam + ρ_M) ≤ e_max := by
        dsimp only [e_max] <;> linarith
      have hM_even : M % 2 = 0 := m_even_helper M δ_n δA s lam ρ_M e_max
        hM_dyadic hM_lower' hδ_n_pos hδ_n_lt_one hδA_pos hδ_n_le_4δA hδA_le_M h_exponent_le he_max_neg
      have hρ_M_le_20 : ρ_M ≤ ε / 20 := by
        dsimp only [reserved_budget] at hρ_M_le_budget
        exact hρ_M_le_budget
      have hlam_eq : lam = ε / 2 := rfl
      have hM_fine_lower : (M : ℝ) / 2 ≥ Real.rpow Δ (-2 * s + 2 * ε) :=
        m_fine_lower_helper M δ_n Δ s ε lam ρ_M hlam_eq hM_lower'
          hδ_n_eq2 hΔ_pos hΔ_lt_one hε_pos hρ_M_le_20 h_small
      have hM_fine_upper : (M : ℝ) ≤ Real.rpow Δ (-2 * s - ε) :=
        m_fine_upper_helper M δ_n Δ s ε hM_upper'
          hδ_n_eq2 hΔ_pos hΔ_lt_one hε_pos h_small

      -- config already has type CTNiceConfiguration n s C₁ M after subst
      let config_n : CTNiceConfiguration n s C₁ M := config

      -- ====================================================================
      -- Step 9: K_dummy/K_real split and numerical bounds
      -- K_dummy goes ONLY to apply_numerical_hypotheses.
      -- K_real = affineLine_packing_constant + 1 goes to B1 → A1 → G → A2.
      -- ====================================================================
      let K_dummy : ℝ := Real.rpow Δ (-2 * ε) / 12
      have hK_dummy_pos : 0 < K_dummy := by
        dsimp only [K_dummy]
        have h1 : 0 < Real.rpow Δ (-2 * ε) := Real.rpow_pos_of_pos hΔ_pos (-2 * ε)
        exact div_pos h1 (by norm_num)
      have hK_dummy_bound : K_dummy ≤ Real.rpow Δ (-2 * ε) / 6 := by
        dsimp only [K_dummy]
        have h1 : 0 ≤ Real.rpow Δ (-2 * ε) := Real.rpow_nonneg hΔ_pos.le (-2 * ε)
        gcongr <;> norm_num

      have hM_pos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
      have h_num_data := apply_numerical_hypotheses
        h_num_bounds hΔ_pos hΔ_lt_δ₀ hδ_n_pos hδ_n_eq2
        hK_dummy_pos hK_dummy_bound hM_pos' hM_fine_lower hM_fine_upper

      rcases h_num_data with
        ⟨h_small_A2, h_num, h_uniform_num, hΔ_small_allFine, hKpack_le_ε, h_absorb_energy,
         h_absorb_Y, h_absorb_X, h_absorb_T,
         hΔ_le_δ₀_axiom, hΔ_lt_half', hΔ_lt_third', hΔ_lt_16', hΔ_lt_one',
         h_small_eps,
         h_energy_uniform_absorb, h_Y_uniform_absorb,
         h_C_Y_uniform_bound, h_C_energy_uniform_bound, h_four_pow_u_bound,
         h_uniform_energy, h_uniform_Y⟩

      -- K_real: actual packing constant for B1 bridge
      let K_real : ℝ := (MainAppendix.affineLine_packing_constant : ℝ) + 1
      have hK_real_pos : 0 < K_real := by positivity
      have hK_real_bound : K_real ≤ Real.rpow Δ (-2 * ε) / 6 := by
        have h1 : 6 * K_real ≤ Real.rpow Δ (-ε) := h_small_A2.hKpack_loss_strong
        have h2 : Real.rpow Δ (-ε) ≤ Real.rpow Δ (-2 * ε) := by
          have h3 : -2 * ε ≤ -ε := by linarith [hε_pos]
          exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one'.le h3
        have h4 : 6 * K_real ≤ Real.rpow Δ (-2 * ε) := le_trans h1 h2
        linarith

      -- ====================================================================
      -- Step 10: B1 bridge decomposition
      -- ====================================================================
      let csq : DiscretisedFurstenbergEstimate.DyadicSquare n → DiscretisedFurstenbergEstimate.DyadicSquare m :=
        DiscretisedFurstenbergEstimate.InductionConfigurations.containingSquare hnm
      let coarseP₀ : Finset (DiscretisedFurstenbergEstimate.DyadicSquare m) := config_n.P₀.image csq

      -- Helper bounds
      have hu_pos : 0 < u := by linarith [hu_t, ht_pos]
      have hεA_int_le : εA_int ≤ 401 * ε / 10000 := by
        dsimp only [εA_int, εA, ρ_scale] <;> linarith [hε_pos]
      have hεA_run_pos : 0 < εA_run := by
        dsimp only [εA_run, EndpointAdapter.endpointAdapter]
        split_ifs with h
        · exact hεA_pos
        · have hpos : 0 < min (εA / 200) ((2 - t) / 4) := by
            apply lt_min <;> linarith [hεA_pos, ht_lt_two]
          linarith [hεA_pos, hpos]
      have hεA_run_le : εA_run ≤ 201 * ε / 10000 := by
        dsimp only [εA_run, EndpointAdapter.endpointAdapter]
        split_ifs with h
        · dsimp only [εA] <;> linarith [hε_pos]
        · have h1 : min (εA / 200) ((2 - t) / 4) ≤ εA / 200 := min_le_left _ _
          dsimp only [εA] at * <;> linarith [hε_pos]
      have hΔ_eq : Δ = dyadicDelta m := by rfl

      -- Swap-aware reference set
      let Ref_fin : Finset EuclideanPlane :=
        if swapped then Pbar.image CoordinatePartition.swapCoords else Pbar
      have hRef_coe : (Ref_fin : Set EuclideanPlane) =
          (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane)
           else (Pbar : Set EuclideanPlane)) := by
        unfold Ref_fin
        split_ifs <;> rfl
      have hP_oriented_sub_Ref : P_oriented ⊆ (Ref_fin : Set EuclideanPlane) := by
        rw [hRef_coe]
        by_cases h_sw : swapped
        · have h := h_swapped_true (by simp [h_sw])
          have h2 : P_ret ⊆ Pbar_set := hP_ret_subset
          have h3 : CoordinatePartition.swapCoords '' P_ret ⊆ CoordinatePartition.swapCoords '' Pbar_set :=
            Set.image_mono h2
          rw [if_pos h_sw]
          have h4 : (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane) =
              CoordinatePartition.swapCoords '' Pbar_set := by
            unfold Pbar_set
            rw [Finset.coe_image]
          rw [h4]
          exact Set.Subset.trans h.1 h3
        · have h := h_swapped_false (by simp [h_sw])
          rw [if_neg h_sw]
          exact Set.Subset.trans h.1 hP_ret_subset
      -- Convert Pbar separation from dyadicDelta n to δ_n and wrap as Set.Pairwise
      have hPbar_sep_pairwise : Set.Pairwise Pbar_set (fun p q => δ_n ≤ dist p q) := by
        intro p hp q hq hne
        rw [h_eq_n]
        exact hPbar_sep_deltas p hp q hq hne
      -- Convert Pbar ncover lower from dyadicDelta n to δ_n
      have hPbar_ncover_lower' : Metric.externalCoveringNumber δ_n.toNNReal Pbar_set ≥
          ENNReal.ofReal ((1 / 10000 : ℝ) * (81 * Real.rpow δ (-εA))⁻¹ * Real.rpow δ_n (-u)) := by
        rw [←h_eq_n] at hPbar_ncover_lower
        exact hPbar_ncover_lower
      -- Transport all Pbar properties to Ref_fin in one call
      have h_transport := transport_Ref_fin Pbar swapped hPbar_sset_n hPbar_sep_pairwise hPbar_ncover_lower'
      rcases h_transport with ⟨hRef_sset, hRef_sep, hRef_card, hRef_ncover_lower⟩

      -- pointSet data
      have hpointSet_sub : config_n.pointSet ⊆
          ⋃ p ∈ (config_n.P₀ : Set (DiscretisedFurstenbergEstimate.DyadicSquare n)), (p.toSet : Set EuclideanPlane) := by
        simp [NiceConfiguration.pointSet]
      -- Transport hNcover_pointSet_lower from dyadicDelta n scale to δ_n scale.
      -- Use congr_arg to rewrite only the Ncover scale argument, avoiding
      -- dependent-type issues with config's C parameter.
      have h_transport : Section9.Ncover δ_n config_n.pointSet ≥
          ENNReal.ofReal (δ_n ^ ρ_mass) * Section9.Ncover δ_n Pbar_set := by
        let S : Set EuclideanPlane := config_n.pointSet
        have hS : S = NiceConfiguration.pointSet config := by rfl
        have h1 : Section9.Ncover δ_n S = Section9.Ncover (DiscretisedFurstenbergEstimate.dyadicDelta n) S :=
          congr_arg (fun x : ℝ => Section9.Ncover x S) h_eq_n
        have h2 : Section9.Ncover δ_n Pbar_set = Section9.Ncover (DiscretisedFurstenbergEstimate.dyadicDelta n) Pbar_set :=
          congr_arg (fun x : ℝ => Section9.Ncover x Pbar_set) h_eq_n
        have h3 : ENNReal.ofReal (δ_n ^ ρ_mass) = ENNReal.ofReal ((DiscretisedFurstenbergEstimate.dyadicDelta n) ^ ρ_mass) :=
          congr_arg (fun x : ℝ => ENNReal.ofReal (x ^ ρ_mass)) h_eq_n
        rw [h1, h2, h3, hS]
        exact hNcover_pointSet_lower

      have hNcover_pointSet_lower_Ref : Metric.externalCoveringNumber δ_n.toNNReal config_n.pointSet ≥
          ENNReal.ofReal (Real.rpow δ_n ρ_mass) *
            Metric.externalCoveringNumber δ_n.toNNReal (Ref_fin : Set EuclideanPlane) := by
        rw [hRef_coe]; split_ifs with h
        · have h_eq : Metric.externalCoveringNumber δ_n.toNNReal
              ((Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane)) =
              Metric.externalCoveringNumber δ_n.toNNReal (Pbar : Set EuclideanPlane) := by
            simpa using CoordinatePartition.externalCoveringNumber_image_of_involutive_isometry
              CoordinatePartition.swapCoords_isometry CoordinatePartition.swapCoords_invol
              δ_n.toNNReal (Pbar : Set EuclideanPlane)
          rw [h_eq]
          simpa [config_n] using h_transport
        · simpa [config_n] using h_transport

      -- Numerical: hΔ_small_eps5 prerequisites (hδ_n_le_4δA already defined above)
      have hΔ_le_2sqrtδA : Δ ≤ 2 * Real.sqrt δA := by
        have h1 : Δ = Real.sqrt δ_n := by
          rw [hδ_n_eq2]; rw [Real.sqrt_sq hΔ_pos.le]
        rw [h1]
        have h2 : Real.sqrt δ_n ≤ Real.sqrt (4 * δA) := Real.sqrt_le_sqrt hδ_n_le_4δA
        have h3 : Real.sqrt (4 * δA) = 2 * Real.sqrt δA := by
          rw [Real.sqrt_mul] <;> norm_num <;> linarith
        rw [h3] at h2; exact h2
      have hδA_le_B1 : δA ≤ δA_B1 := by
        dsimp only [δA]
        apply le_trans (min_le_right _ _)
        apply le_trans (min_le_right _ _)
        apply le_trans (min_le_right _ _)
        apply le_trans (min_le_right _ _)
        apply le_trans (min_le_right _ _)
        apply le_trans (min_le_right _ _)
        apply le_trans (min_le_right _ _)
        apply le_trans (min_le_right _ _)
        apply le_trans (min_le_right _ _)
        exact min_le_left _ _

      -- Numerical: B1 threshold arithmetic via helper
      have h_b1_data := b1_threshold_arith
          ε εA ρ_mass reserved_budget Δ δA C_B1 e_B1
          hε_pos rfl rfl (by linarith [hρ_sum])
          hΔ_pos hΔ_lt_one
          he_B1_pos rfl
          hC_B1_pos (by positivity) hδA_le_B1 hΔ_le_2sqrtδA

      have h_exponent_eps5 := h_b1_data.1
      have h_b1_3 : Real.rpow Δ (ε / 5 - 2 * εA - 2 * ρ_mass) ≤ C_B1 := h_b1_data.2.2
      have hΔ_small_eps5 : (1 / 810000 : ℝ) * Real.rpow 4 (-εA) ≥
          Real.rpow Δ (ε / 5 - 2 * εA - 2 * ρ_mass) := by
        have h : C_B1 = (1 / 810000 : ℝ) * Real.rpow 4 (-εA) := by
          dsimp only [C_B1] <;> rfl
        rw [h] at h_b1_3
        exact h_b1_3

      -- Numerical: h_absorb_sset via helper lemma
      have hδ_n_le_one : δ_n ≤ 1 := delta_n_le_one_lemma δ_n Δ hδ_n_eq2 hΔ_pos hΔ_lt_one
      have h_small8 : Real.rpow δ_n (ε / 8) ≤ 1 / 100 := small8_lemma δ_n Δ ε hδ_n_eq2 hΔ_pos h_small_eps
      have h_sum_le : ρ_mass + εA_int ≤ ε / 2 := by linarith
      have h_absorb_sset : (25 : ℝ) * 625 * (2 : ℝ)^u * Real.rpow δ_n (-ρ_mass) *
          Real.rpow δ_n (-εA_int) ≤ Real.rpow δ_n (-ε) :=
        absorb_sset_lemma δ_n u ε ρ_mass εA_int hδ_n_pos hδ_n_le_one hu_two hε_pos h_sum_le h_small8

      -- Smallness h_small2, h_small3 via helpers
      have h_small2 : Real.rpow Δ (ε / 20) ≤ 1 / 2 :=
        small2_lemma Δ ε hΔ_pos h_small_eps
      have h_small3 : Real.rpow Δ (3 * ε / 10) ≤ 1 / 2 :=
        small3_lemma Δ ε hΔ_pos hΔ_lt_one hε_pos h_small_eps

      -- P_oriented in unit ball via helper (avoids heartbeat timeouts)
      have hP_oriented_ball : P_oriented ⊆ Metric.closedBall 0 1 :=
        p_oriented_ball_helper hP_ret_subset hPbar_subset_ball
          (fun h => (h_swapped_true h).1)
          (fun h => (h_swapped_false h).1)

      -- Square centers in enlarged ball via helper
      have h_points_in_ball_R_b1 :
          ((config_n.P₀.image localSquareCenter) : Set EuclideanPlane) ⊆
          Metric.closedBall 0 (1 + Real.sqrt 2 * δ_n / 2) :=
        centers_in_ball config_n.P₀ P_oriented h_eq_n.symm hP_oriented_ball h_squares_meet

      -- Three card bounds via B1FrontUpperBounds
      let B_centers : Finset EuclideanPlane := config_n.P₀.image localSquareCenter
      have h_match_backward : ∀ q ∈ B_centers, ∃ p ∈ (Ref_fin : Set EuclideanPlane), dist q p ≤ δ_n :=
        match_backward_lemma config_n.P₀ P_oriented Ref_fin h_eq_n.symm h_squares_meet hP_oriented_sub_Ref
      have h_intersect : ∀ Q ∈ coarseP₀,
          ((B_centers : Set EuclideanPlane) ∩ (Q.toSet : Set EuclideanPlane)).Nonempty := by
        intro Q hQ
        rcases Finset.mem_image.mp hQ with ⟨p, hp, rfl⟩
        have h1 : localSquareCenter p ∈ B_centers := Finset.mem_image.mpr ⟨p, hp, rfl⟩
        have h2 : localSquareCenter p ∈ (p.toSet : Set EuclideanPlane) :=
          localSquareCenter_mem_toSet h_eq_n.symm p
        have h3 : (p.toSet : Set EuclideanPlane) ⊆ ((csq p).toSet : Set EuclideanPlane) :=
          fine_square_subset_coarse hnm p
        exact ⟨localSquareCenter p, h1, h3 h2⟩

      -- Adapt hPbar_card from dyadicDelta n scale to δ_n scale
      have hPbar_card' : (Pbar.card : ℝ) ≤ 100 * Real.rpow δ_n (-u) :=
        adapt_pbar_card hPbar_card h_eq_n
      have hP_oriented_sub_Ref' : P_oriented ⊆
          (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane)
           else (Pbar : Set EuclideanPlane)) := by
        rw [←hRef_coe]
        exact hP_oriented_sub_Ref

      have h_fine_card_upper_orig : (config_n.P₀.card : ℝ) ≤ Real.rpow Δ (-2 * u - ε / 4) :=
        fine_card_upper_from_front (m := m) (hnm := hnm)
          hΔ_pos hΔ_lt_one hδ_n_pos hδ_n_eq2 hε_pos
          (hPbar_card := hPbar_card')
          (h_squares_meet := h_squares_meet)
          swapped hP_oriented_sub_Ref' h_small_eps

      -- Adapt hΔ_eq from local dyadicDelta to official
      have hΔ_eq' : Δ = DiscretisedFurstenbergEstimate.dyadicDelta m :=
        hΔ_eq.trans (h_dyadic_eq m)

      -- Adapt h_match_backward from Ref_fin to expected if-expression
      have h_match_backward' : ∀ q ∈ B_centers,
          ∃ p ∈ (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane)
                   else (Pbar : Set EuclideanPlane)), dist q p ≤ δ_n := by
        intro q hq
        rcases h_match_backward q hq with ⟨p, hp, hdist⟩
        have h1 : (Ref_fin : Set EuclideanPlane) =
            (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane)
             else (Pbar : Set EuclideanPlane)) := by
          unfold Ref_fin
          split_ifs <;> simp <;> rfl
        have hp' : p ∈ (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane)
                         else (Pbar : Set EuclideanPlane)) := by
          rw [←h1]
          exact hp
        exact ⟨p, hp', hdist⟩

      have h_coarse_card_upper_orig : (coarseP₀.card : ℝ) ≤ Real.rpow Δ (-u - ε / 2) :=
        coarse_card_upper_from_front (n := n) (m := m) (hnm := hnm)
          hΔ_eq' hΔ_pos hΔ_lt_one hδ_pos hδ_n_pos hδ_n_eq2 hδ_le_δ_n' hδ_n_le_4δ'
          hu_pos hu_two hε_pos hε_lt_one hεA_run_pos hεA_run_le
          (P := P) (Pbar := Pbar) (Pfin := B_centers)
          (coarseP₀ := coarseP₀)
          hPbar_subset hNcover_sqrt swapped
          h_match_backward' h_intersect
          h_small_eps

      -- Convert Ref_fin properties to expected if-expression representation
      have hRef_sset' : IsDeltaSSet δ_n u (δ_n.rpow (-εA_int))
          (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane)
           else (Pbar : Set EuclideanPlane)) := by
        rw [←hRef_coe]
        exact hRef_sset
      have hRef_sep' : Set.Pairwise
          (if swapped then (Pbar.image CoordinatePartition.swapCoords : Set EuclideanPlane)
           else (Pbar : Set EuclideanPlane)) (fun p q => δ_n ≤ dist p q) := by
        rw [←hRef_coe]
        exact hRef_sep

      have h_per_square_upper_orig : ∀ Q ∈ coarseP₀,
          ((config_n.P₀.filter (fun p => csq p = Q)).card : ℝ) ≤
            Real.rpow Δ (-u - 3 * ε / 5) :=
        per_square_upper_from_front config_n
          hΔ_eq' hΔ_pos hΔ_lt_one hδ_n_pos h_eq_n hδ_n_eq2 hε_pos hεA_int_pos hεA_int_le
          (hPbar_card := hPbar_card')
          (h_squares_meet := h_squares_meet)
          swapped hP_oriented_sub_Ref' hRef_sset' hRef_sep' h_small_eps

      -- Call b1_assembly
      have hδ_ge : δ_n / 4 ≤ δ := by linarith [hδ_n_le_4δ']
      rcases b1_assembly hnm hn_even config_n
          hΔ_pos hΔ_lt_one hδ_n_pos h_eq_n hδ_n_eq2 hΔ_eq' hδ_ge
          (by linarith) hε_pos hεA_pos hρ_mass_nonneg
          (by positivity) (by positivity) (by rfl)
          h_exponent_eps5 hΔ_small_eps5
          (Pbar := Ref_fin)
          hRef_sset hRef_sep hRef_ncover_lower
          hpointSet_sub hNcover_pointSet_lower_Ref
          hP_oriented_sub_Ref hP_oriented_subset h_squares_meet h_absorb_sset
          h_fine_card_upper_orig h_coarse_card_upper_orig h_per_square_upper_orig
          h_tubes_strip h_tubes_intercept hM_even hC_fine_bound hC₁ h_tube_sset_absorb
          hM_fine_lower hM_fine_upper
          K_real hK_real_pos hK_real_bound
          h_small_eps h_small2 h_small3
          h_points_in_ball_R_b1 h_tubes_bounded with
        ⟨config', b1, hconfig'_subset⟩


      -- ====================================================================
      -- Step 10b: Helper bounds for GHI chain
      -- ====================================================================

      -- h_points_in_ball_R: needed by front_end_G (swapped centers)
      have h_points_in_ball_R :
          (config_n.P₀.image (CoordinatePartition.swapCoords ∘ localSquareCenter) : Set EuclideanPlane)
          ⊆ Metric.closedBall 0 (1 + Real.sqrt 2 * δ_n / 2) := by
        intro y hy
        exact swapped_centers_in_ball h_points_in_ball_R_b1 hy

      -- Coarse failure at original scale δ (from ¬h_coarse in both-fail branch)
      have h_coarse_failure_HDyadic :
          Metric.externalCoveringNumber (Real.sqrt δ).toNNReal allTubes ≤
          ENNReal.ofReal (Real.rpow δ (-(s + εA))) := by
        have h : Metric.externalCoveringNumber (Real.sqrt δ).toNNReal allTubes <
            ENNReal.ofReal (Real.rpow δ (-(s + εA))) := lt_of_not_ge h_coarse
        exact h.le

      -- K_pack absorption for C_global cardinality
      have h_absorb_Kpack : (CGlobalCardBound.kPack 1 17 : ℝ) ≤
          Real.rpow Δ (ε / 20 - 3 * ε) := by
        have h1 : (1329409 : ℝ) ≤ Real.rpow Δ (-(59 * ε / 20)) := h_num.h_absorb_Kpack_dyadic
        have h2 : (CGlobalCardBound.kPack 1 17 : ℝ) = (1329409 : ℝ) := by
          simp [CGlobalCardBound.kPack] <;> norm_num
        have h3 : ε / 20 - 3 * ε = -(59 * ε / 20) := by ring
        rw [h2, h3]; exact h1

      -- Packing constant absorption
      have h_pack_absorb_A7 : (MainAppendix.affineLine_packing_constant : ℝ) ≤
          Real.rpow Δ (-ε) := by
        have h : (MainAppendix.affineLine_packing_constant : ℝ) + 1 ≤ Real.rpow Δ (-ε) := hKpack_le_ε
        have hpos : 0 ≤ (MainAppendix.affineLine_packing_constant : ℝ) := by positivity
        linarith

      -- Log absorption (from parameter_selection δA_log1/δA_log2)
      have hδA_le_log1' : δA ≤ (1 / 4 : ℝ) * (ε / (8 * (3 : ℝ)^ε))^(1 / ε) := by
        convert hδA_le_log1 using 1 <;> ring
      have hδA_le_log2' : δA ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ)^(2 / (3 * ε)) := by
        convert hδA_le_log2 using 1 <;> ring
      have h_log_absorb : 4 * Real.log (3 / Δ) + 1 ≤ Real.rpow Δ (-3 * ε) :=
        log_absorption_lemma Δ ε δA hΔ_pos hΔ_lt_one hε_pos hδA_pos.le
          hΔ_le_2sqrtδA hδA_le_log1' hδA_le_log2'

      -- T_original for GHI
      let T_original : Set AffineLine := allTubes_bar
      have hT_original_sub : T_original ⊆ allTubes := by
        intro T hT
        rcases Set.mem_iUnion₂.mp hT with ⟨p, hp, hT'⟩
        exact Set.mem_iUnion₂.mpr ⟨p, hPbar_subset hp, hT'⟩

      -- ====================================================================
      -- Step 10c: Transport numerical data from t-level to local u-level
      -- ====================================================================

      -- A2_Smallness: t-level → u-level (phantom exponent transport)
      have h_small_A2_u : AppendixA.A2.A2_Smallness Δ δ_n s u ε A K_real (M : ℝ) :=
        AppendixA.A2_Smallness.transport h_small_A2

      -- Energy absorption: specialize uniform bound at local exponent u
      have h_absorb_energy_u :
          (MainAppendix.plane_energy_constant s u 2) * (MainAppendix.plane_packing_constant : ℝ) ≤
          Real.rpow Δ (-ε) :=
        h_uniform_energy u hu_t hu_two

      -- ====================================================================
      -- Step 11: Call front_end_G → GOutput
      -- ====================================================================
      let g : GOutput n m hnm Δ δ_n s u ε T_oriented :=
        front_end_G
          (hnm := hnm) (hm_pos := hm_pos) (hn_even := hn_even)
          (hΔ_eq' := hΔ_eq') (h_eq_n := h_eq_n) (hδ_n_eq2 := hδ_n_eq2)
          (hΔ_pos := hΔ_pos) (hΔ_lt_half := hΔ_lt_half') (hΔ_lt_one := hΔ_lt_one')
          (hΔ_lt_third := hΔ_lt_third')
          (hδ_n_pos := hδ_n_pos) (hδ_le_D := hδ_le_D)
          (hδ_pos := hδ_pos) (hδ_le_δ_n' := hδ_le_δ_n') (hδ_n_le_4δ' := hδ_n_le_4δ')
          (hε_pos := hε_pos) (hε_lt_one := hε_lt_one)
          (hs_pos := hs_pos) (hs_lt_one := hs_lt_one)
          (hsu := hsu) (hu_pos := hu_pos) (h_run_lt_two := h_run_lt_two)
          (h_small := h_small) (h_small_eps := h_small_eps)
          (hA_one := hA_one) (hQTTC := hQTTC) (hεA_eq := by rfl)
          (config_n := config_n) (config' := config') (b1 := b1)
          (hconfig'_subset := hconfig'_subset.1) (hconfig'_T0_eq := hconfig'_subset.2)
          (h_small_A2 := h_small_A2_u) (h_uniform_num := h_uniform_num)
          (h_absorb_energy := h_absorb_energy_u) (h_absorb_Kpack := h_absorb_Kpack)
          (h_points_in_ball_R := h_points_in_ball_R)
          (T_oriented := T_oriented) (h_section9_prov := fun U hU =>
            h_section9_prov U (by rw [←hconfig'_subset.2]; exact hU))
          (T_original := T_original) (allTubes := allTubes) (hT_original_sub := hT_original_sub)
          (swapped := swapped)
          (h_swapped_true := fun h => (h_swapped_true h).2)
          (h_swapped_false := fun h => (h_swapped_false h).2)
          (h_coarse_failure_HDyadic := h_coarse_failure_HDyadic)
          (δ₀_RKP := δ₀_RKP) (hΔ_le_RKP := hΔ_le_RKP)
          (hRKP_uniform := hRKP_uniform) (h576ε_lt := h576ε_lt)
          (hu_t := hu_t) (hu_two := hu_two)
          (hδ_le_quarter := delta_quarter_bound Δ ε δ_n hΔ_pos hΔ_lt_one' hε_pos hε_lt_one h_small_eps hδ_n_eq2)

      -- ====================================================================
      -- Step 12: hT_source_bound from Section 9 + hconfig'_subset.2
      -- ====================================================================
      have hT_source_dyadic_sub : g.T_source_dyadic ⊆ config'.T₀ := by
        intro U hU
        rcases Finset.mem_biUnion.mp hU with ⟨p, hp, hT'⟩
        have h_eq : tubeFamilyOpt config' p = config'.tubeFamily p hp :=
          tubeFamilyOpt_eq config' hp
        rw [h_eq] at hT'
        exact config'.h_subset p hp hT'

      have hT_source_card_le : (g.T_source.card : ENNReal) ≤ (config_n.T₀.card : ENNReal) := by
        have h1 : g.T_source.card ≤ g.T_source_dyadic.card := Finset.card_image_le
        have h2 : g.T_source_dyadic.card ≤ config'.T₀.card := Finset.card_le_card hT_source_dyadic_sub
        have h3 : config'.T₀ = config_n.T₀ := hconfig'_subset.2
        rw [h3] at h2
        exact_mod_cast le_trans h1 h2

      have hT₀_upper' : (config_n.T₀.card : ENNReal) ≤
          ENNReal.ofReal (Real.rpow δ_n (-ρ_T)) *
          Metric.externalCoveringNumber δ_n.toNNReal allTubes_bar := by
        have h_rhs : ENNReal.ofReal (Real.rpow δ_n (-ρ_T)) *
            Metric.externalCoveringNumber δ_n.toNNReal allTubes_bar =
            ENNReal.ofReal ((DiscretisedFurstenbergEstimate.dyadicDelta n) ^ (-ρ_T)) *
            Section9.Ncover δ_n allTubes_bar := by
          have h7 : Real.rpow δ_n (-ρ_T) = (DiscretisedFurstenbergEstimate.dyadicDelta n) ^ (-ρ_T) := by
            rw [h_eq_n] <;> rfl
          rw [h7] <;> rfl
        rw [h_rhs]
        exact hT₀_upper

      have hT_source_bound : (g.T_source.card : ENNReal) ≤
          ENNReal.ofReal (Real.rpow δ_n (-ρ_T)) *
          Metric.externalCoveringNumber δ_n.toNNReal allTubes_bar :=
        le_trans hT_source_card_le hT₀_upper'

      -- ====================================================================
      -- Step 13: Construct hT_full_upper at the fixed g.T_source
      -- ====================================================================
      have hT_full_upper : ∀ (a4 : A4_Output_v2 Δ δ_n s u ε g.T_source),
          (a5FullFineFamily Δ δ_n s u ε a4.Qset a4.perSquare).card ≤
          Real.rpow Δ (-(4 * s + 3 * ε)) := by
        intro a4
        have hTbar_sub_allTubes : allTubes_bar ⊆ allTubes := by
          intro T hT
          rcases Set.mem_iUnion₂.mp hT with ⟨p, hp, hT'⟩
          exact Set.mem_iUnion₂.mpr ⟨p, hPbar_subset hp, hT'⟩
        have hρ_T_le_20 : ρ_T ≤ ε / 20 := by
          have h1 : ρ_mass + ρ_M + ρ_T ≤ reserved_budget := hρ_sum
          have h2 : reserved_budget = ε / 20 := by rfl
          have h3 : ρ_T ≤ ρ_mass + ρ_M + ρ_T := by linarith
          rw [h2] at h1; linarith
        have hεA_le_50 : εA ≤ ε / 50 := by rfl
        have h_num_u : AssemblyNumericalBounds Δ s u ε := h_uniform_num u hu_t hu_two
        exact TFullUpperBound.t_full_upper_bound
          hΔ_pos hδ_n_pos hδ_pos hδ_n_eq2 hδ_le_δ_n' hδ_n_le_4δ'
          hεA_pos hεA_le_50 hρ_T_nonneg hρ_T_le_20 hs_pos h_num_u
          allTubes_bar allTubes hTbar_sub_allTubes h_fine hT_source_bound a4

      -- ====================================================================
      -- Step 14: Construct h_2s_bound (using hsu : s < u)
      -- ====================================================================
      have h_2s_bound : ∀ (a4 : A4_Output_v2 Δ δ_n s u ε g.T_source)
          (C_global_A2 : Finset AppendixA.CoarseTube),
          (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset),
            (a4.perSquare Q hQ).C_Q_pi ⊆ C_global_A2) →
          (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset),
            ‖Lagoon.squareCenter Δ Q‖ ≤ 2) →
          (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset)
            (R : AppendixA.CoarseSquare Δ) (hR : R ∈ a4.Qset),
            dist (Lagoon.squareCenter Δ Q) (Lagoon.squareCenter Δ R) ≤ 3) →
          (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-u - ε) →
          TwoSBoundWithLower Δ s u ε a4.Qset
            (fun Q hQ => (a4.perSquare Q hQ).C_Q_pi) C_global_A2
            (-2 * s + 210 * ε) := by
        intro a4 C_global_A2 hC_Q_pi_sub hCenter_bound hDist_le_3 hQset_card_upper
        have h_num_u2 : AssemblyNumericalBounds Δ s u ε := g.h_num_u
        have hRKP_cond_u : 576 * ε < u - s := g.hRKP_cond_u
        exact AppendixA5.h_2s_bound_from_a4_num
          hΔ_pos hΔ_lt_half' hδ_n_pos hδ_le_D
          hs_pos hs_lt_one hsu h_run_lt_two hε_pos
          a4 C_global_A2 hC_Q_pi_sub hCenter_bound hDist_le_3 hQset_card_upper
          hRKP_cond_u h_num_u2

      -- ====================================================================
      -- Step 15: h_points_in_ball' for front_H
      -- ====================================================================
      have h_points_in_ball' : ∀ Q hQ, (g.a1.points Q hQ : Set EuclideanPlane) ⊆
          Metric.closedBall 0 (1 + Real.sqrt 2 * δ_n / 2) := by
        intro Q hQ
        have h1 : (g.a1.points Q hQ : Set EuclideanPlane) ⊆
            (config'.P₀.image (CoordinatePartition.swapCoords ∘ localSquareCenter) : Set EuclideanPlane) :=
          AppendixA.NiceConfigToA1.niceConfig_to_a1_output_points_subset
            (hnm := hnm) (b1 := b1)
            hΔ_eq' h_eq_n
            hΔ_pos hΔ_lt_half' hδ_n_pos
            hu_pos h_run_lt_two hs_pos hs_lt_one hε_pos h_small Q hQ
        have h2 : (config'.P₀.image (CoordinatePartition.swapCoords ∘ localSquareCenter) : Set EuclideanPlane) ⊆
            (config_n.P₀.image (CoordinatePartition.swapCoords ∘ localSquareCenter) : Set EuclideanPlane) :=
          Finset.image_mono (CoordinatePartition.swapCoords ∘ localSquareCenter) hconfig'_subset.1
        exact Set.Subset.trans (Set.Subset.trans h1 h2) h_points_in_ball_R

      -- ====================================================================
      -- Step 16: Call front_H → HOutput
      -- ====================================================================
      let h : HOutput g := front_H g h12ε h_points_in_ball'

      -- ====================================================================
      -- Step 17: Call final_contradiction_I → False
      -- ====================================================================
      exact final_contradiction_I
        g h
        hΔ_eq' h_eq_n hΔ_lt_third'
        ht_pos ht_lt_two hst hu_t
        hT_full_upper h_2s_bound
        h_pack_absorb_A7
        η_axiom δ₀_axiom hη_axiom_pos hδ₀_axiom_pos hΔ_le_δ₀_axiom
        h_absorb_Y h_absorb_X h_absorb_T
        hA7
        η_upper hη_upper_pos h214ε_lt hΔ_small_allFine hη_upper_lt
        h_log_absorb

end DirecretisedFurstenbergEstimate.FrontEndLemmas.FrontEndComposition
