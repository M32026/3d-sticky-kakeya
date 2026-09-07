module

/-
  Parameter Selection and Numerical Hypothesis Discharge.

  Chooses ε, A, η_axiom, δ₀_axiom, η_upper and proves all "easy" numerical
  hypotheses of `uniform_appendix_A_alternative` from Δ sufficiently small.

  ## Parameter choices
  - τ = min(t-s, 1)
  - η_axiom, δ₀_axiom from `productProp_bounded s τ`
  - ε = min(s/13, (t-s)/505, η_axiom/20000) / 2
  - η_upper = 215 * ε
  - A from `qttc_typed_parentCell` (typed parent-cell QTTC adapter)

  ## Numerical hypotheses discharged
  - A2_Smallness (polylog + constant absorption)
  - AssemblyNumericalBounds (via assembly_numerical_hypotheses)
  - Energy absorption
  - A11 absorption (Y, X, T)
  - K_pack ≤ Δ^{-ε}
  - Scale constraints (Δ < 1/2, 1/3, 1/16, etc.)

  Whiteprint node: improved_incidence_general / parameter_selection
  Dependencies: AssemblyNumericalHypotheses, ProductPropBounded, RKPBridge,
                QTTC_Assembly, SlopeBoundFromStrip
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AssemblyNumericalHypotheses
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBounded
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.UniformRKP
public import MyLeanRepo.DiscretisedFurstenbergEstimate.QTTC_Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_TypedQTTC_Adapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.UniformAppendixAAlternative
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 500000

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AssemblyNumerical
open DirecretisedFurstenbergEstimate.ProductContradiction
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.QTTC_Assembly
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate (DyadicTube)

/-! ### Helper: polylog absorption for real exponents -/

/-- Absorb `C * (log(2/Δ))^A ≤ Δ^{-α}` for real A ≥ 0, using
    `polylog_absorb_delta` with `n = Nat.ceil A`. -/
lemma polylog_absorb_delta_real (C α A : ℝ) (hC : 0 < C) (hα : 0 < α) (hA : 0 ≤ A) :
    ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ, 0 < Δ → Δ < Δ₀ →
      C * Real.rpow (Real.log (2 / Δ)) A ≤ Real.rpow Δ (-α) := by
  let n : ℕ := Nat.ceil A
  have hA_le_n : A ≤ (n : ℝ) := Nat.le_ceil A
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  rcases polylog_absorb_delta C α n hC hα with ⟨Δ1, hΔ1_pos, hΔ1⟩
  -- Threshold for log(2/Δ) ≥ 1: Δ ≤ 2/e
  let Δ2 : ℝ := 2 * Real.exp (-1)
  have hΔ2_pos : 0 < Δ2 := by positivity
  let Δ₀ := min Δ1 Δ2
  have hΔ₀_pos : 0 < Δ₀ := lt_min hΔ1_pos hΔ2_pos
  use Δ₀, hΔ₀_pos
  intro Δ hΔ_pos hΔ_lt
  have h_lt1 : Δ < Δ1 := lt_of_lt_of_le hΔ_lt (min_le_left _ _)
  have h_lt2 : Δ < Δ2 := lt_of_lt_of_le hΔ_lt (min_le_right _ _)
  have h_log_ge_one : 1 ≤ Real.log (2 / Δ) := by
    have h1 : 2 / Δ > Real.exp 1 := by
      have h2 : Δ < 2 * Real.exp (-1) := h_lt2
      have h3 : 2 / Δ > 2 / (2 * Real.exp (-1)) := by gcongr
      have h4 : 2 / (2 * Real.exp (-1)) = Real.exp 1 := by
        have h41 : 2 / (2 * Real.exp (-1)) = (Real.exp (-1))⁻¹ := by field_simp
        rw [h41]
        have h42 : (Real.exp (-1))⁻¹ = Real.exp 1 := by
          rw [Real.exp_neg] <;> field_simp
        exact h42
      rw [h4] at h3; exact h3
    have h5 : Real.log (2 / Δ) > Real.log (Real.exp 1) := Real.log_lt_log (by positivity) h1
    have h6 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    rw [h6] at h5; exact le_of_lt h5
  have h_log_le : Real.log (2 / Δ) ≤ Real.log (1 / Δ) + 1 := by
    have h1 : Real.log (2 / Δ) = Real.log 2 + Real.log (1 / Δ) := by
      rw [show (2 / Δ) = 2 * (1 / Δ) by ring]
      rw [Real.log_mul (by norm_num) (by positivity)]
    rw [h1]
    have h2 : Real.log 2 ≤ 1 := by
      have h3 : Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) (by linarith [Real.exp_one_gt_d9])
      have h4 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      rw [h4] at h3; linarith
    linarith
  have h7 : Real.rpow (Real.log (2 / Δ)) A ≤ (Real.log (1 / Δ) + 1) ^ n := by
    have h8 : Real.rpow (Real.log (2 / Δ)) A ≤ Real.rpow (Real.log (2 / Δ)) n :=
      Real.rpow_le_rpow_of_exponent_le h_log_ge_one hA_le_n
    have h9 : Real.rpow (Real.log (2 / Δ)) n ≤ (Real.log (1 / Δ) + 1) ^ n := by
      have h91 : Real.rpow (Real.log (2 / Δ)) n = (Real.log (2 / Δ)) ^ n := by
        simp [Real.rpow_natCast]
      rw [h91]
      have h92 : 0 ≤ Real.log (2 / Δ) := by linarith
      have h93 : 0 ≤ Real.log (1 / Δ) + 1 := by linarith [h_log_ge_one, h_log_le]
      gcongr <;> linarith
    exact le_trans h8 h9
  have h10 : C * Real.rpow (Real.log (2 / Δ)) A ≤ C * (Real.log (1 / Δ) + 1) ^ n := by
    gcongr
  exact le_trans h10 (hΔ1 Δ hΔ_pos h_lt1)

/-! ### A2_Smallness from configuration bounds -/

/-- Prove A2_Smallness from B1 configuration bounds and Δ sufficiently small.

    Inputs:
    - K_pack ≤ Δ^{-2ε}/6
    - M/2 ≥ Δ^{-2s+2ε}
    - M ≤ Δ^{-2s-ε}
    - δ = Δ²

    Additional absorption hypotheses (provided by caller for small Δ):
    - hpack_absorb2: packing_constant + 1 ≤ Δ^{-2ε}/6
    - hM_large_absorb: 2 * K_pack ≤ Δ^{-2s+2ε}
    - hcover_lower_pack: 2000 * affinePackingM ≤ Δ^{-14ε}
-/
lemma a2_smallness_from_bounds
    {Δ δ s t ε A M : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ) (hδ_eq2 : δ = Δ ^ 2)
    (hs_pos : 0 < s) (h12ε : 12 * ε ≤ s)
    (hε_pos : 0 < ε)
    (hA_pos : 0 < A)
    (hM_lower : M / 2 ≥ Real.rpow Δ (-2 * s + 2 * ε))
    (hM_upper : M ≤ Real.rpow Δ (-2 * s - ε))
    (hpack_ge1 : 1 ≤ (MainAppendix.affineLine_packing_constant : ℝ))
    -- Thresholds (provided by caller from combined Δ₀)
    (hK_loss : 6 * A * Real.rpow (Real.log (2 / Δ)) A ≤ Real.rpow Δ (-ε))
    (hK_loss_strong : 6 * A * Real.rpow (Real.log (2 / Δ)) A ≤ Real.rpow Δ (-2 * ε))
    (hC2_loss : A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A *
        (MainAppendix.affineLine_packing_constant : ℝ)^2 *
        max 1 (((MainAppendix.affineLine_packing_constant : ℝ) + 1) * Real.rpow δ (-ε)) ≤
        Real.rpow Δ (-10 * ε))
    (hstrip_loss : (42 : ℝ) * (40 * 4 + 110) ≤ Real.rpow Δ (-5 * ε))
    (hslope_sset_const : (1680000 : ℝ) ≤ Real.rpow Δ (-15 * ε))
    (hM_upper_absorb : max 1 ((MainAppendix.affineLine_packing_constant : ℝ) *
        max 1 (((MainAppendix.affineLine_packing_constant : ℝ) + 1) * Real.rpow δ (-ε))) * M ≤
        Real.rpow Δ (-2 * s - 6 * ε))
    -- Additional absorption hypotheses
    (hpack_absorb2 : (MainAppendix.affineLine_packing_constant : ℝ) + 1 ≤ Real.rpow Δ (-2 * ε) / 6)
    (hpack_absorb3 : (MainAppendix.affineLine_packing_constant : ℝ) + 1 ≤ Real.rpow Δ (-ε) / 6)
    (hM_large_absorb : 2 * ((MainAppendix.affineLine_packing_constant : ℝ) + 1) ≤
        Real.rpow Δ (-2 * s + 2 * ε))
    (hcover_lower_pack : (2000 : ENNReal) * (AppendixA4.affinePackingM : ENNReal) ≤
        ENNReal.ofReal (Real.rpow Δ (-14 * ε))) :
    AppendixA.A2.A2_Smallness Δ δ s t ε A
      ((MainAppendix.affineLine_packing_constant : ℝ) + 1) M := by
  have hδ_le_Δ : δ ≤ Δ := by
    rw [hδ_eq2]
    have h2 : Δ < 1 := by linarith [hΔ_lt_half]
    calc Δ ^ 2 = Δ * Δ := by ring
      _ ≤ Δ * 1 := by gcongr
      _ = Δ := by ring
  have hKpack_loss : 6 * ((MainAppendix.affineLine_packing_constant : ℝ) + 1) * Real.rpow Δ (-ε) ≤
      Real.rpow Δ (-3 * ε) := by
    have h1 : 6 * ((MainAppendix.affineLine_packing_constant : ℝ) + 1) ≤ Real.rpow Δ (-2 * ε) := by
      have h2 : (MainAppendix.affineLine_packing_constant : ℝ) + 1 ≤ Real.rpow Δ (-2 * ε) / 6 := hpack_absorb2
      have h3 : 6 * ((MainAppendix.affineLine_packing_constant : ℝ) + 1) ≤ Real.rpow Δ (-2 * ε) := by
        calc
          6 * ((MainAppendix.affineLine_packing_constant : ℝ) + 1)
            ≤ 6 * (Real.rpow Δ (-2 * ε) / 6) := by gcongr
          _ = Real.rpow Δ (-2 * ε) := by ring
      exact h3
    have h4 : 6 * ((MainAppendix.affineLine_packing_constant : ℝ) + 1) * Real.rpow Δ (-ε) ≤
        Real.rpow Δ (-2 * ε) * Real.rpow Δ (-ε) := by
      have h_pos : 0 ≤ Real.rpow Δ (-ε) := (Real.rpow_pos_of_pos hΔ_pos _).le
      exact mul_le_mul_of_nonneg_right h1 h_pos
    have h5 : Real.rpow Δ (-2 * ε) * Real.rpow Δ (-ε) = Real.rpow Δ (-3 * ε) := by
      have h6 : Real.rpow Δ ((-2 * ε) + (-ε)) = Real.rpow Δ (-2 * ε) * Real.rpow Δ (-ε) :=
        Real.rpow_add hΔ_pos (-2 * ε) (-ε)
      have h7 : (-2 * ε) + (-ε) = -3 * ε := by ring
      rw [h7] at h6
      exact h6.symm
    rw [h5] at h4
    exact h4
  have hKpack_loss_strong : 6 * ((MainAppendix.affineLine_packing_constant : ℝ) + 1) ≤
      Real.rpow Δ (-ε) := by
    have h2 : (MainAppendix.affineLine_packing_constant : ℝ) + 1 ≤ Real.rpow Δ (-ε) / 6 := hpack_absorb3
    have h3 : 6 * ((MainAppendix.affineLine_packing_constant : ℝ) + 1) ≤ Real.rpow Δ (-ε) := by
      calc
        6 * ((MainAppendix.affineLine_packing_constant : ℝ) + 1)
          ≤ 6 * (Real.rpow Δ (-ε) / 6) := by gcongr
      _ = Real.rpow Δ (-ε) := by ring
    exact h3
  let K_pack1 := (MainAppendix.affineLine_packing_constant : ℝ) + 1
  have hK_pack1_pos : 0 < K_pack1 := by
    have h1 : 0 ≤ (MainAppendix.affineLine_packing_constant : ℝ) := by linarith [hpack_ge1]
    linarith
  have hM_large : 2 ≤ Real.rpow Δ (-2 * s + 2 * ε) / K_pack1 := by
    have h2 : 2 * K_pack1 ≤ Real.rpow Δ (-2 * s + 2 * ε) := hM_large_absorb
    calc
      2 = (2 * K_pack1) / K_pack1 := by field_simp [hK_pack1_pos.ne'] <;> ring
      _ ≤ (Real.rpow Δ (-2 * s + 2 * ε)) / K_pack1 := by gcongr
  exact {
    hΔ_pos := hΔ_pos
    hΔ_lt_half := by linarith
    hδ_le_Δ := hδ_le_Δ
    hA_pos := hA_pos
    hK_loss := hK_loss
    hK_loss_strong := hK_loss_strong
    hC2_loss := hC2_loss
    hstrip_loss := hstrip_loss
    hKpack_loss := hKpack_loss
    hKpack_loss_strong := hKpack_loss_strong
    hM_large := hM_large
    hM_upper := hM_upper_absorb
    hKpack_const_ge1 := hpack_ge1
    hslope_sset_const := hslope_sset_const
    hcover_lower_pack := hcover_lower_pack
  }

/-! ### Extracted return types (to avoid whnf timeout) -/

/-- The QTTC ∀-statement returned by `parameter_selection`.
    Matches the output type of `qttc_typed_parentCell` exactly, including
    the `sp` witness field for exact-parent provenance. -/
def ParameterSelectionQTTC (s A : ℝ) : Prop :=
  ∀ {n m : ℕ} {δ Δ C₁ : ℝ} {M : ℕ}
    {P : Finset (EuclideanSpace ℝ (Fin 2))} {T : (EuclideanSpace ℝ (Fin 2)) → Finset AffineLine},
    (hδ_eq : δ = dyadicDelta n) →
    (hΔ_eq : Δ = dyadicDelta m) →
    (hnm : m ≤ n) → (hm_pos : 1 ≤ m) →
    1 ≤ C₁ → P.Nonempty → 0 < M →
    (∀ p ∈ P, M / 2 < (T p).card ∧ (T p).card ≤ M) →
    (∀ p ∈ P, _root_.BallGrowth δ s C₁ (T p)) →
    (∀ p ∈ P, SeparatedAt (δ / 2) ((T p) : Set AffineLine)) →
    (∀ p ∈ P, ∀ ℓ ∈ T p,
      (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3) →
    (R : ℝ) →
    (hR : R ≤ Real.sqrt 2) →
    (∀ p ∈ P, |p 1| ≤ R) →
    (hδ_le_quarter_Delta : δ ≤ Δ / 4) →
    (∀ p ∈ P, ∀ ℓ ∈ T p, p ∈ Metric.cthickening (2 * δ) ℓ.1) →
    ∃ (P' : Finset (EuclideanSpace ℝ (Fin 2))) (T' : (EuclideanSpace ℝ (Fin 2)) → Finset AffineLine)
      (C' : Finset AffineLine) (K C₂ : ℝ) (H : ℕ),
      1 ≤ K ∧ K ≤ A * Real.rpow (Real.log (2 / Δ)) A ∧
      1 ≤ C₂ ∧ 0 < H ∧
      P' ⊆ P ∧
      (P.card : ℝ) ≤ K * (P'.card : ℝ) ∧
      (∀ p ∈ P', T' p ⊆ T p) ∧
      (∀ p ∈ P', (M : ℝ) ≤ K * ((T' p).card : ℝ)) ∧
      _root_.IsFiniteDeltaSSet Δ s C₂ C' ∧
      IsDeltaSSet Δ s (max 1 (QTTC_Assembly.C_PACK * C₂)) (C' : Set AffineLine) ∧
      C₂ ≤ A * Real.rpow K A * C₁ ∧
      (∀ c ∈ C', |tubeSlope c| ≤ 1) ∧
      (∀ c ∈ C', (LemmaE.getDirV c) 1 ≠ 0) ∧
      (∀ c ∈ C', |tubeIntercept c| ≤ 3) ∧
      (∀ c ∈ C', ∃ p ∈ P', |tubeIntercept c - (p 0 - tubeSlope c * p 1)| ≤ 4 * Δ) ∧
      -- Exact-parent provenance via composite:
      -- ell → snapTube n ell → sp hnm → dyadicTubeToA2 = c
      (∀ c ∈ C', ∃ (p : AppendixA.Plane) (hp : p ∈ P') (ell : AffineLine)
        (hell : ell ∈ T' p) (U : DyadicTube m),
        TypedQTTC_Assembly.sp hnm (A2DyadicAdapter.snapTube n ell) = U ∧
        c = A2DyadicAdapter.dyadicTubeToA2 U) ∧
      (∀ (hΔ_pos : 0 < Δ), ∀ c ∈ C',
        (H : ℝ) ≤ ∑ p ∈ P', (pointFiber Δ hΔ_pos T' p c).card) ∧
      (∀ (hΔ_pos : 0 < Δ), ∀ p ∈ P', ∀ c ∈ C',
        (pointFiber Δ hΔ_pos T' p c).card ≤
          C₁ * A2TypedQTTCAdapter.GEOM_CONST s * (T p).card * Δ^s) ∧
      (M : ℝ) * (P.card : ℝ) ≤ K * (H : ℝ) * (C'.card : ℝ) ∧
      (H : ℝ) * (C'.card : ℝ) ≤ K * (M : ℝ) * (P.card : ℝ)

/-- The big numerical-hypotheses conjunction returned by `parameter_selection`.
    Extracted to keep the theorem return type small enough for whnf. -/
def ParameterSelectionNumericalHypotheses
    (s t ε η_upper η_axiom δ₀_axiom A δ₀ : ℝ) : Prop :=
  ∀ (Δ δ K_pack M : ℝ),
    0 < Δ → Δ < δ₀ → 0 < δ → δ = Δ^2 →
    0 < K_pack → K_pack ≤ Real.rpow Δ (-2 * ε) / 6 →
    0 < M → M / 2 ≥ Real.rpow Δ (-2 * s + 2 * ε) →
    M ≤ Real.rpow Δ (-2 * s - ε) →
    AppendixA.A2.A2_Smallness Δ δ s t ε A
      ((MainAppendix.affineLine_packing_constant : ℝ) + 1) M ∧
    AssemblyNumericalBounds Δ s t ε ∧
    (∀ (u : ℝ), t ≤ u → u ≤ 2 → AssemblyNumericalBounds Δ s u ε) ∧
    (2000 : ℝ) * 2 < Real.rpow Δ (-(η_upper - 214 * ε)) ∧
    (MainAppendix.affineLine_packing_constant : ℝ) + 1 ≤ Real.rpow Δ (-ε) ∧
    (MainAppendix.plane_energy_constant s t 2) * (MainAppendix.plane_packing_constant : ℝ) ≤
      Real.rpow Δ (-ε) ∧
    (9 * 3 ^ (t - s)) * Real.rpow Δ (-10000 * ε) ≤ Real.rpow Δ (-η_axiom) ∧
    (729 * 50 ^ s) * Real.rpow Δ (-600 * ε) ≤ Real.rpow Δ (-η_axiom) ∧
    (81 ^ 3 * 16 * 50 ^ s) * Real.rpow Δ (-600 * ε) ≤ Real.rpow Δ (-η_axiom) ∧
    Δ ≤ δ₀_axiom ∧
    Δ < 1 / 2 ∧ Δ < 1 / 3 ∧ Δ < 1 / 16 ∧ Δ < 1 ∧
    Real.rpow Δ (ε / 4) ≤ 1 / 100 ∧
    ((MainAppendix.plane_packing_constant : ℝ)^2 *
      (16 + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - t))) ≤ Real.rpow Δ (-ε)) ∧
    ((9 : ℝ) * (3 : ℝ)^(2 - s) ≤ Real.rpow Δ (-(η_axiom - 10000 * ε))) ∧
    (∀ (u : ℝ), t ≤ u → u ≤ 2 →
      (9 : ℝ) * (3 : ℝ)^(u - s) ≤ (9 : ℝ) * (3 : ℝ)^(2 - s)) ∧
    (∀ (u : ℝ), t ≤ u → u ≤ 2 →
      MainAppendix.plane_energy_constant s u 2 ≤
        (MainAppendix.plane_packing_constant : ℝ) *
          (16 + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - t)))) ∧
    (∀ (u : ℝ), t ≤ u → u ≤ 2 → (4 : ℝ)^u ≤ 16) ∧
    (∀ (u : ℝ), t ≤ u → u ≤ 2 →
      MainAppendix.plane_energy_constant s u 2 * (MainAppendix.plane_packing_constant : ℝ) ≤
        Real.rpow Δ (-ε)) ∧
    (∀ (u : ℝ), t ≤ u → u ≤ 2 →
      ((9 : ℝ) * (3 : ℝ)^(u - s)) * Real.rpow Δ (-10000 * ε) ≤
        Real.rpow Δ (-η_axiom))

attribute [irreducible] ParameterSelectionQTTC ParameterSelectionNumericalHypotheses

/-! ### Main parameter selection theorem -/

/-- Choose all numerical parameters and produce a threshold δ₀ such that all
    easy hypotheses of `uniform_appendix_A_alternative` hold for Δ < δ₀.

    Returns:
    - ε, A, η_axiom, δ₀_axiom, η_upper, δ₀
    - Parameter inequality proofs
    - hA7 (product axiom application)
    - hQTTC (with chosen A)
    - RKP bridge data
    - A function that, given Δ < δ₀ and B1 bounds, produces A2_Smallness,
      AssemblyNumericalBounds, energy absorption, A11 absorption, etc.
-/
theorem parameter_selection
    (s t : ℝ)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (ht_pos : 0 < t) (ht_lt_two : t < 2) (hst : s < t) :
    ∃ (ε A η_axiom δ₀_axiom η_upper δ₀ : ℝ),
      0 < ε ∧ 12 * ε ≤ s ∧ 576 * ε < t - s ∧ ε < 1 ∧ ε ≤ 1 ∧
      0 < A ∧ 1 ≤ A ∧
      0 < η_axiom ∧ 0 < δ₀_axiom ∧
      0 < η_upper ∧ 214 * ε < η_upper ∧ η_upper < η_axiom ∧
      0 < δ₀ ∧
      -- Product axiom application (single τ₀ = min(t-s,1))
      ProductPropBoundedTheorem s (min (t - s) 1) η_axiom δ₀_axiom ∧
      -- QTTC with this A (typed parent-cell version with pointFiber bounds)
      ParameterSelectionQTTC s A ∧
      -- Uniform RKP threshold and function (works for all u ∈ [t,2])
      (∃ (δ₀_RKP : ℝ), 0 < δ₀_RKP ∧ δ₀_RKP ≤ 1 ∧
        ∀ (u : ℝ), t ≤ u → u ≤ 2 → RKPAtExponent s u ε δ₀_RKP) ∧
      -- Numerical hypotheses for Δ < δ₀
      ParameterSelectionNumericalHypotheses s t ε η_upper η_axiom δ₀_axiom A δ₀ := by
  let τ₀ : ℝ := min (t - s) 1
  have hτ₀_pos : 0 < τ₀ := by
    have h1 : 0 < t - s := by linarith
    exact lt_min h1 (by norm_num)
  have hτ₀_le_one : τ₀ ≤ 1 := min_le_right _ _
  have hτ₀_le_ts : τ₀ ≤ t - s := min_le_left _ _
  rcases productProp_bounded s τ₀ hs_pos hs_lt_one hτ₀_pos with
    ⟨η_axiom, hη_axiom_pos, δ₀_axiom, hδ₀_axiom_pos, hA7_raw⟩
  let ε : ℝ := min (s / 13) (min ((t - s) / 505) (η_axiom / 20000)) / 2
  have hε_pos : 0 < ε := by positivity
  have hε_le_s26 : ε ≤ s / 26 := by
    have h1 : ε ≤ min (s / 13) (min ((t - s) / 505) (η_axiom / 20000)) / 2 := by rfl
    have h2 : min (s / 13) (min ((t - s) / 505) (η_axiom / 20000)) ≤ s / 13 := min_le_left _ _
    linarith
  have h12ε : 12 * ε ≤ s := by linarith
  have hε_le_ts1010 : ε ≤ (t - s) / 1010 := by
    have h1 : ε ≤ min (s / 13) (min ((t - s) / 505) (η_axiom / 20000)) / 2 := by rfl
    have h2 : min (s / 13) (min ((t - s) / 505) (η_axiom / 20000)) ≤ (t - s) / 505 := by
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have h576ε_lt_t_sub_s : 576 * ε < t - s := by
    have h : 576 * ε ≤ 576 * ((t - s) / 1010) := by gcongr
    have h2 : 576 * ((t - s) / 1010) < t - s := by
      have h3 : 0 < t - s := by linarith
      have h4 : (576 : ℝ) / 1010 < 1 := by norm_num
      have h5 : 576 * ((t - s) / 1010) = ((576 : ℝ) / 1010) * (t - s) := by ring
      rw [h5]
      simpa [one_mul] using mul_lt_mul_of_pos_right h4 h3
    exact lt_of_le_of_lt h h2
  have hε_le_η40000 : ε ≤ η_axiom / 40000 := by
    have h1 : ε ≤ min (s / 13) (min ((t - s) / 505) (η_axiom / 20000)) / 2 := by rfl
    have h2 : min (s / 13) (min ((t - s) / 505) (η_axiom / 20000)) ≤ η_axiom / 20000 := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hε_lt_one : ε < 1 := by linarith [hε_le_s26, hs_lt_one]
  have hε_le_one : ε ≤ 1 := by linarith
  let η_upper : ℝ := 215 * ε
  have hη_upper_pos : 0 < η_upper := by positivity
  have h214ε_lt : 214 * ε < η_upper := by linarith
  have hη_upper_lt : η_upper < η_axiom := by
    have h : 215 * ε ≤ 215 * (η_axiom / 40000) := by gcongr
    have h2 : 215 * (η_axiom / 40000) < η_axiom := by
      have h3 : 0 < η_axiom := hη_axiom_pos
      have h4 : (215 : ℝ) / 40000 < 1 := by norm_num
      have h5 : 215 * (η_axiom / 40000) = ((215 : ℝ) / 40000) * η_axiom := by ring
      rw [h5]
      simpa [one_mul] using mul_lt_mul_of_pos_right h4 h3
    exact lt_of_le_of_lt h h2
  have hη_diff1_pos : 0 < η_axiom - 10000 * ε := by
    have h : 10000 * ε ≤ η_axiom / 4 := by linarith [hε_le_η40000]
    linarith
  have hη_diff2_pos : 0 < η_axiom - 600 * ε := by
    have h : 600 * ε ≤ η_axiom / 4 := by linarith [hε_le_η40000]
    linarith
  rcases A2TypedQTTCAdapter.qttc_typed_parentCell s hs_pos (by linarith) with ⟨A, hA_one, hQTTC_typed⟩
  have hA_pos : 0 < A := by linarith
  rcases uniform_rkp_wrapper s t ε hs_pos hs_lt_one hst (by linarith) hε_pos h576ε_lt_t_sub_s with
    ⟨δ₀_RKP, hδ₀_RKP_pos, hRKP_uniform⟩
  have hRKP_t : RKPAtExponent s t ε δ₀_RKP := hRKP_uniform t (by linarith) (by linarith)
  have hδ₀_RKP_le_one : δ₀_RKP ≤ 1 := hRKP_t.2.1
  rcases assembly_numerical_hypotheses s t ε hs_pos hs_lt_one hst ht_lt_two hε_pos h12ε h576ε_lt_t_sub_s with
    ⟨Δ₀_assembly, hΔ₀_assembly_pos, hAssembly⟩
  set C_pack : ℝ := (MainAppendix.affineLine_packing_constant : ℝ) with hC_pack_def
  have hC_pack_pos : 0 < C_pack := by
    simp [hC_pack_def, MainAppendix.affineLine_packing_constant_pos] <;> positivity
  have hC_pack_ge1 : 1 ≤ C_pack := by
    have h : 1 ≤ MainAppendix.affineLine_packing_constant := Nat.succ_le_iff.mpr MainAppendix.affineLine_packing_constant_pos
    have h' : (1 : ℝ) ≤ (MainAppendix.affineLine_packing_constant : ℝ) := by exact_mod_cast h
    simpa [hC_pack_def] using h'
  set C_packM : ℝ := (AppendixA4.affinePackingM : ℝ) with hC_packM_def
  have hC_packM_pos : 0 < C_packM := by
    simp [hC_packM_def, AppendixA4.affinePackingM] <;> norm_num
  set C_energy : ℝ := (MainAppendix.plane_energy_constant s t 2) * (MainAppendix.plane_packing_constant : ℝ) with hC_energy_def
  have hC_energy_pos : 0 < C_energy := by
    have hpack_pos : 0 < (MainAppendix.plane_packing_constant : ℝ) := by
      exact_mod_cast MainAppendix.plane_packing_constant_pos
    have hratio_lt_one : (2 : ℝ) ^ (s - t) < 1 := by
      have h5 : s - t < 0 := by linarith
      have h6 : (2 : ℝ) ^ (s - t) < (2 : ℝ) ^ (0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h5
      simpa using h6
    have hdenom_pos : 0 < (1 : ℝ) - (2 : ℝ) ^ (s - t) := by linarith
    have h4t_pos : 0 < (2 * (2 : ℝ)) ^ t := by positivity
    have h2s_pos : 0 < (2 : ℝ) ^ s := by positivity
    have hsum_pos : 0 < (2 * (2 : ℝ)) ^ t + (2 : ℝ) ^ s / (1 - (2 : ℝ) ^ (s - t)) := by positivity
    have henergy_pos : 0 < MainAppendix.plane_energy_constant s t 2 := by
      simpa [MainAppendix.plane_energy_constant] using mul_pos hpack_pos hsum_pos
    have h : 0 < MainAppendix.plane_energy_constant s t 2 * (MainAppendix.plane_packing_constant : ℝ) := mul_pos henergy_pos hpack_pos
    simpa [hC_energy_def] using h
  set C_Y : ℝ := 9 * 3 ^ (t - s) with hC_Y_def
  have hC_Y_pos : 0 < C_Y := by positivity
  set C_X : ℝ := 729 * 50 ^ s with hC_X_def
  have hC_X_pos : 0 < C_X := by positivity
  set C_T : ℝ := 81 ^ 3 * 16 * 50 ^ s with hC_T_def
  have hC_T_pos : 0 < C_T := by positivity
  -- Uniform worst-case constants for u ∈ [t, 2]
  set C_Y_uniform : ℝ := 9 * (3 : ℝ)^(2 - s) with hC_Y_uniform_def
  have hC_Y_uniform_pos : 0 < C_Y_uniform := by positivity
  set C_energy_uniform : ℝ :=
    (MainAppendix.plane_packing_constant : ℝ) *
      (16 + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - t))) with hC_energy_uniform_def
  have hC_energy_uniform_pos : 0 < C_energy_uniform := by
    have h1 : 0 < (MainAppendix.plane_packing_constant : ℝ) := by exact_mod_cast MainAppendix.plane_packing_constant_pos
    have h2 : 0 < (2 : ℝ)^(s - t) := by positivity
    have h3 : (2 : ℝ)^(s - t) < 1 := by
      have h4 : s - t < 0 := by linarith
      have h5 : (2 : ℝ)^(s - t) < (2 : ℝ)^(0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h4
      norm_num at h5 ⊢ <;> exact h5
    have h6 : 0 < 1 - (2 : ℝ)^(s - t) := by linarith
    positivity
  set C_energy_uniform_absorb : ℝ :=
    C_energy_uniform * (MainAppendix.plane_packing_constant : ℝ) with hC_energy_uniform_absorb_def
  have hC_energy_uniform_absorb_pos : 0 < C_energy_uniform_absorb := by
    have h1 : 0 < (MainAppendix.plane_packing_constant : ℝ) := by exact_mod_cast MainAppendix.plane_packing_constant_pos
    exact mul_pos hC_energy_uniform_pos h1
  set C_strip : ℝ := (42 : ℝ) * (40 * 4 + 110) with hC_strip_def
  have hC_strip_pos : 0 < C_strip := by norm_num
  set C_slope : ℝ := (1680000 : ℝ) with hC_slope_def
  have hC_slope_pos : 0 < C_slope := by norm_num
  set C_C2 : ℝ := Real.rpow A (A + 1) * C_pack ^ 2 with hC_C2_def
  have hC_C2_pos : 0 < C_C2 := by
    have h1 : 0 < Real.rpow A (A + 1) := Real.rpow_pos_of_pos hA_pos _
    have h2 : 0 < C_pack ^ 2 := by positivity
    have h3 : 0 < Real.rpow A (A + 1) * C_pack ^ 2 := mul_pos h1 h2
    simpa [hC_C2_def] using h3
  rcases polylog_absorb_delta_real (6 * A) ε A (by positivity) hε_pos hA_pos.le with ⟨d1, hd1_pos, hd1⟩
  rcases polylog_absorb_delta_real (6 * A) (2 * ε) A (by positivity) (by positivity) hA_pos.le with ⟨d2, hd2_pos, hd2⟩
  rcases polylog_absorb_delta_real C_C2 (6 * ε) (A ^ 2) hC_C2_pos (by positivity) (by positivity) with ⟨d3, hd3_pos, hd3⟩
  rcases const_absorb_delta C_strip (5 * ε) hC_strip_pos (by positivity) with ⟨d4, hd4_pos, hd4⟩
  rcases const_absorb_delta C_slope (15 * ε) hC_slope_pos (by positivity) with ⟨d5, hd5_pos, hd5⟩
  rcases const_absorb_delta (6 * (C_pack + 1)) (2 * ε) (by positivity) (by positivity) with ⟨d6, hd6_pos, hd6⟩
  rcases const_absorb_delta (2000 * C_packM) (14 * ε) (by positivity) (by positivity) with ⟨d7, hd7_pos, hd7⟩
  rcases const_absorb_delta C_pack ε hC_pack_pos hε_pos with ⟨d8, hd8_pos, hd8⟩
  rcases const_absorb_delta (6 : ℝ) (4 * ε) (by norm_num) (by positivity) with ⟨d9, hd9_pos, hd9⟩
  rcases const_absorb_delta (C_pack + 1) ε (by positivity) hε_pos with ⟨d10, hd10_pos, hd10⟩
  rcases const_absorb_delta C_energy ε hC_energy_pos hε_pos with ⟨d11, hd11_pos, hd11⟩
  rcases const_absorb_delta C_Y (η_axiom - 10000 * ε) hC_Y_pos hη_diff1_pos with ⟨d12, hd12_pos, hd12⟩
  rcases const_absorb_delta C_X (η_axiom - 600 * ε) hC_X_pos hη_diff2_pos with ⟨d13, hd13_pos, hd13⟩
  rcases const_absorb_delta C_T (η_axiom - 600 * ε) hC_T_pos hη_diff2_pos with ⟨d14, hd14_pos, hd14⟩
  set d15 : ℝ := (1 / 100 : ℝ) ^ (4 / ε) with hd15_def
  have hd15_pos : 0 < d15 := by positivity
  rcases const_absorb_delta (6 * (C_pack + 1)) ε (by positivity) hε_pos with ⟨d16, hd16_pos, hd16⟩
  rcases const_absorb_delta (68 : ℝ) (4 * ε) (by norm_num) (by positivity) with ⟨d17, hd17_pos, hd17⟩
  rcases const_absorb_delta C_energy_uniform_absorb ε hC_energy_uniform_absorb_pos hε_pos with ⟨d18, hd18_pos, hd18⟩
  rcases const_absorb_delta C_Y_uniform (η_axiom - 10000 * ε) hC_Y_uniform_pos hη_diff1_pos with ⟨d19, hd19_pos, hd19⟩
  set δ₀ : ℝ := min δ₀_axiom (min δ₀_RKP (min Δ₀_assembly
    (min d1 (min d2 (min d3 (min d4 (min d5 (min d6 (min d7 (min d8 (min d9
    (min d10 (min d11 (min d12 (min d13 (min d14 (min d15 (min d16 (min d17 (min d18 d19)))))))))))))))))))) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by
    rw [hδ₀_def]
    apply lt_min
    · exact hδ₀_axiom_pos
    · apply lt_min
      · exact hδ₀_RKP_pos
      · apply lt_min
        · exact hΔ₀_assembly_pos
        · apply lt_min
          · exact hd1_pos
          · apply lt_min
            · exact hd2_pos
            · apply lt_min
              · exact hd3_pos
              · apply lt_min
                · exact hd4_pos
                · apply lt_min
                  · exact hd5_pos
                  · apply lt_min
                    · exact hd6_pos
                    · apply lt_min
                      · exact hd7_pos
                      · apply lt_min
                        · exact hd8_pos
                        · apply lt_min
                          · exact hd9_pos
                          · apply lt_min
                            · exact hd10_pos
                            · apply lt_min
                              · exact hd11_pos
                              · apply lt_min
                                · exact hd12_pos
                                · apply lt_min
                                  · exact hd13_pos
                                  · apply lt_min
                                    · exact hd14_pos
                                    · apply lt_min
                                      · exact hd15_pos
                                      · apply lt_min
                                        · exact hd16_pos
                                        · apply lt_min
                                          · exact hd17_pos
                                          · apply lt_min
                                            · exact hd18_pos
                                            · exact hd19_pos
  refine' ⟨ε, A, η_axiom, δ₀_axiom, η_upper, δ₀, _⟩
  constructor
  · exact hε_pos
  constructor
  · exact h12ε
  constructor
  · exact h576ε_lt_t_sub_s
  constructor
  · exact hε_lt_one
  constructor
  · exact hε_le_one
  constructor
  · exact hA_pos
  constructor
  · exact hA_one
  constructor
  · exact hη_axiom_pos
  constructor
  · exact hδ₀_axiom_pos
  constructor
  · exact hη_upper_pos
  constructor
  · exact h214ε_lt
  constructor
  · exact hη_upper_lt
  constructor
  · exact hδ₀_pos
  constructor
  · exact hA7_raw
  constructor
  · simp only [ParameterSelectionQTTC]
    exact hQTTC_typed
  constructor
  · exact ⟨δ₀_RKP, hδ₀_RKP_pos, hδ₀_RKP_le_one, hRKP_uniform⟩
  simp only [ParameterSelectionNumericalHypotheses]
  intro Δ δ K_pack M hΔ_pos hΔ_lt_δ₀ hδ_pos hδ_eq2 hK_pack_pos hK_pack_bound hM_pos hM_lower hM_upper
  let mr : ∀ (a b : ℝ), min a b ≤ b := fun a b => min_le_right a b
  let ml : ∀ (a b : ℝ), min a b ≤ a := fun a b => min_le_left a b
  have hδ₀_le_d1 : δ₀ ≤ d1 := by
    rw [hδ₀_def]; exact (mr _ _).trans ((mr _ _).trans ((mr _ _).trans (ml _ _)))
  have hδ₀_le_d2 : δ₀ ≤ d2 := by
    rw [hδ₀_def]; exact (mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans (ml _ _))))
  have hδ₀_le_d3 : δ₀ ≤ d3 := by
    rw [hδ₀_def]; exact (mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans (ml _ _)))))
  have hδ₀_le_d4 : δ₀ ≤ d4 := by
    rw [hδ₀_def]; exact (mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans (ml _ _))))))
  have hδ₀_le_d5 : δ₀ ≤ d5 := by
    rw [hδ₀_def]; exact (mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans (ml _ _)))))))
  have hδ₀_le_d6 : δ₀ ≤ d6 := by
    rw [hδ₀_def]; exact (mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans (ml _ _))))))))
  have hδ₀_le_d7 : δ₀ ≤ d7 := by
    rw [hδ₀_def]; exact (mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans (ml _ _)))))))))
  have hδ₀_le_d8 : δ₀ ≤ d8 := by
    rw [hδ₀_def]; exact (mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans (ml _ _))))))))))
  have hδ₀_le_d9 : δ₀ ≤ d9 := by
    rw [hδ₀_def]; exact (mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans (ml _ _)))))))))))
  have hδ₀_le_d10 : δ₀ ≤ d10 := by
    rw [hδ₀_def]; exact (mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans (ml _ _))))))))))))
  have hδ₀_le_d11 : δ₀ ≤ d11 := by
    rw [hδ₀_def]; exact (mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans (ml _ _)))))))))))))
  have hδ₀_le_d12 : δ₀ ≤ d12 := by
    rw [hδ₀_def]; exact (mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans ((mr _ _).trans (ml _ _))))))))))))))
  have hδ₀_le_d13 : δ₀ ≤ d13 := by
    rw [hδ₀_def]
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    exact min_le_left _ _
  have hδ₀_le_d14 : δ₀ ≤ d14 := by
    rw [hδ₀_def]
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    exact min_le_left _ _
  have hδ₀_le_d15 : δ₀ ≤ d15 := by
    rw [hδ₀_def]
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    exact min_le_left _ _
  have hδ₀_le_d16 : δ₀ ≤ d16 := by
    rw [hδ₀_def]
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    exact min_le_left _ _
  have hδ₀_le_d17 : δ₀ ≤ d17 := by
    rw [hδ₀_def]
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    exact min_le_left _ _
  have hδ₀_le_min1819 : δ₀ ≤ min d18 d19 := by
    rw [hδ₀_def]
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    refine' le_trans (min_le_right _ _) _
    rfl
  have hδ₀_le_d18 : δ₀ ≤ d18 := le_trans hδ₀_le_min1819 (min_le_left _ _)
  have hδ₀_le_d19 : δ₀ ≤ d19 := le_trans hδ₀_le_min1819 (min_le_right _ _)
  have hδ₀_le_axiom : δ₀ ≤ δ₀_axiom := by
    rw [hδ₀_def]; exact ml _ _
  have hδ₀_le_assembly : δ₀ ≤ Δ₀_assembly := by
    rw [hδ₀_def]; exact (mr _ _).trans ((mr _ _).trans (ml _ _))
  have hΔ_lt_d1 : Δ < d1 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d1
  have hΔ_lt_d2 : Δ < d2 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d2
  have hΔ_lt_d3 : Δ < d3 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d3
  have hΔ_lt_d4 : Δ < d4 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d4
  have hΔ_lt_d5 : Δ < d5 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d5
  have hΔ_lt_d6 : Δ < d6 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d6
  have hΔ_lt_d7 : Δ < d7 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d7
  have hΔ_lt_d8 : Δ < d8 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d8
  have hΔ_lt_d9 : Δ < d9 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d9
  have hΔ_lt_d10 : Δ < d10 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d10
  have hΔ_lt_d11 : Δ < d11 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d11
  have hΔ_lt_d12 : Δ < d12 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d12
  have hΔ_lt_d13 : Δ < d13 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d13
  have hΔ_lt_d14 : Δ < d14 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d14
  have hΔ_lt_d15 : Δ < d15 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d15
  have hΔ_lt_d16 : Δ < d16 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d16
  have hΔ_lt_d17 : Δ < d17 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d17
  have hΔ_lt_d18 : Δ < d18 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d18
  have hΔ_lt_d19 : Δ < d19 := lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_d19
  have hΔ_le_δ₀_axiom : Δ ≤ δ₀_axiom := le_trans hΔ_lt_δ₀.le hδ₀_le_axiom
  have hΔ_lt_half : Δ < 1 / 2 := by
    have h : Δ < d15 := hΔ_lt_d15
    have h2 : d15 ≤ 1 / 2 := by
      simp [hd15_def]
      have h31 : 1 ≤ 4 / ε := by
        have h32 : ε ≤ 1 := hε_lt_one.le
        have h33 : 4 / ε ≥ 4 := by
          calc 4 / ε ≥ 4 / 1 := by gcongr
          _ = 4 := by norm_num
        linarith
      have h3 : (1 / 100 : ℝ) ^ (4 / ε) ≤ (1 / 100 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) h31
      have h4 : (1 / 100 : ℝ) ^ (1 : ℝ) = 1 / 100 := by simp
      rw [h4] at h3
      linarith
    linarith
  have hδ_le_Δ : δ ≤ Δ := by
    rw [hδ_eq2]
    have h2 : Δ ≤ 1 := by linarith [hΔ_lt_half]
    calc Δ ^ 2 = Δ * Δ := by ring
      _ ≤ Δ * 1 := by gcongr
      _ = Δ := by ring
  have hK_loss : 6 * A * Real.rpow (Real.log (2 / Δ)) A ≤ Real.rpow Δ (-ε) := hd1 Δ hΔ_pos hΔ_lt_d1
  have hK_loss_strong : 6 * A * Real.rpow (Real.log (2 / Δ)) A ≤ Real.rpow Δ (-2 * ε) := by
    have h := hd2 Δ hΔ_pos hΔ_lt_d2
    have h_norm : Real.rpow Δ (-(2 * ε)) = Real.rpow Δ (-2 * ε) := by ring_nf
    rw [h_norm] at h
    exact h
  have h6_le : (6 : ℝ) ≤ Real.rpow Δ (-4 * ε) := by
    have h := hd9 Δ hΔ_pos hΔ_lt_d9
    have h_norm : Real.rpow Δ (-(4 * ε)) = Real.rpow Δ (-4 * ε) := by ring_nf
    rw [h_norm] at h
    exact h
  have hpack_absorb2 : C_pack + 1 ≤ Real.rpow Δ (-2 * ε) / 6 := by
    have h : 6 * (C_pack + 1) ≤ Real.rpow Δ (-(2 * ε)) := hd6 Δ hΔ_pos hΔ_lt_d6
    have h_norm : Real.rpow Δ (-(2 * ε)) = Real.rpow Δ (-2 * ε) := by ring_nf
    rw [h_norm] at h
    linarith
  have hKpack_delta4 : (C_pack + 1) * Real.rpow δ (-ε) ≤ Real.rpow Δ (-4 * ε) / 6 := by
    have hδ2 : δ = Δ ^ 2 := hδ_eq2
    have h1 : Real.rpow δ (-ε) = Real.rpow Δ (-2 * ε) := by
      rw [hδ2]
      have h_base : (Δ ^ 2 : ℝ) = Real.rpow Δ 2 := by
        simp [Real.rpow_two]
      rw [h_base]
      have h_mul : Real.rpow (Real.rpow Δ 2) (-ε) = Real.rpow Δ ((2 : ℝ) * (-ε)) :=
        (Real.rpow_mul hΔ_pos.le (2 : ℝ) (-ε)).symm
      have h_eq : (2 : ℝ) * (-ε) = -2 * ε := by ring
      rw [h_mul, h_eq]
    rw [h1]
    have h3 : C_pack + 1 ≤ Real.rpow Δ (-2 * ε) / 6 := hpack_absorb2
    have h_pos : 0 < Real.rpow Δ (-2 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    calc (C_pack + 1) * Real.rpow Δ (-2 * ε)
      ≤ (Real.rpow Δ (-2 * ε) / 6) * Real.rpow Δ (-2 * ε) := by gcongr
    _ = Real.rpow Δ (-4 * ε) / 6 := by
      have h5 : Real.rpow Δ (-2 * ε) * Real.rpow Δ (-2 * ε) = Real.rpow Δ (-4 * ε) := by
        have h51 : Real.rpow Δ (-2 * ε) * Real.rpow Δ (-2 * ε) = Real.rpow Δ ((-2 * ε) + (-2 * ε)) :=
          (Real.rpow_add hΔ_pos (-2 * ε) (-2 * ε)).symm
        rw [h51]
        have h52 : (-2 * ε) + (-2 * ε) = -4 * ε := by ring
        rw [h52]
      have h6 : (Real.rpow Δ (-2 * ε) / 6) * Real.rpow Δ (-2 * ε) =
          (Real.rpow Δ (-2 * ε) * Real.rpow Δ (-2 * ε)) / 6 := by ring
      rw [h6, h5] <;> ring
  have hmax1 : max 1 ((C_pack + 1) * Real.rpow δ (-ε)) ≤ Real.rpow Δ (-4 * ε) := by
    have h4 : (C_pack + 1) * Real.rpow δ (-ε) ≤ Real.rpow Δ (-4 * ε) / 6 := hKpack_delta4
    have h5 : Real.rpow Δ (-4 * ε) / 6 ≤ Real.rpow Δ (-4 * ε) := by
      have h6 : 0 < Real.rpow Δ (-4 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h7 : Real.rpow Δ (-4 * ε) / 6 ≤ Real.rpow Δ (-4 * ε) := by
        apply div_le_self
        · exact h6.le
        · norm_num
      exact h7
    have h7 : (C_pack + 1) * Real.rpow δ (-ε) ≤ Real.rpow Δ (-4 * ε) := le_trans h4 h5
    have h8 : (1 : ℝ) ≤ Real.rpow Δ (-4 * ε) := by
      have h9 : (6 : ℝ) ≤ Real.rpow Δ (-4 * ε) := h6_le
      linarith
    exact max_le h8 h7
  have hC2_poly : Real.rpow A (A + 1) * C_pack ^ 2 * Real.rpow (Real.log (2 / Δ)) (A ^ 2) ≤
      Real.rpow Δ (-6 * ε) := by
    have h := hd3 Δ hΔ_pos hΔ_lt_d3
    have h_norm : Real.rpow Δ (-(6 * ε)) = Real.rpow Δ (-6 * ε) := by ring_nf
    rw [h_norm] at h
    have hC2 : C_C2 = Real.rpow A (A + 1) * C_pack ^ 2 := by
      simp [hC_C2_def] <;> ring
    rw [hC2] at h
    exact h
  have hC2_loss : A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A *
      C_pack ^ 2 * max 1 ((C_pack + 1) * Real.rpow δ (-ε)) ≤ Real.rpow Δ (-10 * ε) := by
    have h21 : 0 ≤ A := hA_pos.le
    have h221 : 1 < 2 / Δ := by
      rw [one_lt_div hΔ_pos] <;> linarith [hΔ_lt_half]
    have h22 : 0 ≤ Real.log (2 / Δ) := (Real.log_pos h221).le
    have h23 : 0 ≤ Real.rpow (Real.log (2 / Δ)) A := Real.rpow_nonneg h22 _
    have h1 : A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A =
        Real.rpow A (A + 1) * Real.rpow (Real.log (2 / Δ)) (A ^ 2) := by
      have h24 : Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A =
          Real.rpow A A * Real.rpow (Real.log (2 / Δ)) (A ^ 2) := by
        have h25 : Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A =
            (A * Real.rpow (Real.log (2 / Δ)) A) ^ A := rfl
        rw [h25]
        have h26 : (A * Real.rpow (Real.log (2 / Δ)) A) ^ A =
            A ^ A * (Real.rpow (Real.log (2 / Δ)) A) ^ A := by
          rw [Real.mul_rpow h21 h23]
        rw [h26]
        have h27 : (Real.rpow (Real.log (2 / Δ)) A) ^ A = Real.rpow (Real.log (2 / Δ)) (A * A) :=
          (Real.rpow_mul h22 A A).symm
        rw [h27]
        have h28 : A * A = A ^ 2 := by ring
        rw [h28] <;> rfl
      rw [h24]
      have h29 : Real.rpow A (A + 1) = Real.rpow A A * A := by
        have h_add : Real.rpow A (A + 1) = Real.rpow A A * Real.rpow A (1 : ℝ) :=
          Real.rpow_add hA_pos A (1 : ℝ)
        have h_one : Real.rpow A (1 : ℝ) = A := Real.rpow_one A
        rw [h_add, h_one] <;> ring
      rw [h29] <;> ring
    have hX_pos : 0 ≤ Real.rpow A (A + 1) * C_pack ^ 2 * Real.rpow (Real.log (2 / Δ)) (A ^ 2) := by
      have h1 : 0 ≤ Real.rpow A (A + 1) := Real.rpow_nonneg hA_pos.le _
      have h2 : 0 ≤ C_pack ^ 2 := by positivity
      have h3 : 0 ≤ Real.rpow (Real.log (2 / Δ)) (A ^ 2) := Real.rpow_nonneg h22 _
      exact mul_nonneg (mul_nonneg h1 h2) h3
    calc A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A * C_pack ^ 2 * max 1 ((C_pack + 1) * Real.rpow δ (-ε))
      = (Real.rpow A (A + 1) * Real.rpow (Real.log (2 / Δ)) (A ^ 2)) * C_pack ^ 2 * max 1 ((C_pack + 1) * Real.rpow δ (-ε)) := by rw [h1] <;> ring
    _ = (Real.rpow A (A + 1) * C_pack ^ 2 * Real.rpow (Real.log (2 / Δ)) (A ^ 2)) * max 1 ((C_pack + 1) * Real.rpow δ (-ε)) := by ring
    _ ≤ (Real.rpow A (A + 1) * C_pack ^ 2 * Real.rpow (Real.log (2 / Δ)) (A ^ 2)) * Real.rpow Δ (-4 * ε) := by
      exact mul_le_mul_of_nonneg_left hmax1 hX_pos
    _ ≤ Real.rpow Δ (-6 * ε) * Real.rpow Δ (-4 * ε) := by
      exact mul_le_mul_of_nonneg_right hC2_poly (by positivity)
    _ = Real.rpow Δ (-10 * ε) := by
      have h6 : Real.rpow Δ (-6 * ε) * Real.rpow Δ (-4 * ε) = Real.rpow Δ ((-6 * ε) + (-4 * ε)) :=
        (Real.rpow_add hΔ_pos (-6 * ε) (-4 * ε)).symm
      rw [h6]
      have h7 : (-6 * ε) + (-4 * ε) = -10 * ε := by ring
      rw [h7]
  have hstrip_loss : (42 : ℝ) * (40 * 4 + 110) ≤ Real.rpow Δ (-5 * ε) := by
    have h := hd4 Δ hΔ_pos hΔ_lt_d4
    have h_norm : Real.rpow Δ (-(5 * ε)) = Real.rpow Δ (-5 * ε) := by ring_nf
    rw [h_norm] at h
    have h_def : C_strip = (42 : ℝ) * (40 * 4 + 110) := by simp [hC_strip_def]
    rw [h_def] at h
    exact h
  have hslope_sset_const : (1680000 : ℝ) ≤ Real.rpow Δ (-15 * ε) := by
    have h := hd5 Δ hΔ_pos hΔ_lt_d5
    have h_norm : Real.rpow Δ (-(15 * ε)) = Real.rpow Δ (-15 * ε) := by ring_nf
    rw [h_norm] at h
    have h_def : C_slope = (1680000 : ℝ) := by simp [hC_slope_def]
    rw [h_def] at h
    exact h
  have hpack_absorb2 : C_pack + 1 ≤ Real.rpow Δ (-2 * ε) / 6 := by
    have h : 6 * (C_pack + 1) ≤ Real.rpow Δ (-(2 * ε)) := hd6 Δ hΔ_pos hΔ_lt_d6
    have h_norm : Real.rpow Δ (-(2 * ε)) = Real.rpow Δ (-2 * ε) := by ring_nf
    rw [h_norm] at h
    linarith
  have hpack_absorb3 : C_pack + 1 ≤ Real.rpow Δ (-ε) / 6 := by
    have h : 6 * (C_pack + 1) ≤ Real.rpow Δ (-ε) := hd16 Δ hΔ_pos hΔ_lt_d16
    linarith
  have hM_large_absorb : 2 * (C_pack + 1) ≤ Real.rpow Δ (-2 * s + 2 * ε) := by
    have h1 : 2 * (C_pack + 1) ≤ 2 * (Real.rpow Δ (-2 * ε) / 6) := by gcongr
    have h2 : 2 * (Real.rpow Δ (-2 * ε) / 6) ≤ Real.rpow Δ (-2 * ε) := by
      have h3 : 0 < Real.rpow Δ (-2 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h4 : 2 * (Real.rpow Δ (-2 * ε) / 6) = Real.rpow Δ (-2 * ε) / 3 := by ring
      rw [h4]
      apply div_le_self
      · exact h3.le
      · norm_num
    have h4 : Real.rpow Δ (-2 * ε) ≤ Real.rpow Δ (-2 * s + 2 * ε) := by
      apply Real.rpow_le_rpow_of_exponent_ge hΔ_pos
      <;> linarith
    linarith
  have hC_pack_le : C_pack ≤ Real.rpow Δ (-ε) := hd8 Δ hΔ_pos hΔ_lt_d8
  have hM_upper_absorb : max 1 (C_pack * max 1 ((C_pack + 1) * Real.rpow δ (-ε))) * M ≤
      Real.rpow Δ (-2 * s - 6 * ε) := by
    have h1 : C_pack * max 1 ((C_pack + 1) * Real.rpow δ (-ε)) ≤ C_pack * Real.rpow Δ (-4 * ε) := by
      exact mul_le_mul_of_nonneg_left hmax1 (by positivity)
    have h2 : 1 ≤ C_pack * max 1 ((C_pack + 1) * Real.rpow δ (-ε)) := by
      have h21 : 1 ≤ C_pack := hC_pack_ge1
      have h22 : (1 : ℝ) ≤ max 1 ((C_pack + 1) * Real.rpow δ (-ε)) := le_max_left _ _
      calc 1
        = 1 * 1 := by ring
      _ ≤ C_pack * max 1 ((C_pack + 1) * Real.rpow δ (-ε)) := by gcongr
    have h5 : max 1 (C_pack * max 1 ((C_pack + 1) * Real.rpow δ (-ε))) =
        C_pack * max 1 ((C_pack + 1) * Real.rpow δ (-ε)) := by
      rw [max_eq_right h2]
    rw [h5]
    have h6 : C_pack * max 1 ((C_pack + 1) * Real.rpow δ (-ε)) * M ≤
        C_pack * Real.rpow Δ (-4 * ε) * M := by
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have h7 : C_pack * Real.rpow Δ (-4 * ε) * M ≤
        C_pack * Real.rpow Δ (-4 * ε) * Real.rpow Δ (-2 * s - ε) := by
      exact mul_le_mul_of_nonneg_left hM_upper (by positivity)
    have h_pos1 : 0 < Real.rpow Δ (-4 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_pos2 : 0 < Real.rpow Δ (-2 * s - ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h8 : C_pack * Real.rpow Δ (-4 * ε) * Real.rpow Δ (-2 * s - ε) ≤
        Real.rpow Δ (-ε) * (Real.rpow Δ (-4 * ε) * Real.rpow Δ (-2 * s - ε)) := by
      have h_pos : 0 ≤ Real.rpow Δ (-4 * ε) * Real.rpow Δ (-2 * s - ε) := mul_nonneg h_pos1.le h_pos2.le
      have h_assoc : C_pack * Real.rpow Δ (-4 * ε) * Real.rpow Δ (-2 * s - ε) =
          C_pack * (Real.rpow Δ (-4 * ε) * Real.rpow Δ (-2 * s - ε)) := by ring
      rw [h_assoc]
      exact mul_le_mul_of_nonneg_right hC_pack_le h_pos
    have h91 : Real.rpow Δ (-4 * ε) * Real.rpow Δ (-2 * s - ε) = Real.rpow Δ ((-4 * ε) + (-2 * s - ε)) :=
      (Real.rpow_add hΔ_pos (-4 * ε) (-2 * s - ε)).symm
    have h9 : Real.rpow Δ (-ε) * (Real.rpow Δ (-4 * ε) * Real.rpow Δ (-2 * s - ε)) =
        Real.rpow Δ (-2 * s - 6 * ε) := by
      rw [h91]
      have h93 : Real.rpow Δ (-ε) * Real.rpow Δ ((-4 * ε) + (-2 * s - ε)) =
          Real.rpow Δ ((-ε) + ((-4 * ε) + (-2 * s - ε))) :=
        (Real.rpow_add hΔ_pos (-ε) ((-4 * ε) + (-2 * s - ε))).symm
      rw [h93]
      have h94 : (-ε) + ((-4 * ε) + (-2 * s - ε)) = -2 * s - 6 * ε := by ring
      rw [h94]
    rw [h9] at h8
    exact le_trans (le_trans h6 h7) h8
  have hcover_lower_pack : (2000 : ENNReal) * (AppendixA4.affinePackingM : ENNReal) ≤
      ENNReal.ofReal (Real.rpow Δ (-14 * ε)) := by
    have h_rpow_norm : Real.rpow Δ (-(14 * ε)) = Real.rpow Δ (-14 * ε) := by ring_nf
    have h : (2000 : ℝ) * C_packM ≤ Real.rpow Δ (-14 * ε) := by
      have h' := hd7 Δ hΔ_pos hΔ_lt_d7
      rw [h_rpow_norm] at h'
      exact h'
    have h10 : (2000 : ENNReal) * (AppendixA4.affinePackingM : ENNReal) =
        ENNReal.ofReal ((2000 : ℝ) * C_packM) := by
      have h11 : (AppendixA4.affinePackingM : ENNReal) = ENNReal.ofReal C_packM := by
        simp [hC_packM_def, AppendixA4.affinePackingM] <;> norm_cast
      rw [h11, ENNReal.ofReal_mul] <;> norm_cast
    rw [h10]
    exact ENNReal.ofReal_le_ofReal h
  have hA2 : AppendixA.A2.A2_Smallness Δ δ s t ε A (C_pack + 1) M :=
    a2_smallness_from_bounds hΔ_pos hΔ_lt_half hδ_pos hδ_eq2 hs_pos h12ε hε_pos hA_pos
      hM_lower hM_upper hC_pack_ge1
      hK_loss hK_loss_strong hC2_loss hstrip_loss hslope_sset_const hM_upper_absorb
      hpack_absorb2 hpack_absorb3 hM_large_absorb hcover_lower_pack
  have hAssembly_num : AssemblyNumericalBounds Δ s t ε := hAssembly Δ hΔ_pos (lt_of_lt_of_le hΔ_lt_δ₀ hδ₀_le_assembly)
  have hpack_le_ε : C_pack + 1 ≤ Real.rpow Δ (-ε) := hd10 Δ hΔ_pos hΔ_lt_d10
  have henergy_le_ε : C_energy ≤ Real.rpow Δ (-ε) := hd11 Δ hΔ_pos hΔ_lt_d11
  have h_absorb_Y : C_Y * Real.rpow Δ (-10000 * ε) ≤ Real.rpow Δ (-η_axiom) := by
    have h1 : C_Y ≤ Real.rpow Δ (-(η_axiom - 10000 * ε)) := hd12 Δ hΔ_pos hΔ_lt_d12
    have h2 : Real.rpow Δ (-(η_axiom - 10000 * ε)) = Real.rpow Δ (-η_axiom + 10000 * ε) := by ring_nf
    rw [h2] at h1
    have h3 : C_Y * Real.rpow Δ (-10000 * ε) ≤
        Real.rpow Δ (-η_axiom + 10000 * ε) * Real.rpow Δ (-10000 * ε) := by
      have h_rpow_nonneg : 0 ≤ Real.rpow Δ (-10000 * ε) := Real.rpow_nonneg hΔ_pos.le _
      exact mul_le_mul_of_nonneg_right h1 h_rpow_nonneg
    have h4 : Real.rpow Δ (-η_axiom + 10000 * ε) * Real.rpow Δ (-10000 * ε) =
        Real.rpow Δ (-η_axiom) := by
      have h5 : Real.rpow Δ ((-η_axiom + 10000 * ε) + (-10000 * ε)) =
          Real.rpow Δ (-η_axiom + 10000 * ε) * Real.rpow Δ (-10000 * ε) :=
        Real.rpow_add hΔ_pos (-η_axiom + 10000 * ε) (-10000 * ε)
      have h6 : (-η_axiom + 10000 * ε) + (-10000 * ε) = -η_axiom := by ring
      have h7 : Real.rpow Δ (-η_axiom + 10000 * ε) * Real.rpow Δ (-10000 * ε) =
          Real.rpow Δ ((-η_axiom + 10000 * ε) + (-10000 * ε)) := h5.symm
      rw [h7, h6]
    rw [h4] at h3
    exact h3
  have h_absorb_X : C_X * Real.rpow Δ (-600 * ε) ≤ Real.rpow Δ (-η_axiom) := by
    have h1 : C_X ≤ Real.rpow Δ (-(η_axiom - 600 * ε)) := hd13 Δ hΔ_pos hΔ_lt_d13
    have h2 : Real.rpow Δ (-(η_axiom - 600 * ε)) = Real.rpow Δ (-η_axiom + 600 * ε) := by ring_nf
    rw [h2] at h1
    have h3 : C_X * Real.rpow Δ (-600 * ε) ≤
        Real.rpow Δ (-η_axiom + 600 * ε) * Real.rpow Δ (-600 * ε) := by
      have h_rpow_nonneg : 0 ≤ Real.rpow Δ (-600 * ε) := Real.rpow_nonneg hΔ_pos.le _
      exact mul_le_mul_of_nonneg_right h1 h_rpow_nonneg
    have h4 : Real.rpow Δ (-η_axiom + 600 * ε) * Real.rpow Δ (-600 * ε) =
        Real.rpow Δ (-η_axiom) := by
      have h5 : Real.rpow Δ ((-η_axiom + 600 * ε) + (-600 * ε)) =
          Real.rpow Δ (-η_axiom + 600 * ε) * Real.rpow Δ (-600 * ε) :=
        Real.rpow_add hΔ_pos (-η_axiom + 600 * ε) (-600 * ε)
      have h6 : (-η_axiom + 600 * ε) + (-600 * ε) = -η_axiom := by ring
      have h7 : Real.rpow Δ (-η_axiom + 600 * ε) * Real.rpow Δ (-600 * ε) =
          Real.rpow Δ ((-η_axiom + 600 * ε) + (-600 * ε)) := h5.symm
      rw [h7, h6]
    rw [h4] at h3
    exact h3
  have h_absorb_T : C_T * Real.rpow Δ (-600 * ε) ≤ Real.rpow Δ (-η_axiom) := by
    have h1 : C_T ≤ Real.rpow Δ (-(η_axiom - 600 * ε)) := hd14 Δ hΔ_pos hΔ_lt_d14
    have h2 : Real.rpow Δ (-(η_axiom - 600 * ε)) = Real.rpow Δ (-η_axiom + 600 * ε) := by ring_nf
    rw [h2] at h1
    have h3 : C_T * Real.rpow Δ (-600 * ε) ≤
        Real.rpow Δ (-η_axiom + 600 * ε) * Real.rpow Δ (-600 * ε) := by
      have h_rpow_nonneg : 0 ≤ Real.rpow Δ (-600 * ε) := Real.rpow_nonneg hΔ_pos.le _
      exact mul_le_mul_of_nonneg_right h1 h_rpow_nonneg
    have h4 : Real.rpow Δ (-η_axiom + 600 * ε) * Real.rpow Δ (-600 * ε) =
        Real.rpow Δ (-η_axiom) := by
      have h5 : Real.rpow Δ ((-η_axiom + 600 * ε) + (-600 * ε)) =
          Real.rpow Δ (-η_axiom + 600 * ε) * Real.rpow Δ (-600 * ε) :=
        Real.rpow_add hΔ_pos (-η_axiom + 600 * ε) (-600 * ε)
      have h6 : (-η_axiom + 600 * ε) + (-600 * ε) = -η_axiom := by ring
      have h7 : Real.rpow Δ (-η_axiom + 600 * ε) * Real.rpow Δ (-600 * ε) =
          Real.rpow Δ ((-η_axiom + 600 * ε) + (-600 * ε)) := h5.symm
      rw [h7, h6]
    rw [h4] at h3
    exact h3
  have hΔ_lt_16 : Δ < 1 / 16 := by
    have h : Δ < d15 := hΔ_lt_d15
    have h21 : 1 ≤ 4 / ε := by
      have h22 : ε ≤ 1 := hε_lt_one.le
      have h23 : 4 / ε ≥ 4 := by
        calc 4 / ε ≥ 4 / 1 := by gcongr
        _ = 4 := by norm_num
      linarith
    have h3 : (1 / 100 : ℝ) ^ (4 / ε) ≤ (1 / 100 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) h21
    have h4 : (1 / 100 : ℝ) ^ (1 : ℝ) = 1 / 100 := by simp
    have h5 : d15 ≤ 1 / 100 := by
      have h6 : d15 = (1 / 100 : ℝ) ^ (4 / ε) := hd15_def
      rw [h6]
      rw [h4] at h3
      exact h3
    have h7 : (1 / 100 : ℝ) ≤ 1 / 16 := by norm_num
    have h8 : d15 ≤ 1 / 16 := le_trans h5 h7
    exact lt_of_lt_of_le h h8
  have h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100 := by
    have h : Δ < d15 := hΔ_lt_d15
    have h2 : Δ ≤ (1 / 100 : ℝ) ^ (4 / ε) := by
      simpa [hd15_def] using le_of_lt h
    have h_base_nonneg : 0 ≤ Δ := by linarith
    have h_exp_nonneg : 0 ≤ ε / 4 := by positivity
    have h_rpow_le : Real.rpow Δ (ε / 4) ≤ Real.rpow (((1 / 100 : ℝ) ^ (4 / ε))) (ε / 4) :=
      Real.rpow_le_rpow h_base_nonneg h2 h_exp_nonneg
    have h4 : Real.rpow (((1 / 100 : ℝ) ^ (4 / ε))) (ε / 4) = (1 / 100 : ℝ) := by
      have h41 : Real.rpow (((1 / 100 : ℝ) ^ (4 / ε))) (ε / 4) =
          (1 / 100 : ℝ) ^ ((4 / ε) * (ε / 4)) :=
        (Real.rpow_mul (show (0 : ℝ) ≤ (1 / 100 : ℝ) by norm_num) (4 / ε) (ε / 4)).symm
      rw [h41]
      have h5 : (4 / ε) * (ε / 4) = 1 := by
        field_simp [hε_pos.ne'] <;> ring
      rw [h5]
      simp
    rw [h4] at h_rpow_le
    exact h_rpow_le
  have hΔ_lt_third : Δ < 1 / 3 := by linarith [hΔ_lt_16]
  have hΔ_lt_one : Δ < 1 := by linarith [hΔ_lt_half]
  have hΔ_small_allFine : (2000 : ℝ) * 2 < Real.rpow Δ (-(η_upper - 214 * ε)) := by
    have hη_eq : η_upper - 214 * ε = ε := by
      have h : η_upper = 215 * ε := by rfl
      rw [h] <;> ring
    rw [hη_eq]
    have h1 : (2 * 10^13 : ℝ) ≤ Real.rpow Δ (-ε) := hAssembly_num.hΔ_coarse_absorb_A9
    have h2 : (2000 : ℝ) * 2 < (2 * 10^13 : ℝ) := by norm_num
    exact lt_of_lt_of_le h2 h1
  have h_small2_univ : (68 : ℝ) ≤ Real.rpow Δ (-4 * ε) := by
    have h := hd17 Δ hΔ_pos hΔ_lt_d17
    have h_norm : Real.rpow Δ (-(4 * ε)) = Real.rpow Δ (-4 * ε) := by ring_nf
    rw [h_norm] at h
    exact h
  have h_uniform_num : ∀ (u : ℝ), t ≤ u → u ≤ 2 → AssemblyNumericalBounds Δ s u ε :=
    fun u htu hu2 => hAssembly_num.weaken_u h_small2_univ hΔ_pos hΔ_lt_one hs_pos hst htu hu2
  -- Uniform worst-case absorptions
  have h_energy_uniform_absorb : C_energy_uniform_absorb ≤ Real.rpow Δ (-ε) :=
    hd18 Δ hΔ_pos hΔ_lt_d18
  have h_Y_uniform_absorb : C_Y_uniform ≤ Real.rpow Δ (-(η_axiom - 10000 * ε)) :=
    hd19 Δ hΔ_pos hΔ_lt_d19
  -- Monotonicity: 9*3^(u-s) ≤ 9*3^(2-s) for u ≤ 2
  have h_C_Y_uniform_bound : ∀ (u : ℝ), t ≤ u → u ≤ 2 →
      (9 : ℝ) * (3 : ℝ)^(u - s) ≤ C_Y_uniform := by
    intro u htu hu2
    have h1 : u - s ≤ 2 - s := by linarith
    have h_base3 : (1 : ℝ) ≤ 3 := by norm_num
    have h2 : (3 : ℝ)^(u - s) ≤ (3 : ℝ)^(2 - s) :=
      Real.rpow_le_rpow_of_exponent_le h_base3 h1
    have h3 : (9 : ℝ) * (3 : ℝ)^(u - s) ≤ (9 : ℝ) * (3 : ℝ)^(2 - s) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    have h4 : C_Y_uniform = (9 : ℝ) * (3 : ℝ)^(2 - s) := by
      exact hC_Y_uniform_def
    rw [h4]
    exact h3
  -- Monotonicity: 4^u ≤ 16 for u ≤ 2
  have h_four_pow_u_bound : ∀ (u : ℝ), t ≤ u → u ≤ 2 → (4 : ℝ)^u ≤ 16 := by
    intro u htu hu2
    have h_base4 : (1 : ℝ) ≤ 4 := by norm_num
    have h1 : (4 : ℝ)^u ≤ (4 : ℝ)^(2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h_base4 hu2
    have h2 : (4 : ℝ)^(2 : ℝ) = 16 := by norm_num
    rw [h2] at h1
    exact h1
  -- Monotonicity: plane_energy_constant s u 2 ≤ C_energy_uniform for t ≤ u ≤ 2
  have h_C_energy_uniform_bound : ∀ (u : ℝ), t ≤ u → u ≤ 2 →
      MainAppendix.plane_energy_constant s u 2 ≤ C_energy_uniform := by
    intro u htu hu2
    have h_st_neg : s - t < 0 := by linarith
    have h_su_neg : s - u < 0 := by linarith
    have h_base2 : (1 : ℝ) ≤ 2 := by norm_num
    have h1 : (2 : ℝ)^(s - u) ≤ (2 : ℝ)^(s - t) :=
      Real.rpow_le_rpow_of_exponent_le h_base2 (by linarith)
    have h2 : (2 : ℝ)^(s - t) < 1 := by
      have h3 : (2 : ℝ)^(s - t) < (2 : ℝ)^(0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h_st_neg
      have h4 : (2 : ℝ)^(0 : ℝ) = 1 := by simp
      rw [h4] at h3
      exact h3
    have h4 : 0 < 1 - (2 : ℝ)^(s - t) := by linarith
    have h5 : 0 < 1 - (2 : ℝ)^(s - u) := by
      have h6 : (2 : ℝ)^(s - u) < 1 := by
        have h7 : (2 : ℝ)^(s - u) < (2 : ℝ)^(0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h_su_neg
        have h8 : (2 : ℝ)^(0 : ℝ) = 1 := by simp
        rw [h8] at h7
        exact h7
      linarith
    have h6 : (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u)) ≤
        (2 : ℝ)^s / (1 - (2 : ℝ)^(s - t)) := by
      have h7 : 1 - (2 : ℝ)^(s - u) ≥ 1 - (2 : ℝ)^(s - t) := by linarith
      have h8 : 0 < (2 : ℝ)^s := by positivity
      exact div_le_div_of_nonneg_left h8.le (by linarith) h7
    have h9 : (4 : ℝ)^u ≤ 16 := h_four_pow_u_bound u htu hu2
    have h10 : (4 : ℝ)^u + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u)) ≤
        (16 : ℝ) + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - t)) := by linarith
    have h11 : MainAppendix.plane_energy_constant s u 2 =
        (MainAppendix.plane_packing_constant : ℝ) *
          ((4 : ℝ)^u + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) := by
      have h_def : MainAppendix.plane_energy_constant s u 2 =
          (MainAppendix.plane_packing_constant : ℝ) *
            ((2 * (2 : ℝ))^u + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - u))) := by
        simp [MainAppendix.plane_energy_constant] <;> rfl
      rw [h_def]
      have h22 : (2 * (2 : ℝ))^u = (4 : ℝ)^u := by
        have h : (2 * (2 : ℝ)) = (4 : ℝ) := by norm_num
        rw [h]
      rw [h22] <;> rfl
      <;> exact Or.inl trivial
    rw [h11, hC_energy_uniform_def]
    have h12 : 0 ≤ (MainAppendix.plane_packing_constant : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_le_mul_of_nonneg_left h10 h12
  -- Forall-u adapters
  have h_uniform_energy : ∀ (u : ℝ), t ≤ u → u ≤ 2 →
      MainAppendix.plane_energy_constant s u 2 * (MainAppendix.plane_packing_constant : ℝ) ≤
        Real.rpow Δ (-ε) := by
    intro u htu hu2
    have h1 : MainAppendix.plane_energy_constant s u 2 ≤ C_energy_uniform :=
      h_C_energy_uniform_bound u htu hu2
    have h2 : MainAppendix.plane_energy_constant s u 2 * (MainAppendix.plane_packing_constant : ℝ) ≤
        C_energy_uniform_absorb := by
      have h_def : C_energy_uniform_absorb = C_energy_uniform * (MainAppendix.plane_packing_constant : ℝ) :=
        hC_energy_uniform_absorb_def
      rw [h_def]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    exact le_trans h2 h_energy_uniform_absorb
  have h_uniform_Y : ∀ (u : ℝ), t ≤ u → u ≤ 2 →
      ((9 : ℝ) * (3 : ℝ)^(u - s)) * Real.rpow Δ (-10000 * ε) ≤
        Real.rpow Δ (-η_axiom) := by
    intro u htu hu2
    have h1 : (9 : ℝ) * (3 : ℝ)^(u - s) ≤ C_Y_uniform := h_C_Y_uniform_bound u htu hu2
    have h_pos : 0 < Real.rpow Δ (-10000 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h2 : ((9 : ℝ) * (3 : ℝ)^(u - s)) * Real.rpow Δ (-10000 * ε) ≤
        C_Y_uniform * Real.rpow Δ (-10000 * ε) :=
      mul_le_mul_of_nonneg_right h1 h_pos.le
    have h3 : C_Y_uniform * Real.rpow Δ (-10000 * ε) ≤ Real.rpow Δ (-η_axiom) := by
      have h_rpow_nonneg : 0 ≤ Real.rpow Δ (-10000 * ε) := Real.rpow_nonneg hΔ_pos.le _
      have h4 : Real.rpow Δ (-η_axiom) =
          Real.rpow Δ (-(η_axiom - 10000 * ε)) * Real.rpow Δ (-10000 * ε) := by
        have h5 : Real.rpow Δ ((-(η_axiom - 10000 * ε)) + (-10000 * ε)) =
            Real.rpow Δ (-(η_axiom - 10000 * ε)) * Real.rpow Δ (-10000 * ε) :=
          Real.rpow_add hΔ_pos (-(η_axiom - 10000 * ε)) (-10000 * ε)
        have h6 : (-(η_axiom - 10000 * ε)) + (-10000 * ε) = -η_axiom := by ring
        rw [h6] at h5
        exact h5
      rw [h4]
      exact mul_le_mul_of_nonneg_right h_Y_uniform_absorb h_rpow_nonneg
    exact le_trans h2 h3
  have h_energy_uniform_absorb' : (MainAppendix.plane_packing_constant : ℝ)^2 *
      (16 + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - t))) ≤ Real.rpow Δ (-ε) := by
    have h_eq : C_energy_uniform_absorb = (MainAppendix.plane_packing_constant : ℝ)^2 *
        (16 + (2 : ℝ)^s / (1 - (2 : ℝ)^(s - t))) := by
      rw [hC_energy_uniform_absorb_def, hC_energy_uniform_def] <;> ring
    rw [h_eq] at h_energy_uniform_absorb
    exact h_energy_uniform_absorb
  have h_Y_uniform_absorb' : (9 : ℝ) * (3 : ℝ)^(2 - s) ≤ Real.rpow Δ (-(η_axiom - 10000 * ε)) := by
    have h_eq : C_Y_uniform = (9 : ℝ) * (3 : ℝ)^(2 - s) := by
      rw [hC_Y_uniform_def] <;> ring
    rw [h_eq] at h_Y_uniform_absorb
    exact h_Y_uniform_absorb
  exact ⟨hA2, hAssembly_num, h_uniform_num, hΔ_small_allFine, hpack_le_ε, henergy_le_ε,
    h_absorb_Y, h_absorb_X, h_absorb_T,
    hΔ_le_δ₀_axiom, hΔ_lt_half, hΔ_lt_third, hΔ_lt_16, hΔ_lt_one, h_small_eps,
    h_energy_uniform_absorb', h_Y_uniform_absorb',
    h_C_Y_uniform_bound, h_C_energy_uniform_bound, h_four_pow_u_bound,
    h_uniform_energy, h_uniform_Y⟩

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction
