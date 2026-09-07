import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperCV
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperBroadMassBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperAbsorptionArithmetic
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiberHabsorption
import Mathlib.Tactic

/-!
# Broad set deletion via 3D multilinear Kakeya (Paper Lemma 11)

This module formalizes the constant-multiplicity loophole for broad set deletion:
using the CV (Córdoba/Visan) 3D endpoint multilinear Kakeya theorem to bound
the volume of the broad set, then converting to a multiplicity-weighted mass
bound on a constant-multiplicity subshading.

## Core result

`broad_set_small_from_real_absorption`: given a real-valued absorption inequality
`2 · M · C · (δ² · N)^(3/2) ≤ √(Q·τ) · mass`, derive the broad-small condition
`2 · broadMass ≤ S.mass` using the paper CV estimate.

## Mathematical route

1. `paper_cv_broad_set_estimate` gives the universal CV volume bound:
   `L · volume(E) ≤ C · (δ² · N)^(3/2)` when `L ≤ √(trilinear multiplicity)` on E.
2. On the counted-broad set `E = paperCountedBroadSet S tau Q`, we have
   `Q·τ ≤ trilinear multiplicity`, so `L = √(Q·τ)` satisfies the CV hypothesis.
3. The multiplicity-weighted broad mass satisfies `broadMass ≤ M · volume(E)`.
4. The absorption inequality converts the CV volume bound into the required
   `2 · broadMass ≤ S.mass`.

## Whiteprint

This is the `broad_set_multilinear_kakeya` node. It depends on:
- `multilinear_kakeya_theorem` (via `paper_cv_broad_set_estimate`)
- `transverse_from_sticky` (provides multiplicity m for Q = m³/16)
- `constant_multiplicity_refinement` (provides M = 2μ₀ upper bound)
-/

noncomputable section

open MeasureTheory Set Finset Classical ENNReal
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Specialize the universal paper CV estimate to a specific shading.

Given the universal estimate from `paper_cv_broad_set_estimate`, produce
the shading-specific form required by `paper_broad_mass_budget_main`. -/
lemma specialize_paper_cv_to_shading
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (C : ENNReal)
    (hCV_univ : ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
      ∀ (F : Kakeya.Streamlined.TubeFamily delta),
      ∀ (Y : WZ1PaperTubeShading F),
      ∀ (E : Set Point3) (L : ENNReal),
        MeasurableSet E →
        (∀ x ∈ E, L ≤ paperShadingTrilinearMultiplicity Y x ^ (1 / 2 : ℝ)) →
        L * volume E ≤ C * (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ))
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1) :
    ∀ (E : Set Point3), MeasurableSet E → E ⊆ S.union →
      ∀ (L : ENNReal),
        (∀ p ∈ E, L ≤ (paperShadingTrilinearMultiplicity S p)^(1/2:ℝ)) →
        L * volume E ≤ C * (ENNReal.ofReal (delta^2) * F.enncard)^(3/2:ℝ) := by
  intro E hE_meas hE_sub L hL_bound
  exact hCV_univ delta hdelta_pos hdelta_le_one F S E L hE_meas hL_bound

/-- **Broad set smallness from real absorption inequality.**

Given a cubical paper shading `S`, the universal CV estimate, a multiplicity
upper bound `M`, broad-set parameters `Q`, `tau`, and a real-valued absorption
inequality, prove that the broad set has multiplicity-weighted mass at most
`S.mass / 2`.

This is the core of Paper Lemma 11 (broad deletion via multilinear Kakeya).
The real absorption inequality is the only parameter-dependent condition; it
can always be satisfied by choosing `Q` sufficiently large (see
`general_h_absorb_Q_exists` in `FiberHabsorption.lean`).

### Parameters

- `C_real`: real upper bound for the CV constant
- `M_max`: real upper bound for point multiplicity on `S`
- `N`: cardinality bound for the tube family
- `mass_band`: real lower bound for `S.mass`
- `h_real`: `2 · M_max · C_real · (δ² · N)^(3/2) ≤ √(Q·τ) · mass_band`
-/
theorem broad_set_small_from_real_absorption
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    -- Universal CV estimate
    (C : ENNReal)
    (hC_ne_top : C ≠ ⊤)
    (hCV_univ : ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
      ∀ (F : Kakeya.Streamlined.TubeFamily delta),
      ∀ (Y : WZ1PaperTubeShading F),
      ∀ (E : Set Point3) (L : ENNReal),
        MeasurableSet E →
        (∀ x ∈ E, L ≤ paperShadingTrilinearMultiplicity Y x ^ (1 / 2 : ℝ)) →
        L * volume E ≤ C * (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ))
    -- Shading properties
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    -- Multiplicity upper bound
    (M_max : ℝ)
    (hM_max_nonneg : 0 ≤ M_max)
    (hM_max : ∀ p ∈ S.union, (S.pointMultiplicity p : ENNReal) ≤ ENNReal.ofReal M_max)
    -- Broad-set parameters
    (Q : ℕ)
    (tau : ℝ)
    (hQ_pos : 0 < Q)
    (htau_pos : 0 < tau)
    -- Real-valued absorption parameters
    (C_real : ℝ)
    (hC_real_nonneg : 0 ≤ C_real)
    (hC_le : C ≤ ENNReal.ofReal C_real)
    (N : ℕ)
    (hN_pos : 0 < N)
    (hcard : F.enncard ≤ (N : ENNReal))
    (mass_band : ℝ)
    (hmass_band_pos : 0 < mass_band)
    (hmass_band : ENNReal.ofReal mass_band ≤ S.mass)
    -- The key absorption inequality
    (h_real : 2 * M_max * C_real * ((delta ^ 2) * (N : ℝ))^(3 / 2 : ℝ) ≤
        Real.sqrt ((Q : ℝ) * tau) * mass_band) :
    2 * (∫⁻ p in paperCountedBroadSet S tau Q,
          (S.pointMultiplicity p : ENNReal)) ≤ S.mass := by
  -- Step 1: Specialize CV estimate to this shading
  have hCV_spec : ∀ (E : Set Point3), MeasurableSet E → E ⊆ S.union →
      ∀ (L : ENNReal),
        (∀ p ∈ E, L ≤ (paperShadingTrilinearMultiplicity S p)^(1/2:ℝ)) →
        L * volume E ≤ C * (ENNReal.ofReal (delta^2) * F.enncard)^(3/2:ℝ) :=
    specialize_paper_cv_to_shading (S := S) (F := F) (delta := delta)
      C hCV_univ hdelta_pos hdelta_le_one

  -- Step 2: Convert real absorption inequality to ENNReal form
  let M_enn : ENNReal := ENNReal.ofReal M_max
  have h_absorb_enn : (2 : ENNReal) * M_enn * C *
        (ENNReal.ofReal (delta ^ 2) * F.enncard)^(3 / 2 : ℝ) ≤
      (((Q : ENNReal) * ENNReal.ofReal tau)^(1 / 2 : ℝ)) * S.mass :=
    paper_h_absorb_ennreal_bridge
      (delta ^ 2) N C_real M_max mass_band tau Q
      C M_enn S.mass F.enncard
      (by positivity) hC_real_nonneg hM_max_nonneg (by linarith) htau_pos hN_pos
      h_real hC_le (by rfl) hcard hmass_band

  -- Step 3: Apply the broad mass budget theorem
  exact paper_broad_mass_budget_main
    C hCV_spec M_enn hM_max Q tau hQ_pos htau_pos h_absorb_enn

/-- **Existence of a broad-small Q.**

For any positive parameters, there exists a natural number `Q` such that
the real absorption inequality holds. This shows the broad-small condition
is always achievable by choosing the broadness threshold large enough.

When used with the narrow-pruning pipeline, one additionally needs
`4 · Q ≤ m³` where `m` is the multiplicity lower bound. Whether this holds
depends on the specific scaling of `m` from sticky data.
-/
lemma exists_Q_for_broad_small
    (M_max C_real delta N tau mass_band : ℝ)
    (hM_nonneg : 0 ≤ M_max)
    (hC_nonneg : 0 ≤ C_real)
    (hdelta_nonneg : 0 ≤ delta)
    (hN_pos : 0 < N)
    (htau_pos : 0 < tau)
    (hmass_pos : 0 < mass_band) :
    ∃ (Q : ℕ), 2 * M_max * C_real * ((delta ^ 2) * (N : ℝ))^(3 / 2 : ℝ) ≤
        Real.sqrt ((Q : ℝ) * tau) * mass_band :=
  general_h_absorb_Q_exists
    M_max C_real ((delta ^ 2) * (N : ℝ)) tau mass_band
    hM_nonneg hC_nonneg (by positivity) htau_pos hmass_pos

/-- **Broad set smallness via constant-multiplicity loophole.**

Improved version that makes the μ₀ cancellation explicit. Given a shading
with point multiplicity in `[μ₀, 2μ₀)`, the CV estimate, and a geometric
volume lower bound, prove `2 · broadMass ≤ S.mass`.

### Key cancellation

Since `multiplicity ≈ μ₀`:
- `broadMass ≤ 2μ₀ · volume(broad)`
- `S.mass ≥ μ₀ · volume(S.union)`
- So `2 · broadMass ≤ S.mass` follows from `4 · volume(broad) ≤ volume(S.union)`

The μ₀ factor **cancels entirely**. The remaining condition is purely geometric:
the CV broad-set volume must be at most `volume(S.union) / 4`.

### Geometric hypothesis

`hvol_lower` is the "N-bound linchpin": it requires the broad-set CV upper
bound to be dominated by the union volume. For a dense cubical shading,
`volume(S.union) ≳ δ² · N / μ₀`, so this becomes a condition on `Q · τ`.
-/
theorem broad_set_small_constant_multiplicity
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    -- Universal CV estimate
    (C : ENNReal)
    (hC_ne_top : C ≠ ⊤)
    (hCV_univ : ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
      ∀ (F : Kakeya.Streamlined.TubeFamily delta),
      ∀ (Y : WZ1PaperTubeShading F),
      ∀ (E : Set Point3) (L : ENNReal),
        MeasurableSet E →
        (∀ x ∈ E, L ≤ paperShadingTrilinearMultiplicity Y x ^ (1 / 2 : ℝ)) →
        L * volume E ≤ C * (ENNReal.ofReal (delta ^ 2) * F.enncard) ^ (3 / 2 : ℝ))
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    -- Constant multiplicity bounds
    (mu0 : ENNReal)
    (hmu0_ne_top : mu0 ≠ ⊤)
    (hmult_lower : ∀ p ∈ S.union, mu0 ≤ (S.pointMultiplicity p : ENNReal))
    (hmult_upper : ∀ p ∈ S.union, (S.pointMultiplicity p : ENNReal) < 2 * mu0)
    -- Broad-set parameters
    (Q : ℕ)
    (tau : ℝ)
    (hQ_pos : 0 < Q)
    (htau_pos : 0 < tau)
    -- Geometric volume lower bound (N-bound linchpin)
    (hvol_lower : (4 : ENNReal) * C * (ENNReal.ofReal (delta ^ 2) * F.enncard)^(3 / 2 : ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal tau)^(1 / 2 : ℝ)) * volume S.union) :
    2 * (∫⁻ p in paperCountedBroadSet S tau Q,
          (S.pointMultiplicity p : ENNReal)) ≤ S.mass := by
  let E := paperCountedBroadSet S tau Q
  let L : ENNReal := ((Q : ENNReal) * ENNReal.ofReal tau)^(1/2:ℝ)
  have hE_meas : MeasurableSet E := paperCountedBroadSet_measurable S tau Q
  have hE_sub : E ⊆ S.union := by intro p hp; exact hp.1

  -- Step 1: CV bound on broad set volume
  have hL_bound : ∀ p ∈ E, L ≤ (paperShadingTrilinearMultiplicity S p)^(1/2:ℝ) := by
    intro p hp
    have hQ_count : Q ≤ paperLargeTripleCount S p tau := hp.2
    have h_mult : (Q : ENNReal) * ENNReal.ofReal tau ≤ paperShadingTrilinearMultiplicity S p :=
      paper_large_triple_count_le_multiplicity S p tau Q hQ_count
    exact ENNReal.rpow_le_rpow h_mult (by norm_num)
  have hCV' : L * volume E ≤ C * (ENNReal.ofReal (delta ^ 2) * F.enncard)^(3/2:ℝ) :=
    hCV_univ delta hdelta_pos hdelta_le_one F S E L hE_meas hL_bound

  -- Step 2: 4 * volume(E) ≤ volume(S.union)
  have hL_ne_zero : L ≠ 0 := by positivity
  have hL_ne_top : L ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
  have h1 : L * ((4 : ENNReal) * volume E) ≤
      (4 : ENNReal) * C * (ENNReal.ofReal (delta ^ 2) * F.enncard)^(3/2:ℝ) := by
    have h1a : L * volume E ≤ C * (ENNReal.ofReal (delta ^ 2) * F.enncard)^(3/2:ℝ) := hCV'
    have h : L * ((4 : ENNReal) * volume E) = (4 : ENNReal) * (L * volume E) := by ring
    rw [h]
    have h2 : (4 : ENNReal) * (L * volume E) ≤ (4 : ENNReal) * (C * (ENNReal.ofReal (delta ^ 2) * F.enncard)^(3/2:ℝ)) := by
      exact mul_le_mul_of_nonneg_left h1a (by positivity)
    have h3 : (4 : ENNReal) * (C * (ENNReal.ofReal (delta ^ 2) * F.enncard)^(3/2:ℝ)) =
        (4 : ENNReal) * C * (ENNReal.ofReal (delta ^ 2) * F.enncard)^(3/2:ℝ) := by ring
    rw [h3] at h2
    exact h2
  have h2 : L * ((4 : ENNReal) * volume E) ≤ L * volume S.union :=
    le_trans h1 hvol_lower
  have h4vol : (4 : ENNReal) * volume E ≤ volume S.union :=
    (ENNReal.mul_le_mul_iff_right hL_ne_zero hL_ne_top).mp h2

  -- Step 3: broadMass ≤ 2 * mu0 * volume(E)
  set broadMass := ∫⁻ p in E, (S.pointMultiplicity p : ENNReal) with hBM_def
  have h_broad_le : broadMass ≤ (2 : ENNReal) * mu0 * volume E := by
    have h_mult_upper : ∀ p ∈ E, (S.pointMultiplicity p : ENNReal) ≤ (2 : ENNReal) * mu0 := by
      intro p hp
      have h4 : p ∈ S.union := hE_sub hp
      have h5 : (S.pointMultiplicity p : ENNReal) < (2 : ENNReal) * mu0 := hmult_upper p h4
      exact le_of_lt h5
    calc broadMass
      ≤ ∫⁻ _p in E, (2 : ENNReal) * mu0 := setLIntegral_mono' hE_meas h_mult_upper
    _ = (2 : ENNReal) * mu0 * volume E := by
      rw [setLIntegral_const] <;> ring

  -- Step 4: S.mass ≥ mu0 * volume(S.union)
  have h_union_meas : MeasurableSet S.union := by
    have h : S.union = ⋃ i : Fin F.card, S.carrier i := by
      ext p
      simp only [Kakeya.Streamlined.Shading.union, Set.mem_iUnion]
      <;> aesop
    rw [h]
    exact MeasurableSet.iUnion fun i => S.measurable_carrier i
  have h_mass_lower : mu0 * volume S.union ≤ S.mass := by
    have h_eq : (∫⁻ p, (S.pointMultiplicity p : ENNReal)) = S.mass :=
      lintegral_pointMultiplicity S
    have h4 : ∫⁻ p, (S.pointMultiplicity p : ENNReal) ≥ ∫⁻ p in S.union, (S.pointMultiplicity p : ENNReal) := by
      exact setLIntegral_le_lintegral (Streamlined.Shading.union S) fun x =>
        ↑(Streamlined.Shading.pointMultiplicity S x)
    have h5 : ∫⁻ p in S.union, (S.pointMultiplicity p : ENNReal) ≥ ∫⁻ p in S.union, mu0 := by
      exact setLIntegral_mono' h_union_meas hmult_lower
    have h6 : ∫⁻ p in S.union, mu0 = mu0 * volume S.union := by
      rw [setLIntegral_const] <;> ring
    calc mu0 * volume S.union
        = ∫⁻ p in S.union, mu0 := by rw [h6]
      _ ≤ ∫⁻ p in S.union, (S.pointMultiplicity p : ENNReal) := h5
      _ ≤ ∫⁻ p, (S.pointMultiplicity p : ENNReal) := h4
      _ = S.mass := h_eq

  -- Step 5: Combine
  calc
    2 * broadMass
      ≤ 2 * ((2 : ENNReal) * mu0 * volume E) := by gcongr
    _ = (4 : ENNReal) * mu0 * volume E := by ring
    _ = mu0 * ((4 : ENNReal) * volume E) := by ring
    _ ≤ mu0 * volume S.union := by gcongr
    _ ≤ S.mass := h_mass_lower

end Kakeya.Assouad

end
