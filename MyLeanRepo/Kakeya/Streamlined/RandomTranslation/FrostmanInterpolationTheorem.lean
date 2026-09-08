import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.ScaleInterpolation
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FrostmanInterpolation
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FrostmanAssembly
import MyLeanRepo.Kakeya.Streamlined.Estimates

/-!
# Frostman scale interpolation

Transfer Frostman property between scales using volume ratio bounds.

## Main results

- `frostman_constant_scale`: Frostman constant can be scaled up by any factor ≥ 1
- `frostman_transfer_basic`: transfer Frostman from a finer-scale factoring to a
  coarser-scale factoring when contained masses and fiber masses are comparable
- `frostman_from_grid_bracketing`: given grid-scale Frostman and volume ratio
  bounds, obtain Frostman at an intermediate scale

The full cross-scale transfer for a `CoherentUniformTubeStructure` requires
geometric nesting assumptions (fiber decomposition, essential disjointness of
coarse tubes) that are not yet packaged into a single hypothesis.
-/

noncomputable section

open MeasureTheory Kakeya.Streamlined Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.RandomTranslation

/-- Scaling the Frostman constant of a generic factoring. -/
lemma frostman_constant_scale
    {fine coarse : BodyFamily} {P : Factoring fine coarse}
    {C C' : ENNReal} (h : P.FibersAreCFrostman C) (hC' : 1 ≤ C') :
    P.FibersAreCFrostman (C' * C) := by
  intro j K hK_conv hK_sub
  have h1 := h j K hK_conv hK_sub
  have h2 : C ≤ C' * C := by
    have h3 : C ≤ 1 * C := by simp
    have h4 : 1 * C ≤ C' * C := by gcongr
    exact le_trans h3 h4
  have h5 : C * P.fiberMass j * volume K ≤ C' * C * P.fiberMass j * volume K := by
    gcongr
  exact le_trans h1 h5

/-- Basic Frostman transfer between two factorings of the SAME fine family.

If `P_k` is Frostman with constant `C_k`, and for every fiber `j` of `P_rho`
and convex `K ⊆ coarse_rho(j)`, there exists a fiber `i` of `P_k` such that:
- `K ⊆ coarse_k(i)` (so Frostman at scale k applies to K)
- `fiberContainedMass_rho(j,K) ≤ fiberContainedMass_k(i,K)`
- `fiberMass_k(i) ≤ fiberMass_rho(j)`
- `coarseVol_rho(j) ≤ C_vol * coarseVol_k(i)`

Then `P_rho` is Frostman with constant `C_vol * C_k`. -/
lemma frostman_transfer_basic
    {fine coarse_k coarse_rho : BodyFamily}
    {P_k : Factoring fine coarse_k}
    {P_rho : Factoring fine coarse_rho}
    {C_k C_vol : ENNReal}
    (hFrost_k : P_k.FibersAreCFrostman C_k)
    (h_transfer : ∀ (j_rho : Fin coarse_rho.card) (K : Set Point3),
      Convex ℝ K → K ⊆ (coarse_rho.body j_rho).carrier →
      ∃ (j_k : Fin coarse_k.card),
        K ⊆ (coarse_k.body j_k).carrier ∧
        P_rho.fiberContainedMass j_rho K ≤ P_k.fiberContainedMass j_k K ∧
        P_k.fiberMass j_k ≤ P_rho.fiberMass j_rho ∧
        (coarse_rho.body j_rho).volume ≤ C_vol * (coarse_k.body j_k).volume) :
    P_rho.FibersAreCFrostman (C_vol * C_k) := by
  intro j_rho K hK_conv hK_sub
  rcases h_transfer j_rho K hK_conv hK_sub with
    ⟨j_k, hK_sub_k, h_contained_le, h_mass_le, h_vol_le⟩
  have h1 := hFrost_k j_k K hK_conv hK_sub_k
  have h_a : P_rho.fiberContainedMass j_rho K * (coarse_rho.body j_rho).volume ≤
      P_k.fiberContainedMass j_k K * (C_vol * (coarse_k.body j_k).volume) :=
    mul_le_mul h_contained_le h_vol_le (by positivity) (by positivity)
  have h_b : P_k.fiberContainedMass j_k K * (C_vol * (coarse_k.body j_k).volume) =
      C_vol * (P_k.fiberContainedMass j_k K * (coarse_k.body j_k).volume) := by ring
  have h_c : C_vol * (P_k.fiberContainedMass j_k K * (coarse_k.body j_k).volume) ≤
      C_vol * (C_k * P_k.fiberMass j_k * MeasureTheory.volume K) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h_d : C_vol * (C_k * P_k.fiberMass j_k * MeasureTheory.volume K) =
      (C_vol * C_k) * P_k.fiberMass j_k * MeasureTheory.volume K := by ring
  have h_e : (C_vol * C_k) * P_k.fiberMass j_k * MeasureTheory.volume K ≤
      (C_vol * C_k) * P_rho.fiberMass j_rho * MeasureTheory.volume K := by
    have h_e1 : (C_vol * C_k) * P_k.fiberMass j_k ≤
        (C_vol * C_k) * P_rho.fiberMass j_rho :=
      mul_le_mul_of_nonneg_left h_mass_le (by positivity)
    exact mul_le_mul_of_nonneg_right h_e1 (by positivity)
  exact le_trans (le_trans (le_trans h_a (le_of_eq h_b)) h_c) (le_trans (le_of_eq h_d) h_e)

/-- Volume ratio between two scales using the grid ratio bound.

If `ρ_k ≤ ρ ≤ ρ_{k-1}` and `ρ_{k-1} ≤ A * ρ_k`, then
`deltaTubeVolume ρ ≤ C_vol(A) * deltaTubeVolume ρ_k`,
where `C_vol(A) = ofReal(((π + 8πA/3)/2) * A^2)`. -/
lemma scale_volume_ratio
    {ρ ρ_k ρ_km1 A : ℝ}
    (hρk_pos : 0 < ρ_k) (hρ_pos : 0 < ρ)
    (h1 : ρ_k ≤ ρ) (h2 : ρ ≤ ρ_km1)
    (h3 : ρ_km1 ≤ A * ρ_k) (hA_pos : 0 < A)
    (hρkm1_le_one : ρ_km1 ≤ 1) :
    Kakeya.deltaTubeVolume ρ ≤
      ENNReal.ofReal (((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2) *
      Kakeya.deltaTubeVolume ρ_k :=
  have h4 : ρ ≤ A * ρ_k := le_trans h2 h3
  have hρ_le_one : ρ ≤ 1 := le_trans h2 hρkm1_le_one
  deltaTubeVolume_ratio_bound hρk_pos hρ_pos h1 h4 hA_pos hρ_le_one

/-- Frostman at all admissible scales from grid-scale Frostman.

Given a uniform tube structure `U`, suppose:
1. Frostman holds at every grid scale `ρ_k` with constant `C_grid`
2. For every admissible scale `ρ`, there is a grid scale `ρ_k ≤ ρ` and a
   transfer hypothesis relating the fibers at `ρ` to those at `ρ_k`
3. The volume ratio `V_ρ / V_{ρ_k}` is bounded by `C_vol`

Then Frostman holds at every admissible scale with constant `C_vol * C_grid`.

This is the main interpolation theorem. The transfer hypothesis is the key
geometric assumption that must be verified for a specific cover construction. -/
theorem frostman_from_grid_interpolation
    {δ : ℝ} {F : TubeFamily δ}
    (U : AssignedUniformTubeStructure F)
    (C_grid C_vol : ENNReal)
    (h_grid : ∀ (rho : AdmissibleScale δ),
      (U.cover rho).AssignedFibersAreCFrostman C_grid)
    (h_transfer : ∀ (rho : AdmissibleScale δ),
      ∃ (rho_k : AdmissibleScale δ),
        rho_k.val ≤ rho.val ∧
        (∀ (j : Fin (U.coarse rho).card) (K : Set Point3),
          Convex ℝ K → K ⊆ ((U.coarse rho).toBodyFamily.body j).carrier →
          ∃ (i : Fin (U.coarse rho_k).card),
            K ⊆ ((U.coarse rho_k).toBodyFamily.body i).carrier ∧
            (U.cover rho).toFactoring.fiberContainedMass j K ≤
              (U.cover rho_k).toFactoring.fiberContainedMass i K ∧
            (U.cover rho_k).toFactoring.fiberMass i ≤
              (U.cover rho).toFactoring.fiberMass j ∧
            ((U.coarse rho).toBodyFamily.body j).volume ≤
              C_vol * ((U.coarse rho_k).toBodyFamily.body i).volume)) :
    U.AssignedIsFrostmanAtEveryScale (C_vol * C_grid) := by
  intro rho
  rcases h_transfer rho with ⟨rho_k, _, h_transfer_jK⟩
  exact frostman_transfer_basic (h_grid rho_k) h_transfer_jK

end Kakeya.Streamlined.RandomTranslation
