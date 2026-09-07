module

/-
# Exact Endgame Composition — GENERALIZED v3

Corrected interface with three independent exponents and exact constants:
- `rho_sel`: selection retention exponent (δ^rho_sel ≤ c/2)
- `rho_sep`: direction separation exponent (r = δ^rho_sep)
- `rho_exc`: Kaufman bad-direction threshold exponent (threshold = δ^(-rho_exc))

Uses:
- kestrel's `kaufman_exact_for_endgame`: exact bad mass c/8
- lagoon's `threefold_recursive_selection`: exact retention c/2, separation r
- marlin's WireBudgets_v2: exponent ledger

Energy ledger:
- Bad-direction threshold: q_bad = rho_exc
- Normalized subset energy: q_bad + 6·rho_sel
- Coordinate energy: q_bad + 6·rho_sel + 2·κ0·rho_sep

## Whiteprint node
`exact_endgame_composition_v3`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.FrostmanFromDeltaSet
public import MyLeanRepo.ProductLikeIncidence.CoordinateNormalization
public import MyLeanRepo.Energy.AverageProjectionEnergy
public import MyLeanRepo.Energy.RegularSetHasBoundedEnergy
public import MyLeanRepo.Energy.KaufmanBadDirectionsBridge
public import MyLeanRepo.Energy.KaufmanIntegrationHelper
public import MyLeanRepo.ProductLikeIncidence.ThreefoldRecursiveSelectionExact
public import MyLeanRepo.Energy.RieszEnergyMonotonicity
public import MyLeanRepo.Energy.RelativeEnergyBound
public import MyLeanRepo.Energy.EndgameEnergyHelper
public import MyLeanRepo.ProductLikeIncidence.NormalizationHelpers
public import MyLeanRepo.OSWPrelude

@[expose] public section


noncomputable section

open MeasureTheory ENNReal Set Bornology Finset Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- **Steps 1-4 (GENERALIZED v3): From parameter point set to three separated directions.**

Given the refined parameter set `Pbar_param` with `(δ,2s)`-set regularity and multiplicity,
construct uniform measure `μE`, Frostman `ν`, small bad set `Θ_bad`, and three
separated directions with nested subsets.

v3 corrections from v2:
- Uses exact Kaufman bridge (`kaufman_exact_for_endgame`) with threshold `δ^(-rho_exc)`
  and bad mass `c/8`, avoiding the impossible `C·δ^q ≤ δ^(2ε)` condition.
- Uses exact threefold selection with retention `c/2` per step and separation `r = δ^rho_sep`.
- `rho_sel`, `rho_sep`, `rho_exc` are explicit parameters chosen by WireBudgets_v3.
- `c` is an exact constant, not δ-dependent.

### Parameters
- `rho_sel`: selection retention exponent; requires `δ^rho_sel ≤ c/2`
- `rho_sep`: separation exponent; `r = δ^rho_sep`, requires `rho_sep ≤ 1`
- `q_bad`: Kaufman threshold exponent; threshold = `δ^(-q_bad)`, bad mass = `c/8`

### Key numeric conditions
- `hδ_rho_sel_le_c2`: `δ^rho_sel ≤ c/2`
- `h_small_neighborhood`: `2·C_ν·r^τ ≤ c/8`
- `h_kaufman_absorb`: `C_Kaufman·C_plan ≤ δ^(-q_bad)·(c/8)`
-/
lemma exact_endgame_steps_1_4_generalized_v3
    {δ s τ κ0 L η c C_trim C_Y C_Pbar R : ℝ}
    (rho_sel rho_sep : ℝ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hδ_le_one : δ ≤ 1)
    (hs_pos : 0 < s)
    (hτ_pos : 0 < τ)
    (hκ0_pos : 0 < κ0)
    (hκ0_lt_s : κ0 < s)
    (hτ_gt_2κ0 : τ > 2 * κ0)
    -- Exponent parameters
    (hrho_sel_pos : 0 < rho_sel)
    (hrho_sep_pos : 0 < rho_sep)
    (hrho_sep_le_one : rho_sep ≤ 1)
    (hL_pos : 0 < L)
    (hη_pos : 0 < η)
    (hc_pos : 0 < c)
    (hC_Y_pos : 0 < C_Y)
    (hC_Pbar_pos : 0 < C_Pbar)
    (hR_pos : 0 < R)
    (q_bad : ℝ)
    (hq_bad_pos : 0 < q_bad)
    (hR_ge1 : 1 ≤ R)
    -- Numeric conditions (from WireBudgets_v3)
    (hδ_rho_sel_le_c2 : δ ^ rho_sel ≤ c / 2)
    (h_small_neighborhood : 2 * (3 * C_Y * 2 ^ τ) * (δ ^ rho_sep) ^ τ ≤ c / 8)
    (h_kaufman_absorb :
      (1 + ((3 * C_Y * 2 ^ τ) + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) *
        (1 + (2 * κ0) / (τ - 2 * κ0))) *
      robust_projection.energyBoundConstant C_Pbar s κ0 ≤
      δ ^ (-q_bad) * (c / 8))
    -- Y data
    {Y : Set ℝ}
    (hY_grid : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C_Y Y)
    (hY_fin : Y.Finite)
    (hY_nonempty : Y.Nonempty)
    -- Pbar data (parameter points directly)
    {Pbar_param : Set (EuclideanSpace ℝ (Fin 2))}
    (hPbar_delta : IsDeltaSCSet (d := 2) δ (2 * s) C_Pbar Pbar_param)
    (hPbar_nonempty : Pbar_param.Nonempty)
    (hPbar_size : ENNReal.ofReal (δ ^ (-2 * κ0)) ≤ Nplane δ Pbar_param)
    -- Box bound for Kaufman averaging
    (hP_param_in_Rbox : Pbar_param ⊆
      {p : EuclideanSpace ℝ (Fin 2) | ∀ i, p i ∈ Set.Icc (-R) R})
    -- T_y: point sets per direction
    {T_y_points : ℝ → Set (EuclideanSpace ℝ (Fin 2))}
    (hT_y_points_sub : ∀ y ∈ Y, T_y_points y ⊆ Pbar_param)
    -- Multiplicity: each point appears for ≥ c|Y| directions
    (h_multiplicity_points : ∀ p ∈ Pbar_param,
      ENat.toENNReal {y ∈ Y | p ∈ T_y_points y}.encard ≥
        ENNReal.ofReal c * ENat.toENNReal Y.encard)
    -- Projection bound for T_y parameter points
    (h_proj_bound : ∀ y ∈ Y,
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) (T_y_points y)) ≤
      ENNReal.ofReal (δ ^ (-(L * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal))) :
    ∃ (ν : Measure ℝ)
      (E : Finset (EuclideanSpace ℝ (Fin 2)))
      (μE : Measure (EuclideanSpace ℝ (Fin 2)))
      (θ1 θ2 θ3 : ℝ)
      (E1 E2 E3 : Set (EuclideanSpace ℝ (Fin 2)))
      (E3fin : Finset (EuclideanSpace ℝ (Fin 2)))
      (μE3 : Measure (EuclideanSpace ℝ (Fin 2))),
      -- Frostman measure on Y
      IsDirectionFrostman δ τ (3 * C_Y * 2 ^ τ) ν ∧
      ν.support = Y ∧
      ν.support ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ y ∈ Y, ν {y} = ENNReal.ofReal (1 / (Y.ncard : ℝ))) ∧
      -- Uniform measure on representative set E
      E.Nonempty ∧
      IsProbabilityMeasure μE ∧
      μE.support ⊆ Pbar_param ∧
      (μE = ∑ p ∈ E, (1 / (E.card : ENNReal)) • Measure.dirac p) ∧
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos μE ≤
        ENNReal.ofReal (robust_projection.energyBoundConstant C_Pbar s κ0) ∧
      -- Cardinal equality for product density
      (E.card : ENNReal) = Nplane δ (Pbar_param) ∧
      -- Per-cube uniqueness
      (∀ Q ∈ dyadicCubesMeeting δ (Pbar_param),
        ∃! (p : EuclideanSpace ℝ (Fin 2)), p ∈ E ∧ p ∈ Q ∩ (Pbar_param)) ∧
      -- Three separated directions with nested sets
      E3 ⊆ E2 ∧ E2 ⊆ E1 ∧ E1 ⊆ (E : Set _) ∧
      E3.Nonempty ∧
      -- Retention: δ^rho_sel per step (equivalent to c/2)
      ENat.toENNReal E1.encard ≥ ENNReal.ofReal (δ ^ rho_sel) * (E.card : ENNReal) ∧
      ENat.toENNReal E2.encard ≥ ENNReal.ofReal (δ ^ rho_sel) * ENat.toENNReal E1.encard ∧
      ENat.toENNReal E3.encard ≥ ENNReal.ofReal (δ ^ rho_sel) * ENat.toENNReal E2.encard ∧
      ENat.toENNReal E3.encard ≥ ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal) ∧
      -- μE3 is uniform counting measure on E3
      IsProbabilityMeasure μE3 ∧
      μE3.support = E3 ∧
      (E3fin : Set _) = E3 ∧
      (μE3 = ∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard) • Measure.dirac p) ∧
      -- Normalized-subset energy bound
      (∀ θ ∈ ({θ1, θ2, θ3} : Set ℝ),
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE3) ≤
        ENNReal.ofReal (δ ^ (-6 * rho_sel)) *
          robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
            (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE)) ∧
      -- Absolute energy bound
      (∀ θ ∈ ({θ1, θ2, θ3} : Set ℝ),
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE3) ≤
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel)))) ∧
      -- Separation in terms of r = δ^rho_sep
      |θ1 - θ2| ≥ δ ^ rho_sep ∧
      |θ1 - θ3| ≥ δ ^ rho_sep ∧
      |θ2 - θ3| ≥ δ ^ rho_sep ∧
      θ1 < θ3 ∧ θ3 < θ2 ∧
      θ1 ∈ Set.Icc (0 : ℝ) 1 ∧
      θ2 ∈ Set.Icc (0 : ℝ) 1 ∧
      θ3 ∈ Set.Icc (0 : ℝ) 1 ∧
      -- Energy bounds for μE at selected directions (from Kaufman)
      (∀ y ∈ ({θ1, θ2, θ3} : Set ℝ),
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) μE) ≤
        ENNReal.ofReal (δ ^ (-q_bad))) ∧
      -- Projection bounds for E3
      (∀ y ∈ ({θ1, θ2, θ3} : Set ℝ),
        Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) E3) ≤
        ENNReal.ofReal (δ ^ (-(L * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal
            (dyadicCoveringNumber δ (Pbar_param))).toReal))) ∧
      -- Coordinate energy bounds
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
          ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1)) μE3) ≤
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) ∧
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
          ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1)) μE3) ≤
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) := by
  let C_ν : ℝ := 3 * C_Y * 2 ^ τ
  have hC_ν_pos : 0 < C_ν := by positivity

  -- Step 1: Frostman measure on Y
  rcases frostman_from_delta_set
      hδ_pos hδ_dyadic hδ_le_one (hκ_pos := hτ_pos) (by linarith) hC_Y_pos hY_grid hY_delta
    with ⟨ν, hν_frost, hν_supp_eq, hν_counting⟩
  letI : IsProbabilityMeasure ν := ⟨hν_frost.1⟩
  have hν_supp_Icc : ν.support ⊆ Set.Icc (0 : ℝ) 1 := hν_frost.2.1

  -- Step 2: Uniform measure + planar energy bound
  have hPbar_bdd : Bornology.IsBounded Pbar_param := hPbar_delta.1
  rcases robust_projection.regular_set_has_bounded_energy_with_card
      (hs := hs_pos) (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hκ_pos := hκ0_pos) (hκ_lt_s := hκ0_lt_s)
      (hP := hPbar_delta) (hP_bdd := hPbar_bdd) (hP_nonempty := hPbar_nonempty)
      (hP_lower := hPbar_size)
    with ⟨E, μE, hE_nonempty', hE_dense, hE_card, hE_unique, hμE_univ, hμE_supp, hμE_form, hE_bound⟩
  letI : IsProbabilityMeasure μE := ⟨hμE_univ⟩
  have hE_nonempty : E.Nonempty := hE_nonempty'
  have hμE_supp_eq : μE.support = (E : Set _) := by
    have hE_finite : (E : Set (EuclideanSpace ℝ (Fin 2))).Finite := Finset.finite_toSet E
    have hE_closed : IsClosed (E : Set (EuclideanSpace ℝ (Fin 2))) := Set.Finite.isClosed hE_finite
    have hμE_compl_E : μE ((E : Set _)ᶜ) = 0 := by
      rw [hμE_form, Measure.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro p hp
      have h_p_in_E : p ∈ (E : Set _) := by exact_mod_cast hp
      have h : ((1 / (E.card : ENNReal)) • Measure.dirac p) ((E : Set _)ᶜ) = 0 := by
        rw [Measure.smul_apply, Measure.dirac_apply]
        simp [h_p_in_E] <;> ring
      exact h
    have h1 : μE.support ⊆ (E : Set _) := by
      rw [MeasureTheory.Measure.support_eq_sInter]
      apply Set.sInter_subset_of_mem
      exact ⟨hE_closed, hμE_compl_E⟩
    have h2 : (E : Set _) ⊆ μE.support := by
      intro p hp
      have hE_card_pos : 0 < E.card := Finset.card_pos.mpr hE_nonempty
      have h3 : μE {p} > 0 := by
        have h4 : μE {p} = (1 / (E.card : ENNReal)) := by
          rw [hμE_form]
          have h_apply : (∑ q ∈ E, (1 / (E.card : ENNReal)) • Measure.dirac q) {p} =
              ∑ q ∈ E, (((1 / (E.card : ENNReal)) • Measure.dirac q) {p}) := by
            simpa [Measure.finsetSum_apply] using rfl
          rw [h_apply]
          rw [Finset.sum_eq_single_of_mem p hp]
          · have h_dirac : Measure.dirac p {p} = 1 := by simp
            simp [Measure.smul_apply, h_dirac] <;> ring
          · intro q _ hqp
            have h7 : Measure.dirac q {p} = 0 := by simp [Measure.dirac_apply, hqp]
            simp [Measure.smul_apply, h7]
        rw [h4]
        have h5 : (E.card : ENNReal) ≠ 0 := by exact_mod_cast hE_card_pos.ne'
        have h6 : (E.card : ENNReal) ≠ ⊤ := by simp
        exact ENNReal.div_pos one_ne_zero h6
      by_contra h4
      have h5 : ∃ (U : Set _), IsOpen U ∧ p ∈ U ∧ μE U = 0 := by
        have h6 := MeasureTheory.Measure.notMem_support_iff_exists.mp h4
        rcases h6 with ⟨U, hU_nhds, hU_zero⟩
        rcases mem_nhds_iff.mp hU_nhds with ⟨V, hV_sub, hV_open, hpV⟩
        have hV_zero : μE V = 0 := by
          have h : μE V ≤ μE U := measure_mono hV_sub
          rw [hU_zero] at h; exact le_zero_iff.mp h
        exact ⟨V, hV_open, hpV, hV_zero⟩
      rcases h5 with ⟨U, hU_open, hpU, hU_zero⟩
      have h6 : μE {p} ≤ μE U := measure_mono (fun x hx => hx ▸ hpU)
      rw [hU_zero] at h6
      have h7 : μE {p} = 0 := by simpa using h6
      rw [h7] at h3; simpa using h3
    exact Set.Subset.antisymm h1 h2
  have hE_sub_Pparam : (E : Set _) ⊆ Pbar_param :=
    hμE_supp_eq.symm.subset.trans hμE_supp
  have hE_bound' : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos μE ≤
      ENNReal.ofReal (robust_projection.energyBoundConstant C_Pbar s κ0) := hE_bound
  have hμE_Rbox : μE.support ⊆ {p : EuclideanSpace ℝ (Fin 2) | ∀ i, p i ∈ Set.Icc (-R) R} :=
    subset_trans hμE_supp_eq.subset (subset_trans hE_sub_Pparam hP_param_in_Rbox)

  -- Step 3: T_y point sets and multiplicity are direct inputs.

  -- Step 4: Exact Kaufman bad directions bridge
  let C_Kaufman_R : ℝ := 1 + (C_ν + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) *
      (1 + (2 * κ0) / (τ - 2 * κ0))
  have hC_Kaufman_R_pos : 0 < C_Kaufman_R := by positivity
  have hC_Kaufman_R_eq : C_Kaufman_R = 1 + (C_ν + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) *
      (1 + 2 * κ0 / (τ - 2 * κ0)) := by rfl
  let C_plan : ℝ := robust_projection.energyBoundConstant C_Pbar s κ0

  rcases robust_projection_main.kaufman_exact_for_endgame
      (C_Kaufman := C_Kaufman_R) (C_plan := C_plan) (rho_exc := q_bad)
      (E := E) (μE := μE) (Ybar := Y) (ν := ν)
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hkappa_pos := hκ0_pos) (hτ_gt_2κ0 := hτ_gt_2κ0)
      (hC_ν_pos := hC_ν_pos) (hC_Kaufman_pos := hC_Kaufman_R_pos)
      (hR_ge1 := hR_ge1) (hC_Kaufman_eq := hC_Kaufman_R_eq)
      (hc_pos := hc_pos) (hrho_exc_pos := hq_bad_pos)
      (h_absorb := h_kaufman_absorb)
      (hμE_supp := hμE_supp_eq)
      (hμE_support_bdd := hμE_Rbox)
      (hYbar_fin := hY_fin) (hν_supp_eq := hν_supp_eq)
      (hν_frost := hν_frost)
      (h_energy := hE_bound')
    with ⟨Θ_bad, hΘ_bad_eq, hΘ_bad_mass⟩

  -- Convert to full-set bad mass
  let E_y : ℝ → ENNReal := fun y =>
    robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) μE)
  let threshold : ENNReal := ENNReal.ofReal (δ ^ (-q_bad))
  have h_set_eq : {y : ℝ | E_y y > threshold} ∩ Y = Θ_bad := by
    rw [hΘ_bad_eq]; ext y; dsimp only [E_y, threshold]
    simp [Set.mem_inter_iff, and_comm] <;> exact Iff.rfl
  have h_rest_null : ν ({y : ℝ | E_y y > threshold} \ Y) = 0 := by
    have h_sub : ({y : ℝ | E_y y > threshold} \ Y) ⊆ (ν.support)ᶜ := by
      intro z hz; have h_notY : z ∉ Y := hz.2
      have h_supp_eq : ν.support = Y := hν_supp_eq
      rw [h_supp_eq]; exact h_notY
    have h : ν ({y : ℝ | E_y y > threshold} \ Y) ≤ ν ((ν.support)ᶜ) := measure_mono h_sub
    have h2 : ν ((ν.support)ᶜ) = 0 := ν.measure_compl_support
    rw [h2] at h; exact le_zero_iff.mp h
  have hΘ_bad' : ν {y : ℝ | E_y y > threshold} ≤ ENNReal.ofReal (c / 8) := by
    set A : Set ℝ := {y : ℝ | E_y y > threshold} with hA_def
    have h_union : A = (A ∩ Y) ∪ (A \ Y) := by
      ext x; simp [Set.mem_sdiff] <;> by_cases h : x ∈ Y <;> simp [h] <;> tauto
    have h2 : A ∩ Y = Θ_bad := h_set_eq
    have h5 : ν (A \ Y) = 0 := h_rest_null
    have h6 : ν A = ν Θ_bad := by
      have h7 : ν A ≤ ν (A ∩ Y) + ν (A \ Y) := measure_le_inter_add_sdiff ν A Y
      rw [h5] at h7
      have h9 : ν A ≤ ν (A ∩ Y) := by simpa using h7
      have h10 : ν (A ∩ Y) ≤ ν A := measure_mono (by simp)
      have h11 : ν A = ν (A ∩ Y) := le_antisymm h9 h10
      rw [h11, h2]
    rw [h6]; exact hΘ_bad_mass

  -- Step 5: Define r = δ^rho_sep and neighborhood mass
  let r : ℝ := δ ^ rho_sep
  have hr_pos : 0 < r := by positivity
  have hr_lt_one : r < 1 := by
    have h1 : 0 < δ := hδ_pos
    have h2 : δ < 1 := hδ_lt_one
    have h3 : 0 < rho_sep := hrho_sep_pos
    have h4 : δ ^ rho_sep < 1 := Real.rpow_lt_one (le_of_lt h1) h2 h3
    simpa [r] using h4
  have hr_ge_delta : δ ≤ r := by
    have hδ_le_one : δ ≤ 1 := by linarith
    have h_rpow : δ ^ (1 : ℝ) ≤ δ ^ rho_sep :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one hrho_sep_le_one
    have h1 : δ ^ (1 : ℝ) = δ := Real.rpow_one δ
    have h2 : r = δ ^ rho_sep := rfl
    rw [h1] at h_rpow
    rw [h2]
    exact h_rpow
  have h_small_neighborhood' : 2 * C_ν * r ^ τ ≤ c / 8 := by
    have h_eq : r = δ ^ rho_sep := rfl
    rw [h_eq]
    exact h_small_neighborhood

  have h_neighborhoods_general : ∀ (Ω : Set ℝ), Ω.encard ≤ 2 →
      ν (⋃ y ∈ Ω, Metric.ball y r) ≤ ENNReal.ofReal (c / 8) := by
    intro Ω hΩ_encard
    have hΩ_fin : Ω.Finite := by exact finite_of_encard_le_coe hΩ_encard
    let Ωf : Finset ℝ := hΩ_fin.toFinset
    have hΩf_eq : (Ωf : Set ℝ) = Ω := Set.Finite.coe_toFinset hΩ_fin
    have hΩf_card_le_2 : Ωf.card ≤ 2 := by
      have h4 : Ω.encard ≤ 2 := hΩ_encard
      have h5 : Ω.encard = ↑Ω.ncard := Set.Finite.encard_eq_coe hΩ_fin
      rw [h5] at h4
      have h6 : (Ω.ncard : ENat) ≤ 2 := h4
      have h7 : Ω.ncard ≤ 2 := by exact_mod_cast h6
      have h8 : Ωf.card = Ω.ncard := by exact Eq.symm (ncard_eq_toFinset_card Ω hΩ_fin)
      rw [h8]; exact h7
    have h_ball_mass : ∀ (y : ℝ), ν (Metric.ball y r) ≤ ENNReal.ofReal (C_ν * r ^ τ) := by
      intro y
      have h1 : Metric.ball y r ⊆ Set.Icc (y - r) (y + r) := by
        intro x hx
        have h4 : dist x y < r := hx
        have h5 : |x - y| < r := by simpa [Real.dist_eq] using h4
        have h6 : y - r ≤ x := by linarith [abs_lt.mp h5]
        have h7 : x ≤ y + r := by linarith [abs_lt.mp h5]
        exact ⟨h6, h7⟩
      have h2 : ν (Set.Icc (y - r) (y + r)) ≤ ENNReal.ofReal (C_ν * r ^ τ) :=
        hν_frost.2.2 y r hr_ge_delta (by linarith)
      exact (measure_mono h1).trans h2
    have h_union : ν (⋃ y ∈ Ω, Metric.ball y r) ≤ ∑ y ∈ Ωf, ν (Metric.ball y r) := by
      rw [show (⋃ y ∈ Ω, Metric.ball y r) = ⋃ y ∈ (Ωf : Set ℝ), Metric.ball y r by rw [hΩf_eq]]
      exact measure_biUnion_finset_le Ωf fun i => Metric.ball i r
    have h_sum : ∑ y ∈ Ωf, ν (Metric.ball y r) ≤ ∑ y ∈ Ωf, ENNReal.ofReal (C_ν * r ^ τ) := by
      apply Finset.sum_le_sum; intro y _; exact h_ball_mass y
    have h3 : ∑ y ∈ Ωf, ENNReal.ofReal (C_ν * r ^ τ) =
        (Ωf.card : ENNReal) * ENNReal.ofReal (C_ν * r ^ τ) := by
      rw [Finset.sum_const] <;> ring
    have h4 : (Ωf.card : ENNReal) * ENNReal.ofReal (C_ν * r ^ τ) ≤
        ENNReal.ofReal (2 * C_ν * r ^ τ) := by
      have h5 : (Ωf.card : ENNReal) ≤ 2 := by exact_mod_cast hΩf_card_le_2
      have h6 : (2 : ENNReal) * ENNReal.ofReal (C_ν * r ^ τ) =
          ENNReal.ofReal (2 * C_ν * r ^ τ) := by
        rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num)] <;> ring_nf
      have h_pos : 0 ≤ ENNReal.ofReal (C_ν * r ^ τ) := by positivity
      have h7 : (Ωf.card : ENNReal) * ENNReal.ofReal (C_ν * r ^ τ) ≤
          (2 : ENNReal) * ENNReal.ofReal (C_ν * r ^ τ) :=
        mul_le_mul_of_nonneg_right h5 h_pos
      rw [h6] at h7
      exact h7
    have h7 : ENNReal.ofReal (2 * C_ν * r ^ τ) ≤ ENNReal.ofReal (c / 8) :=
      ENNReal.ofReal_le_ofReal h_small_neighborhood'
    calc ν (⋃ y ∈ Ω, Metric.ball y r)
      ≤ ∑ y ∈ Ωf, ν (Metric.ball y r) := h_union
    _ ≤ ∑ y ∈ Ωf, ENNReal.ofReal (C_ν * r ^ τ) := h_sum
    _ = (Ωf.card : ENNReal) * ENNReal.ofReal (C_ν * r ^ τ) := h3
    _ ≤ ENNReal.ofReal (2 * C_ν * r ^ τ) := h4
    _ ≤ ENNReal.ofReal (c / 8) := h7

  -- Step 6: Threefold recursive selection with exact constants
  rcases threefold_recursive_selection
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hkappa_pos := hκ0_pos)
      (hc_pos := hc_pos) (hL_pos := hL_pos) (hη_pos := hη_pos)
      (hτ_pos := hτ_pos) (hC_ν_pos := hC_ν_pos) (hr_pos := hr_pos)
      (q_bad := q_bad) (hq_bad_pos := hq_bad_pos)
      (hT_y_sub := hT_y_points_sub)
      (hYbar_fin := hY_fin) (hYbar_nonempty := hY_nonempty)
      (hν_counting := hν_counting) (hν_supp := hν_supp_eq)
      (hν_frost := hν_frost)
      (h_multiplicity := h_multiplicity_points)
      (h_proj_bound := h_proj_bound)
      (hΘ_bad := hΘ_bad')
      (hE_sub := hE_sub_Pparam) (hE_nonempty := hE_nonempty)
      (h_neighborhoods_general := h_neighborhoods_general)
    with ⟨θ1, θ2, θ3, E1, E2, E3,
      hE3_sub_E2, hE2_sub_E1, hE1_sub_E, hE3_nonempty,
      hE1_card, hE2_card, hE3_card,
      h_sep12, h_sep13, h_sep23,
      h_ord13, h_ord32,
      hθ1_in_Y, hθ2_in_Y, hθ3_in_Y,
      h_energy_dirs, h_proj_dirs⟩

  -- Convert c/2 retention to δ^rho_sel retention
  have h_c2_ge_drhosel : ENNReal.ofReal (δ ^ rho_sel) ≤ ENNReal.ofReal (c / 2) :=
    ENNReal.ofReal_le_ofReal hδ_rho_sel_le_c2
  have hE1_card' : ENat.toENNReal E1.encard ≥ ENNReal.ofReal (δ ^ rho_sel) * (E.card : ENNReal) := by
    have h : ENNReal.ofReal (δ ^ rho_sel) * (E.card : ENNReal) ≤ ENNReal.ofReal (c / 2) * (E.card : ENNReal) :=
      mul_le_mul_of_nonneg_right h_c2_ge_drhosel bot_le
    exact le_trans h hE1_card
  have hE2_card' : ENat.toENNReal E2.encard ≥ ENNReal.ofReal (δ ^ rho_sel) * ENat.toENNReal E1.encard := by
    have h : ENNReal.ofReal (δ ^ rho_sel) * ENat.toENNReal E1.encard ≤ ENNReal.ofReal (c / 2) * ENat.toENNReal E1.encard :=
      mul_le_mul_of_nonneg_right h_c2_ge_drhosel bot_le
    exact le_trans h hE2_card
  have hE3_card' : ENat.toENNReal E3.encard ≥ ENNReal.ofReal (δ ^ rho_sel) * ENat.toENNReal E2.encard := by
    have h : ENNReal.ofReal (δ ^ rho_sel) * ENat.toENNReal E2.encard ≤ ENNReal.ofReal (c / 2) * ENat.toENNReal E2.encard :=
      mul_le_mul_of_nonneg_right h_c2_ge_drhosel bot_le
    exact le_trans h hE3_card
  have h_drs_nonneg : 0 ≤ δ ^ rho_sel := (Real.rpow_pos_of_pos hδ_pos rho_sel).le
  have h_drs2_nonneg : 0 ≤ δ ^ (2 * rho_sel) := (Real.rpow_pos_of_pos hδ_pos (2 * rho_sel)).le
  have h_rpow2 : (δ ^ rho_sel) * (δ ^ rho_sel) = δ ^ (2 * rho_sel) := by
    have h1 : δ ^ rho_sel * δ ^ rho_sel = δ ^ (rho_sel + rho_sel) := by
      rw [← Real.rpow_add hδ_pos]
    have h2 : rho_sel + rho_sel = 2 * rho_sel := by ring
    rw [h1, h2]
  have h_rpow3 : (δ ^ (2 * rho_sel)) * (δ ^ rho_sel) = δ ^ (3 * rho_sel) := by
    have h1 : δ ^ (2 * rho_sel) * δ ^ rho_sel = δ ^ (2 * rho_sel + rho_sel) := by
      rw [← Real.rpow_add hδ_pos]
    have h2 : 2 * rho_sel + rho_sel = 3 * rho_sel := by ring
    rw [h1, h2]
  have h_mul2 : ENNReal.ofReal (δ ^ rho_sel) * ENNReal.ofReal (δ ^ rho_sel) =
      ENNReal.ofReal (δ ^ (2 * rho_sel)) := by
    have h : ENNReal.ofReal (δ ^ rho_sel) * ENNReal.ofReal (δ ^ rho_sel) =
        ENNReal.ofReal ((δ ^ rho_sel) * (δ ^ rho_sel)) := by
      rw [ENNReal.ofReal_mul h_drs_nonneg]
    rw [h, h_rpow2]
  have h_mul3 : ENNReal.ofReal (δ ^ (2 * rho_sel)) * ENNReal.ofReal (δ ^ rho_sel) =
      ENNReal.ofReal (δ ^ (3 * rho_sel)) := by
    have h : ENNReal.ofReal (δ ^ (2 * rho_sel)) * ENNReal.ofReal (δ ^ rho_sel) =
        ENNReal.ofReal ((δ ^ (2 * rho_sel)) * (δ ^ rho_sel)) := by
      rw [← ENNReal.ofReal_mul h_drs2_nonneg]
    rw [h, h_rpow3]
  have hE3_3rhosel : ENat.toENNReal E3.encard ≥
      ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal) :=
    calc ENat.toENNReal E3.encard
      ≥ ENNReal.ofReal (δ ^ rho_sel) * ENat.toENNReal E2.encard := hE3_card'
    _ ≥ ENNReal.ofReal (δ ^ rho_sel) * (ENNReal.ofReal (δ ^ rho_sel) * ENat.toENNReal E1.encard) :=
      mul_le_mul_of_nonneg_left hE2_card' bot_le
    _ = (ENNReal.ofReal (δ ^ rho_sel) * ENNReal.ofReal (δ ^ rho_sel)) * ENat.toENNReal E1.encard := by
      rw [mul_assoc]
    _ = ENNReal.ofReal (δ ^ (2 * rho_sel)) * ENat.toENNReal E1.encard := by rw [h_mul2]
    _ ≥ ENNReal.ofReal (δ ^ (2 * rho_sel)) * (ENNReal.ofReal (δ ^ rho_sel) * (E.card : ENNReal)) :=
      mul_le_mul_of_nonneg_left hE1_card' bot_le
    _ = (ENNReal.ofReal (δ ^ (2 * rho_sel)) * ENNReal.ofReal (δ ^ rho_sel)) * (E.card : ENNReal) := by
      rw [mul_assoc]
    _ = ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal) := by rw [h_mul3]

  -- Convert separation r to δ^rho_sep
  have hr_eq : r = δ ^ rho_sep := by rfl
  have h_sep12' : |θ1 - θ2| ≥ δ ^ rho_sep := by rw [← hr_eq]; exact h_sep12
  have h_sep13' : |θ1 - θ3| ≥ δ ^ rho_sep := by rw [← hr_eq]; exact h_sep13
  have h_sep23' : |θ2 - θ3| ≥ δ ^ rho_sep := by rw [← hr_eq]; exact h_sep23

  -- Step 7: Construct μE3
  have hE3_sub_E : E3 ⊆ (E : Set _) :=
    Set.Subset.trans hE3_sub_E2 (Set.Subset.trans hE2_sub_E1 hE1_sub_E)
  have hE3_finite : E3.Finite := Set.Finite.subset E.finite_toSet hE3_sub_E
  let E3fin : Finset (EuclideanSpace ℝ (Fin 2)) := Set.Finite.toFinset hE3_finite
  have hE3fin_coe : (E3fin : Set _) = E3 := Set.Finite.coe_toFinset hE3_finite
  let μE3 : Measure (EuclideanSpace ℝ (Fin 2)) :=
    ∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard : ENNReal) • Measure.dirac p

  -- Direction bounds
  have hθ1_in_Icc : θ1 ∈ Set.Icc (0 : ℝ) 1 := by
    have h : θ1 ∈ productLikeUnitGrid δ := hY_grid hθ1_in_Y
    exact ⟨h.2.1, h.2.2⟩
  have hθ2_in_Icc : θ2 ∈ Set.Icc (0 : ℝ) 1 := by
    have h : θ2 ∈ productLikeUnitGrid δ := hY_grid hθ2_in_Y
    exact ⟨h.2.1, h.2.2⟩
  have hθ3_in_Icc : θ3 ∈ Set.Icc (0 : ℝ) 1 := by
    have h : θ3 ∈ productLikeUnitGrid δ := hY_grid hθ3_in_Y
    exact ⟨h.2.1, h.2.2⟩

  -- E3fin cardinality facts (needed before energy bounds)
  let E3fin_set : Set (EuclideanSpace ℝ (Fin 2)) := E3fin
  have hE3fin_nonempty : E3fin.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]
    exact hE3_nonempty
  have hE3fin_card_pos : 0 < E3fin.card := Finset.card_pos.mpr hE3fin_nonempty
  have h_card_eq : ENat.toENNReal E3.encard = (E3fin.card : ENNReal) := by
    have h1 : E3 = E3fin_set := hE3fin_coe.symm
    rw [h1]
    have h2 : E3fin_set.encard = ↑E3fin.card := by
      simp [E3fin_set, Set.Finite.coe_toFinset]
      <;> rfl
    rw [h2]
    <;> norm_cast
  have h_weight_ne_zero : (ENat.toENNReal E3.encard) ≠ 0 := by
    rw [h_card_eq]
    exact_mod_cast hE3fin_card_pos.ne'
  have h_weight_ne_top : (ENat.toENNReal E3.encard) ≠ ⊤ := by
    rw [h_card_eq] <;> simp

  -- Energy bounds
  -- Identify μE and μE3 with uniformMeasureOn
  have hμE_uniform : μE = uniformMeasureOn E := by
    rw [hμE_form]
    exact (uniform_measure_eq_dirac_sum E hE_nonempty).symm
  have hμE3_uniform : μE3 = uniformMeasureOn E3fin := by
    exact muE3_eq_uniform E3fin hE3fin_nonempty hE3fin_coe
  have hE3fin_sub_E : E3fin ⊆ E := by
    intro x hx
    have h_x_in_E3 : x ∈ E3 := by
      have h : x ∈ (E3fin : Set _) := by exact_mod_cast hx
      rw [hE3fin_coe] at h
      exact h
    have h_x_in_E_set : x ∈ (E : Set _) := hE3_sub_E h_x_in_E3
    exact_mod_cast h_x_in_E_set
  have h_retention : (E3fin.card : ENNReal) ≥
      ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal) := by
    have h1 : ENat.toENNReal E3.encard ≥ ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal) := hE3_3rhosel
    rw [h_card_eq] at h1
    exact h1

  -- Energy bounds using helper lemma (avoids context-induced timeouts)
  rcases endgame_projected_energy_bounds
      δ κ0 rho_sel q_bad hδ_pos hκ0_pos hrho_sel_pos hq_bad_pos
      E E3fin hE3fin_sub_E hE3fin_nonempty μE μE3
      hμE_uniform hμE3_uniform h_retention θ1 θ2 θ3 h_energy_dirs
    with ⟨h_energy_E3, h_energy_E3_abs⟩

  have hμE3_univ : μE3 Set.univ = 1 := by
    rw [show μE3 = ∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard : ENNReal) • Measure.dirac p from rfl]
    have h_sum : (∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard : ENNReal) • Measure.dirac p) Set.univ =
        ∑ p ∈ E3fin, ((1 / ENat.toENNReal E3.encard : ENNReal) • Measure.dirac p) Set.univ := by
      rw [Measure.finsetSum_apply]
    rw [h_sum]
    have h_each : ∀ p ∈ E3fin, ((1 / ENat.toENNReal E3.encard : ENNReal) • Measure.dirac p) Set.univ =
        (1 / ENat.toENNReal E3.encard) := by
      intro p _
      rw [Measure.smul_apply, Measure.dirac_apply] <;> simp
    rw [Finset.sum_congr rfl h_each]
    have h_sum_const : ∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard) =
        (E3fin.card : ENNReal) * (1 / ENat.toENNReal E3.encard) := by
      rw [Finset.sum_const]
      rw [nsmul_eq_mul E3fin.card (1 / ENat.toENNReal E3.encard)]
      <;> rfl
    rw [h_sum_const]
    have h_mul : (E3fin.card : ENNReal) * (1 / ENat.toENNReal E3.encard) = 1 := by
      rw [h_card_eq]
      exact ENNReal.mul_div_cancel' (by exact_mod_cast hE3fin_card_pos.ne') (by simp)
    exact h_mul
  have hμE3_prob : IsProbabilityMeasure μE3 := ⟨hμE3_univ⟩

  have hμE3_supp : μE3.support = E3 := by
    have hE3fin_finite : (E3fin : Set (EuclideanSpace ℝ (Fin 2))).Finite := Finset.finite_toSet E3fin
    have hE3fin_closed : IsClosed (E3fin : Set (EuclideanSpace ℝ (Fin 2))) := Set.Finite.isClosed hE3fin_finite
    have hμE3_compl_E3fin : μE3 ((E3fin : Set _)ᶜ) = 0 := by
      rw [show μE3 = ∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard : ENNReal) • Measure.dirac p from rfl]
      rw [Measure.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro p hp
      have h_p_in : p ∈ (E3fin : Set _) := by exact_mod_cast hp
      have h : ((1 / ENat.toENNReal E3.encard : ENNReal) • Measure.dirac p) ((E3fin : Set _)ᶜ) = 0 := by
        rw [Measure.smul_apply, Measure.dirac_apply]
        simp [h_p_in] <;> ring
      exact h
    have h1 : μE3.support ⊆ (E3fin : Set _) := by
      rw [MeasureTheory.Measure.support_eq_sInter]
      apply Set.sInter_subset_of_mem
      exact ⟨hE3fin_closed, hμE3_compl_E3fin⟩
    have h2 : (E3fin : Set _) ⊆ μE3.support := by
      intro p hp
      have h3 : μE3 {p} > 0 := by
        have h4 : μE3 {p} = (1 / ENat.toENNReal E3.encard) := by
          rw [show μE3 = ∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard : ENNReal) • Measure.dirac p from rfl]
          have h_apply : (∑ q ∈ E3fin, (1 / ENat.toENNReal E3.encard : ENNReal) • Measure.dirac q) {p} =
              ∑ q ∈ E3fin, (((1 / ENat.toENNReal E3.encard : ENNReal) • Measure.dirac q) {p}) := by
            simpa [Measure.finsetSum_apply] using rfl
          rw [h_apply]
          rw [Finset.sum_eq_single_of_mem p hp]
          · have h_dirac : Measure.dirac p {p} = 1 := by simp
            simp [Measure.smul_apply, h_dirac] <;> ring
          · intro q _ hqp
            have h7 : Measure.dirac q {p} = 0 := by simp [Measure.dirac_apply, hqp]
            simp [Measure.smul_apply, h7]
        rw [h4]
        exact ENNReal.div_pos one_ne_zero h_weight_ne_top
      by_contra h4
      have h5 : ∃ (U : Set _), IsOpen U ∧ p ∈ U ∧ μE3 U = 0 := by
        have h6 := MeasureTheory.Measure.notMem_support_iff_exists.mp h4
        rcases h6 with ⟨U, hU_nhds, hU_zero⟩
        rcases mem_nhds_iff.mp hU_nhds with ⟨V, hV_sub, hV_open, hpV⟩
        have hV_zero : μE3 V = 0 := by
          have h : μE3 V ≤ μE3 U := measure_mono hV_sub
          rw [hU_zero] at h; exact le_zero_iff.mp h
        exact ⟨V, hV_open, hpV, hV_zero⟩
      rcases h5 with ⟨U, hU_open, hpU, hU_zero⟩
      have h6 : μE3 {p} ≤ μE3 U := measure_mono (fun x hx => hx ▸ hpU)
      rw [hU_zero] at h6
      have h7 : μE3 {p} = 0 := by simpa using h6
      rw [h7] at h3; simpa using h3
    have h_supp_eq_fin : μE3.support = (E3fin : Set _) := Set.Subset.antisymm h1 h2
    rw [h_supp_eq_fin, hE3fin_coe]

  -- Coordinate energy bounds
  let b3 : ℝ := (θ3 - θ1) / (θ2 - θ1)
  let a3 : ℝ := (θ2 - θ3) / (θ2 - θ1)

  have h_abs_E2 : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ2 + p 1) μE3) ≤
    ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel))) :=
    h_energy_E3_abs θ2 (by simp)
  have h_abs_E1 : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ1 + p 1) μE3) ≤
    ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel))) :=
    h_energy_E3_abs θ1 (by simp)

  have h_energy_coord0 : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
        b3 * (p 0 * θ2 + p 1)) μE3) ≤
      ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) :=
    coordinate_energy_b3_bound hδ_pos hδ_lt_one hκ0_pos
      hrho_sel_pos hrho_sep_pos hrho_sep_le_one hq_bad_pos
      (hθ1_in := hθ1_in_Icc) (hθ2_in := hθ2_in_Icc) (hθ3_in := hθ3_in_Icc)
      h_ord13 h_ord32 h_sep13' h_sep23' h_abs_E2 h_abs_E1

  have h_energy_coord1 : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
        a3 * (p 0 * θ1 + p 1)) μE3) ≤
      ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) :=
    coordinate_energy_a3_bound hδ_pos hδ_lt_one hκ0_pos
      hrho_sel_pos hrho_sep_pos hrho_sep_le_one hq_bad_pos
      (hθ1_in := hθ1_in_Icc) (hθ2_in := hθ2_in_Icc) (hθ3_in := hθ3_in_Icc)
      h_ord13 h_ord32 h_sep13' h_sep23' h_abs_E2 h_abs_E1

  exact ⟨ν, E, μE, θ1, θ2, θ3, E1, E2, E3, E3fin, μE3,
    hν_frost, hν_supp_eq, hν_supp_Icc, hν_counting,
    hE_nonempty, inferInstance, hμE_supp, hμE_form, hE_bound', hE_card, hE_unique,
    hE3_sub_E2, hE2_sub_E1, hE1_sub_E,
    hE3_nonempty, hE1_card', hE2_card', hE3_card', hE3_3rhosel,
    hμE3_prob, hμE3_supp, hE3fin_coe, rfl,
    h_energy_E3, h_energy_E3_abs,
    h_sep12', h_sep13', h_sep23',
    h_ord13, h_ord32,
    hθ1_in_Icc, hθ2_in_Icc, hθ3_in_Icc,
    h_energy_dirs, h_proj_dirs,
    h_energy_coord0, h_energy_coord1⟩

end ProductLikeIncidence.ProductReduction
