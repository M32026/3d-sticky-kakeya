import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyPBase
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountGeneral
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiScaleArithmetic
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalADFromSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SubfamilyShadingExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakenLoss
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HardRegimeHelper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HAvgCombination
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HAvgExponentArithmetic
import Mathlib.Tactic

/-!
# Phase 1: Sticky data → Z subshading + PropertyP with small ε₃

This is the Phase 1 lemma for the every-scale nesting. Given sticky data at
coarse scale `rho_coarse`, produce:
- Z subshading of Y with midLoss extremality and CWA
- Z.union ⊆ croppedCoarseShading.union
- PropertyP with small ε₃ (for WZ1 arithmetic compatibility)

## Status

hZ_ext, hZ_cwa, and hpropP are all proved. hpropP uses the already-proved
`pureWz2_close_direction_count_general` (not harbor's robust close count).
Requires 7 additional arithmetic hypotheses (sigma bounds, loss ordering,
cell fullness, and h_avg exponent bound).

The slack condition `hslack` is required for the polylogarithmic mass
retention factor to be absorbed by the loss gap `midLoss - inputLoss`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- Phase 1: sticky data → Z + PropertyP with small ε₃.

The `hslack` hypothesis ensures the polylog refinement fraction is
absorbed by the loss gap: `(log(1/δ))^logExponent · δ^midLoss ≤ δ^inputLoss`.

The `stickyLoss` parameter is the loss at which the sticky data's coarse
extremality holds. The proved parts (hZ_ext, hZ_cwa) are independent of
`stickyLoss`; they use `hY_ext` and mass retention. -/
lemma phase1_sticky_to_Z_and_propertyP_certified
    {delta sigma inputLoss midLoss stickyLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    {rho_coarse : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      (sourceShading := Y) rho_coarse logExponent)
    (hY_ext : WZ2PaperCroppedIsExtremal sigma inputLoss F Y)
    (hY_cwa : WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-inputLoss)))
    (hmidLoss_pos : 0 < midLoss)
    (hinputLoss_le_mid : inputLoss ≤ midLoss)
    (hL_small : rho_coarse.1 ≤ 1 / 10000)
    (hslack : (wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
               Kakeya.realRpowENN delta midLoss ≤
               Kakeya.realRpowENN delta inputLoss)
    -- Arithmetic hypotheses for PropertyP construction
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hinputLoss_pos : 0 < inputLoss)
    (hinputLoss_le_sticky : inputLoss ≤ stickyLoss)
    (hstickyLoss_small : 6 * stickyLoss < sigma + 2 * inputLoss)
    (hL_le_C : rho_coarse.1 ≤ (3 : ℝ) ^ (-(20 / sigma)))
    (h_havg_bound : (PureWZ2.h_avg_m_val sigma inputLoss rho_coarse.1 : ℝ) *
        rho_coarse.1 ^ (sigma - 3 * stickyLoss) < 1 / 8) :
    ∃ (Z : WZ1PaperTubeShading F)
      (hZ_sub : PaperIsSubshading Z Y)
      (hZ_ext : WZ2PaperCroppedIsExtremal sigma midLoss F Z)
      (hZ_cwa : WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-midLoss)))
      (epsilon₁ epsilon₃ : ℝ)
      (propP : PureWZ2PropertyPData
        (sigma := sigma)
        (coarseShading := sticky.croppedCoarseShading)
        (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
        (tau := rho_coarse.1 * Real.sqrt 3))
      (hepsilon₁_def : epsilon₁ = (sigma - 2 * inputLoss) / 20)
      (hepsilon₁_pos : 0 < epsilon₁)
      (hepsilon₁_lt : epsilon₁ < 1 / 20)
      (hepsilon₃_pos : 0 < epsilon₃)
      (hepsilon₃_def : epsilon₃ = 1 - 2 * epsilon₁)
      (hepsilon_sum : epsilon₁ + epsilon₃ < 1)
      (htau_pos : 0 < rho_coarse.1 * Real.sqrt 3)
      (hrho_le_tau : rho_coarse.1 ≤ rho_coarse.1 * Real.sqrt 3)
      (htau_sq : (rho_coarse.1 * Real.sqrt 3) ^ 2 ≤ 4 * rho_coarse.1)
      (htau_le_one : rho_coarse.1 * Real.sqrt 3 ≤ 1)
      (hpropertyThree_eq : propP.propertyThree = propP.propertyOne)
      (hZ_sub_coarse : Z.union ⊆ sticky.croppedCoarseShading.union), True := by
  let L : ℝ := rho_coarse.1
  let tau : ℝ := L * Real.sqrt 3

  -- Extend sticky.refined to full family using existing extendShading
  let Z : WZ1PaperTubeShading F :=
    extendShading sticky.selected sticky.refined

  -- Z ⊆ Y via sticky.subshading + extension
  have hZ_sub : PaperIsSubshading Z Y := by
    intro i
    by_cases h : ∃ j : Fin sticky.selected.family.card, sticky.selected.embedding j = i
    · rcases h with ⟨j, hj⟩
      have hcar : Z.carrier i = sticky.refined.carrier j := by
        rw [← hj]
        exact extendShading_carrier_mem (sub := sticky.selected) (refined := sticky.refined) (j := j)
      rw [hcar]
      have hsub : sticky.refined.carrier j ⊆ Y.carrier (sticky.selected.embedding j) := sticky.subshading j
      rw [hj] at hsub
      exact hsub
    · have hcar : Z.carrier i = ∅ := extendShading_carrier_empty (h := h)
      rw [hcar]
      exact Set.empty_subset _

  -- Z.union = refined.union, then subset of coarse shading
  have hZ_union_eq : Z.union = sticky.refined.union :=
    extendShading_union sticky.selected sticky.refined
  have hZ_sub_coarse : Z.union ⊆ sticky.croppedCoarseShading.union := by
    rw [hZ_union_eq]
    exact PureWZ2.refined_union_subset_coarse sticky

  -- Z is cubical: selected indices inherit refined cubicality; rest are empty
  have hZ_cubical : WZ1PaperIsCubicalShading Z := by
    intro i p hp
    by_cases h : ∃ j : Fin sticky.selected.family.card, sticky.selected.embedding j = i
    · rcases h with ⟨j, hj⟩
      have hcar : Z.carrier i = sticky.refined.carrier j := by
        rw [← hj]
        exact extendShading_carrier_mem (sub := sticky.selected) (refined := sticky.refined) (j := j)
      rw [hcar] at hp
      have hcube := sticky.refined_cubical j p hp
      rw [hcar]
      exact hcube
    · have hcar : Z.carrier i = ∅ := extendShading_carrier_empty (h := h)
      rw [hcar] at hp
      contradiction

  -- Z.mass = refined.mass
  have hmass_eq : Z.mass = sticky.refined.mass :=
    extendShading_mass sticky.selected sticky.refined

  -- Mass retention transfers: fraction * Y.mass ≤ Z.mass
  have hmass_retention : (wz2PaperPureRefinementFraction delta logExponent) * Y.mass ≤ Z.mass := by
    calc (wz2PaperPureRefinementFraction delta logExponent) * Y.mass
      ≤ sticky.refined.mass := sticky.retained_mass
    _ = Z.mass := hmass_eq.symm

  -- delta < 1 from hL_small + delta ≤ rho_coarse.1
  have hdelta_lt_one : delta < 1 := by
    have h1 : delta ≤ rho_coarse.1 := rho_coarse.2.1
    linarith
  have hdelta_pos : 0 < delta := hY_ext.delta_pos

  -- Refinement fraction is positive and finite
  have hlog_pos : 0 < Real.log (1 / delta) := by
    have h1 : 1 < 1 / delta := by
      apply one_lt_one_div
      <;> linarith
    exact Real.log_pos h1
  have hlog_ennreal_pos : 0 < ENNReal.ofReal (Real.log (1 / delta)) :=
    ENNReal.ofReal_pos.mpr hlog_pos
  have hlog_ennreal_ne_top : ENNReal.ofReal (Real.log (1 / delta)) ≠ ⊤ := by
    simp
  let base : ENNReal := (ENNReal.ofReal (Real.log (1 / delta)))⁻¹
  have hbase_pos : 0 < base := ENNReal.inv_pos.mpr hlog_ennreal_ne_top
  have hbase_ne_top : base ≠ ⊤ := ENNReal.inv_ne_top.mpr hlog_ennreal_pos.ne'
  have hfraction_pos : 0 < wz2PaperPureRefinementFraction delta logExponent := by
    have hne : (ENNReal.ofReal (Real.log (1 / delta)))⁻¹ ≠ 0 := hbase_pos.ne'
    have h : (ENNReal.ofReal (Real.log (1 / delta)))⁻¹ ^ logExponent ≠ 0 :=
      pow_ne_zero logExponent hne
    exact h.bot_lt
  have hfraction_ne_top : wz2PaperPureRefinementFraction delta logExponent ≠ ⊤ := by
    have h_main : ∀ n : ℕ, base ^ n ≠ ⊤ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have h1 : base ^ (n + 1) = base ^ n * base := pow_succ base n
        rw [h1]
        intro htop
        have h2 : (base ^ n ≠ 0 ∧ base = ⊤) ∨ (base ^ n = ⊤ ∧ base ≠ 0) :=
          (ENNReal.mul_eq_top).mp htop
        rcases h2 with ⟨_, h3⟩ | ⟨h4, _⟩
        · exact hbase_ne_top h3
        · exact ih h4
    exact h_main logExponent

  let K : ENNReal := (wz2PaperPureRefinementFraction delta logExponent)⁻¹
  have hK_pos : 0 < K := ENNReal.inv_pos.mpr hfraction_ne_top
  have hK_ne_top : K ≠ ⊤ := ENNReal.inv_ne_top.mpr hfraction_pos.ne'
  have hK_inv_eq : K⁻¹ = wz2PaperPureRefinementFraction delta logExponent := by
    dsimp only [K]
    exact inv_inv (wz2PaperPureRefinementFraction delta logExponent)
  have hmass' : K⁻¹ * Y.mass ≤ Z.mass := by
    rw [hK_inv_eq]
    exact hmass_retention

  -- hZ_ext via transfer_cropped_extremal_to_subshading
  have hZ_ext : WZ2PaperCroppedIsExtremal sigma midLoss F Z :=
    transfer_cropped_extremal_to_subshading
      K hK_pos hK_ne_top
      hY_ext hZ_sub hmass' hZ_cubical
      hinputLoss_le_mid hslack
      hdelta_pos hY_ext.delta_le_one hmidLoss_pos

  -- hZ_cwa via weaken_convex_wolff_bound (larger constant = weaker bound)
  have hC_le : Kakeya.realRpowENN delta (-inputLoss) ≤ Kakeya.realRpowENN delta (-midLoss) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta_pos hY_ext.delta_le_one (by linarith)
  have hZ_cwa : WZ2PaperConvexWolffBound F (Kakeya.realRpowENN delta (-midLoss)) :=
    weaken_convex_wolff_bound hY_cwa hC_le

  -- Choose ε₁, ε₃ based on inputLoss for WZ1 arithmetic compatibility
  let epsilon₁ : ℝ := (sigma - 2 * inputLoss) / 20
  let epsilon₃ : ℝ := 1 - 2 * epsilon₁
  let K : ℕ := Nat.ceil (L ^ (-2 * epsilon₁))
  let m : ℕ := 12 * max (2 * 4 * 601 ^ 3 * 12001 ^ 3) ((1600 * K + 1) ^ 5) + 12
  let C_P : ℝ := (3 : ℝ) ^ (20 / sigma)

  -- Derived loss bounds
  have hstickyLoss_lt_quarter : stickyLoss < sigma / 4 := by linarith
  have hstickyLoss_le_quarter : stickyLoss ≤ sigma / 4 := by linarith
  have hstickyLoss_pos : 0 < stickyLoss := by linarith
  have hstickyLoss_half : stickyLoss ≤ 1 / 2 := by linarith
  have h_out_le_half : stickyLoss ≤ sigma / 2 := by linarith

  have hL_le_C' : L ≤ 1 / C_P := by
    have h1 : 1 / C_P = (3 : ℝ) ^ (-(20 / sigma)) := by
      simp only [C_P]
      have h2 : (1 : ℝ) / (3 : ℝ) ^ (20 / sigma) = ((3 : ℝ) ^ (20 / sigma))⁻¹ := by simp
      rw [h2]
      exact (Real.rpow_neg (by norm_num) (20 / sigma)).symm
    rw [h1]
    exact hL_le_C

  have hL_pos : 0 < L := by
    have h1 : 0 < delta := hdelta_pos
    have h2 : delta ≤ L := rho_coarse.2.1
    linarith

  -- tau bounds
  have htau_pos : 0 < tau := by
    dsimp only [tau]
    exact mul_pos hL_pos (Real.sqrt_pos.mpr (by norm_num))
  have hL_le_tau : L ≤ tau := by
    dsimp only [tau]
    have h : 1 ≤ Real.sqrt 3 := by
      have h2 : (1 : ℝ) ≤ 3 := by norm_num
      have h3 : Real.sqrt 1 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt h2
      have h4 : Real.sqrt 1 = 1 := by rw [Real.sqrt_one]
      linarith
    have hL_nonneg : 0 ≤ L := by linarith
    calc L = L * 1 := by ring
      _ ≤ L * Real.sqrt 3 := by gcongr
  have htau_large : L * Real.sqrt 3 ≤ tau := by
    dsimp only [tau]; rfl
  have htau_sq : tau ^ 2 ≤ 4 * L := by
    dsimp only [tau]
    have h4 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h5 : (L * Real.sqrt 3) ^ 2 = 3 * L ^ 2 := by
      rw [mul_pow, h4] <;> ring
    rw [h5]
    have h7 : 3 * L ≤ 4 := by linarith [hL_small]
    have h8 : 3 * L ^ 2 ≤ 4 * L := by
      calc 3 * L ^ 2 = (3 * L) * L := by ring
        _ ≤ 4 * L := by gcongr
    exact h8
  have htau_le_one : tau ≤ 1 := by
    dsimp only [tau]
    have h2 : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_iff] <;> norm_num
    have h3 : L * Real.sqrt 3 ≤ L * 2 := by gcongr
    have h4 : L * 2 ≤ 1 := by linarith [hL_small]
    linarith

  -- K bounds
  have hK_one : 1 ≤ K := by
    have h_exp_nonpos : -2 * epsilon₁ ≤ 0 := by dsimp only [epsilon₁]; linarith
    have h' : L ^ (0 : ℝ) ≤ L ^ (-2 * epsilon₁) :=
      Real.rpow_le_rpow_of_exponent_ge hL_pos (by linarith [hL_small]) h_exp_nonpos
    have h1 : L ^ (0 : ℝ) = 1 := Real.rpow_zero L
    rw [h1] at h'
    have h2 : (1 : ℝ) ≤ (K : ℝ) := by
      calc (1 : ℝ) ≤ L ^ (-2 * epsilon₁) := h'
        _ ≤ (K : ℝ) := Nat.le_ceil _
    exact_mod_cast h2
  have hKL_small : (K : ℝ) * L ≤ 1 / 2 := by
    have h1 : (K : ℝ) ≤ L ^ (-2 * epsilon₁) + 1 := by
      have h_nonneg : 0 ≤ L ^ (-2 * epsilon₁) := by positivity
      have h_lt : (K : ℝ) < L ^ (-2 * epsilon₁) + 1 := Nat.ceil_lt_add_one h_nonneg
      exact h_lt.le
    have h2 : (K : ℝ) * L ≤ (L ^ (-2 * epsilon₁) + 1) * L := by gcongr
    have h3 : (L ^ (-2 * epsilon₁) + 1) * L = L ^ epsilon₃ + L := by
      have h4 : L ^ (-2 * epsilon₁) * L = L ^ epsilon₃ := by
        have h5 : L ^ ((-2 * epsilon₁) + 1) = L ^ (-2 * epsilon₁) * L := by
          rw [Real.rpow_add hL_pos, Real.rpow_one] <;> ring
        have h6 : (-2 * epsilon₁) + 1 = epsilon₃ := by
          dsimp only [epsilon₃, epsilon₁] <;> ring
        rw [h6] at h5; exact h5.symm
      calc (L ^ (-2 * epsilon₁) + 1) * L
        = L ^ (-2 * epsilon₁) * L + L := by ring
      _ = L ^ epsilon₃ + L := by rw [h4]
    rw [h3] at h2
    have h4 : L ^ epsilon₃ ≤ 1 / 4 := by
      have h5 : epsilon₃ ≥ 9 / 10 := by
        dsimp only [epsilon₃, epsilon₁]
        have h6 : sigma - 2 * inputLoss < 1 := by linarith [hsigma_lt_one]
        linarith
      have h7 : L ^ epsilon₃ ≤ L ^ (9 / 10 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hL_pos (by linarith [hL_small]) h5
      have h8 : L ≤ 1 / 10000 := hL_small
      have h9 : L ^ (9 / 10 : ℝ) ≤ (1 / 10000 : ℝ) ^ (9 / 10 : ℝ) :=
        Real.rpow_le_rpow (by linarith) h8 (by linarith)
      have h10 : (1 / 10000 : ℝ) ^ (9 / 10 : ℝ) ≤ 1 / 4 := by
        have h11 : (1 / 10000 : ℝ) ^ (9 / 10 : ℝ) ≤ (1 / 10000 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
        have h12 : (1 / 10000 : ℝ) ^ (1 / 2 : ℝ) = 1 / 100 := by
          have h13 : (1 / 10000 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (1 / 10000 : ℝ) := by
            rw [Real.sqrt_eq_rpow] <;> norm_num
          rw [h13]
          have h14 : Real.sqrt (1 / 10000 : ℝ) = 1 / 100 := by
            rw [Real.sqrt_eq_cases] <;> norm_num
          rw [h14]
        rw [h12] at h11
        linarith
      linarith
    have h5 : L ≤ 1 / 4 := by linarith [hL_small]
    linarith

  -- m bounds
  have hm_pos : 0 < m := by
    dsimp only [m]; positivity
  have hm_gt_packing : (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) < (m : ENNReal) := by
    have h : (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ℕ) < m := by
      dsimp only [m] <;> omega
    exact_mod_cast h
  have hm_gt_general : ((1600 * K + 1)^5 : ENNReal) < (m : ENNReal) := by
    have h : ((1600 * K + 1)^5 : ℕ) < m := by
      dsimp only [m] <;> omega
    exact_mod_cast h

  -- epsilon bounds
  have heps₁_pos : 0 < epsilon₁ := by dsimp only [epsilon₁]; linarith
  have heps₁_lt : epsilon₁ < 1 / 20 := by
    dsimp only [epsilon₁]
    linarith
  have heps₃_pos : 0 < epsilon₃ := by dsimp only [epsilon₃, epsilon₁]; linarith
  have heps₃_def : epsilon₃ = 1 - 2 * epsilon₁ := by rfl
  have heps_sum : epsilon₁ + epsilon₃ < 1 := by dsimp only [epsilon₃]; linarith

  -- Cell full bound: use stickyLoss-based eps₁ as upper bound via monotonicity
  let eps₁_sticky : ℝ := (sigma - 2 * stickyLoss) / 20
  have h_cell_full_sticky : L ^ (2 + 2 * eps₁_sticky) * tau ≤ L ^ (3 : ℝ) :=
    PureWZ2.cell_full_real_ineq L tau sigma stickyLoss eps₁_sticky C_P
      hL_pos hL_le_C' hstickyLoss_le_quarter hsigma_pos rfl rfl rfl
  have h_eps₁_ge : eps₁_sticky ≤ epsilon₁ := by
    dsimp only [epsilon₁, eps₁_sticky]; linarith
  have h_monotone_pow : L ^ (2 + 2 * epsilon₁) ≤ L ^ (2 + 2 * eps₁_sticky) :=
    Real.rpow_le_rpow_of_exponent_ge hL_pos (by linarith [hL_small]) (by linarith)
  have h_cell_full_real : L ^ (2 + 2 * epsilon₁) * tau ≤ L ^ (3 : ℝ) := by
    calc L ^ (2 + 2 * epsilon₁) * tau
      ≤ L ^ (2 + 2 * eps₁_sticky) * tau := by gcongr
    _ ≤ L ^ (3 : ℝ) := h_cell_full_sticky
  have h_cell_full : Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤ Kakeya.realRpowENN L 3 := by
    simp only [Kakeya.realRpowENN]
    have h16a : 0 ≤ Real.rpow L (2 + 2 * epsilon₁) := Real.rpow_nonneg hL_pos.le _
    have h17 : ENNReal.ofReal (Real.rpow L (2 + 2 * epsilon₁) * tau) =
        ENNReal.ofReal (Real.rpow L (2 + 2 * epsilon₁)) * ENNReal.ofReal tau :=
      ENNReal.ofReal_mul h16a
    have h18 : Real.rpow L (2 + 2 * epsilon₁) * tau ≤ Real.rpow L (3 : ℝ) := by
      simpa [Real.rpow_natCast] using h_cell_full_real
    have h19 : ENNReal.ofReal (Real.rpow L (2 + 2 * epsilon₁) * tau) ≤
        ENNReal.ofReal (Real.rpow L (3 : ℝ)) := ENNReal.ofReal_le_ofReal h18
    rw [←h17]; exact h19

  -- kappa bound: L^eps₃ = L^(1-2eps₁) = L * L^(-2eps₁) ≤ L * K
  have h_kappa : Real.rpow L epsilon₃ ≤ (K : ℝ) * L := by
    have h1 : epsilon₃ = 1 - 2 * epsilon₁ := by dsimp only [epsilon₃] <;> ring
    rw [h1]
    have h2 : Real.rpow L (1 - 2 * epsilon₁) = Real.rpow L (-2 * epsilon₁) * L := by
      have h3 : Real.rpow L ((-2 * epsilon₁) + 1) = Real.rpow L (-2 * epsilon₁) * Real.rpow L 1 :=
        Real.rpow_add hL_pos (-2 * epsilon₁) 1
      have h4 : Real.rpow L 1 = L := Real.rpow_one L
      rw [h4] at h3
      have h5 : (-2 * epsilon₁) + 1 = 1 - 2 * epsilon₁ := by ring
      rw [h5] at h3; exact h3
    rw [h2]
    have h5 : Real.rpow L (-2 * epsilon₁) ≤ (K : ℝ) := Nat.le_ceil _
    have h6 : 0 ≤ L := by linarith
    nlinarith

  -- Volume upper bound
  have h_volume_ne_top : MeasureTheory.volume sticky.croppedCoarseShading.union ≠ ⊤ := by
    have h1 : MeasureTheory.volume sticky.croppedCoarseShading.union ≤
        Kakeya.realRpowENN L (sigma - stickyLoss) := sticky.coarse_extremal.volume_upper
    have h2 : Kakeya.realRpowENN L (sigma - stickyLoss) ≠ ⊤ := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    exact ne_top_of_le_ne_top h2 h1

  -- Mass upper bound
  have h_mass_ne_top : sticky.croppedCoarseShading.mass ≠ ⊤ := by
    have h_mult : ∀ p ∈ sticky.croppedCoarseShading.union,
        (sticky.croppedCoarseShading.pointMultiplicity p : ENNReal) ≤
          Kakeya.realRpowENN L (2 - sigma - stickyLoss) * sticky.coarse.enncard := by
      intro p _
      have h := sticky.coarse_multiplicity_upper p
      simpa [L] using h
    have h_mass_le : sticky.croppedCoarseShading.mass ≤
        (Kakeya.realRpowENN L (2 - sigma - stickyLoss) * sticky.coarse.enncard) *
          MeasureTheory.volume sticky.croppedCoarseShading.union :=
      mass_le_of_pointMultiplicity_le h_mult
    have hL_pow_le : Kakeya.realRpowENN L (2 - sigma - stickyLoss) *
        Kakeya.realRpowENN L (sigma - stickyLoss) ≤ 1 := by
      have h_add : (2 - sigma - stickyLoss) + (sigma - stickyLoss) = 2 - 2 * stickyLoss := by ring
      have h_pos1 : 0 ≤ Real.rpow L (2 - sigma - stickyLoss) := Real.rpow_nonneg hL_pos.le _
      have h_eq1 : Kakeya.realRpowENN L (2 - sigma - stickyLoss) * Kakeya.realRpowENN L (sigma - stickyLoss) =
          ENNReal.ofReal (Real.rpow L (2 - sigma - stickyLoss) * Real.rpow L (sigma - stickyLoss)) := by
        simp only [Kakeya.realRpowENN]
        rw [← ENNReal.ofReal_mul h_pos1]
      rw [h_eq1]
      have h_eq2 : Real.rpow L (2 - sigma - stickyLoss) * Real.rpow L (sigma - stickyLoss) =
          Real.rpow L (2 - 2 * stickyLoss) := by
        have h : Real.rpow L ((2 - sigma - stickyLoss) + (sigma - stickyLoss)) =
            Real.rpow L (2 - sigma - stickyLoss) * Real.rpow L (sigma - stickyLoss) :=
          Real.rpow_add hL_pos (2 - sigma - stickyLoss) (sigma - stickyLoss)
        rw [h_add] at h; exact h.symm
      rw [h_eq2]
      have h6 : Real.rpow L (2 - 2 * stickyLoss) ≤ 1 :=
        Real.rpow_le_one hL_pos.le (by linarith [hL_small]) (by linarith [hstickyLoss_half])
      simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal h6
    have h_vol : MeasureTheory.volume sticky.croppedCoarseShading.union ≤
        Kakeya.realRpowENN L (sigma - stickyLoss) := sticky.coarse_extremal.volume_upper
    have h_fin : (Kakeya.realRpowENN L (2 - sigma - stickyLoss) * sticky.coarse.enncard) *
        MeasureTheory.volume sticky.croppedCoarseShading.union ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
        · simp [Kakeya.Streamlined.TubeFamily.enncard] <;> exact ENNReal.natCast_ne_top _
      · exact ne_top_of_le_ne_top (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]) h_vol
    exact ne_top_of_le_ne_top h_fin h_mass_le

  -- h_avg bound
  have hme : (m : ℝ) = (PureWZ2.h_avg_m_val sigma inputLoss L : ℝ) := by
    dsimp only [m, PureWZ2.h_avg_m_val]
    <;> rfl
  have h_havg_bound' : (m : ℝ) * L ^ (sigma - 3 * stickyLoss) < 1 / 8 := by
    rw [hme]
    exact h_havg_bound
  have hL_coarse_le_24 : L ≤ 1 / 24 := by
    have h : L ≤ 1 / 10000 := hL_small
    linarith
  have h_avg_strong : (m : ENNReal) * MeasureTheory.volume sticky.croppedCoarseShading.union <
      (1 / 2 : ENNReal) * sticky.croppedCoarseShading.mass :=
    PureWZ2.h_avg_from_sticky sticky.coarse_extremal sticky.cover m hL_pos hL_coarse_le_24 h_havg_bound'
  have h_avg : (m : ENNReal) * MeasureTheory.volume sticky.croppedCoarseShading.union <
      sticky.croppedCoarseShading.mass := by
    have h3 : (1 / 2 : ENNReal) * sticky.croppedCoarseShading.mass ≤
        (1 : ENNReal) * sticky.croppedCoarseShading.mass := by gcongr <;> norm_num
    have h4 : (1 : ENNReal) * sticky.croppedCoarseShading.mass = sticky.croppedCoarseShading.mass := one_mul _
    exact h_avg_strong.trans_le (h3.trans_eq h4)

  -- Construct PropertyP using already-proved close direction count
  let hpropP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      (tau := tau) :=
    PureWZ2.constructPropertyPFromSticky
      delta sigma stickyLoss
      (sticky := sticky)
      tau epsilon₁ epsilon₃ K m
      hL_pos hL_small htau_pos hL_le_tau htau_large htau_sq htau_le_one
      hK_one hKL_small hm_pos hm_gt_packing hm_gt_general
      heps₁_pos heps₃_pos heps_sum
      h_mass_ne_top h_volume_ne_top h_avg_strong
      h_kappa h_cell_full
  have hpropertyThree_eq : hpropP.propertyThree = hpropP.propertyOne := by
    rfl

  exact ⟨Z, hZ_sub, hZ_ext, hZ_cwa, epsilon₁, epsilon₃, hpropP,
    rfl, heps₁_pos, heps₁_lt, heps₃_pos, heps₃_def, heps_sum, htau_pos,
    hL_le_tau, htau_sq, htau_le_one, hpropertyThree_eq,
    hZ_sub_coarse, trivial⟩

/-- Backwards-compatible Phase 1 interface.  New paper-order consumers should
use `phase1_sticky_to_Z_and_propertyP_certified` so that the Property-(P)
parameter certificates are not discarded. -/
lemma phase1_sticky_to_Z_and_propertyP
    {delta sigma inputLoss midLoss stickyLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    {rho_coarse : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      (sourceShading := Y) rho_coarse logExponent)
    (hY_ext : WZ2PaperCroppedIsExtremal sigma inputLoss F Y)
    (hY_cwa : WZ2PaperConvexWolffBound F
      (Kakeya.realRpowENN delta (-inputLoss)))
    (hmidLoss_pos : 0 < midLoss)
    (hinputLoss_le_mid : inputLoss ≤ midLoss)
    (hL_small : rho_coarse.1 ≤ 1 / 10000)
    (hslack : (wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
        Kakeya.realRpowENN delta midLoss ≤
      Kakeya.realRpowENN delta inputLoss)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hinputLoss_pos : 0 < inputLoss)
    (hinputLoss_le_sticky : inputLoss ≤ stickyLoss)
    (hstickyLoss_small : 6 * stickyLoss < sigma + 2 * inputLoss)
    (hL_le_C : rho_coarse.1 ≤ (3 : ℝ) ^ (-(20 / sigma)))
    (h_havg_bound :
      (PureWZ2.h_avg_m_val sigma inputLoss rho_coarse.1 : ℝ) *
          rho_coarse.1 ^ (sigma - 3 * stickyLoss) < 1 / 8) :
    ∃ (Z : WZ1PaperTubeShading F)
      (hZ_sub : PaperIsSubshading Z Y)
      (hZ_ext : WZ2PaperCroppedIsExtremal sigma midLoss F Z)
      (hZ_cwa : WZ2PaperConvexWolffBound F
        (Kakeya.realRpowENN delta (-midLoss)))
      (epsilon₁ epsilon₃ : ℝ)
      (propP : PureWZ2PropertyPData
        (sigma := sigma)
        (coarseShading := sticky.croppedCoarseShading)
        (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
        (tau := rho_coarse.1 * Real.sqrt 3))
      (hZ_sub_coarse : Z.union ⊆ sticky.croppedCoarseShading.union), True := by
  rcases phase1_sticky_to_Z_and_propertyP_certified sticky hY_ext hY_cwa
      hmidLoss_pos hinputLoss_le_mid hL_small hslack hsigma_pos
      hsigma_lt_one hinputLoss_pos hinputLoss_le_sticky
      hstickyLoss_small hL_le_C h_havg_bound with
    ⟨Z, hZ_sub, hZ_ext, hZ_cwa, epsilon₁, epsilon₃, propP,
      _, _, _, _, _, _, _, _, _, _, _, hZ_sub_coarse, _⟩
  exact ⟨Z, hZ_sub, hZ_ext, hZ_cwa, epsilon₁, epsilon₃, propP,
    hZ_sub_coarse, trivial⟩

end Kakeya.Assouad

end
