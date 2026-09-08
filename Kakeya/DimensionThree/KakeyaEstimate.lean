/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Asymptotics
public import Kakeya.Bootstrap
public import Kakeya.DimensionThree.MainLemma1
public import Kakeya.DimensionThree.MainLemma2
public import Kakeya.KakeyaEstimate
public import Kakeya.PartialEstimates
public import Kakeya.ConvexBody

/-!
# Kakeya in dimension three
-/

@[expose] public section

open MeasureTheory

namespace Kakeya

/-- The Katz-Tao partial Kakeya estimate `K_KT(β)` holds in `ℝ^3` for every `0 < β ≤ 1`.

The set `s = {β | K_KT(β)}` contains `1` (`KatzTao_one`), is up-closed
(`KatzTaoEstimate.mono`), and is closed under `β ↦ β - ν β / 2` on `(0, 1]`, so
`ioc_subset_of_sub_mem_of_monotoneOn` gives `(0, 1] ⊆ s` with the monotone, positive step
`ν / 2`, where `ν` is the increment of Main Lemma 2.

The halving is what pays for the non-sharp form of Main Lemma 1, which produces `K_F(γ)`
only for `γ > β`. Given `K_KT(β)`, apply Main Lemma 1 and Main Lemma 2 at
`γ = min 1 (β + ν β / 2)` rather than at `β`: for `β < 1` this `γ` lies in `Set.Ioc β 1`,
so `K_F(γ)` is available, `K_KT(γ)` follows from `KatzTaoEstimate.mono`, and monotonicity of
`ν` gives `γ - ν γ ≤ β + ν β / 2 - ν β = β - ν β / 2`; up-closedness then yields
`β - ν β / 2 ∈ s`. At `β = 1` no shift is needed, since `K_F(1)` is `frostmanEstimate_one`. -/
theorem katzTaoEstimateDimensionThree
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    {β : ℝ} (h1 : 0 < β) (h2 : β ≤ 1) :
    KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β := by
  obtain ⟨ν, hν_mono, hν_pos, hν_step⟩ :=
    KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate hSFE
  set f : ℝ → ℝ := fun x => ν x / 2 with hf_def
  have hf_mono : MonotoneOn f (Set.Ioc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    dsimp [f]
    have hν_le : ν x ≤ ν y := hν_mono hx hy hxy
    nlinarith
  have hf_pos : ∀ γ ∈ Set.Ioc (0 : ℝ) 1, f γ > 0 := by
    intro γ hγ
    dsimp [f]
    have hνγ_pos : 0 < ν γ := hν_pos γ hγ.1 hγ.2
    nlinarith
  have h_up_closed : ∀ γ γ', γ ≤ γ' → KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) γ →
      KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) γ' := by
    intro γ γ' h_le h_KT
    exact KatzTaoEstimate.mono h_le h_KT
  have h_one_KT : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) 1 :=
    KatzTao_one
  have h_step : ∀ γ ∈ Set.Ioc (0 : ℝ) 1,
      KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) γ →
      KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) (γ - f γ) := by
    intro γ hγ h_KT_γ
    have hγ_pos : 0 < γ := hγ.1
    have hγ_le_one : γ ≤ 1 := hγ.2
    dsimp [f]
    by_cases hγ_eq_one : γ = 1
    · subst hγ_eq_one
      have h_F_1 : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) 1 :=
        frostmanEstimate_one
      have h_KT_sub_ν : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) (1 - ν 1) :=
        hν_step 1 (by norm_num) (by norm_num) h_KT_γ h_F_1
      have h_ineq : 1 - ν 1 ≤ 1 - ν 1 / 2 := by
        have hν1_pos : 0 < ν 1 := hν_pos 1 (by norm_num) (by norm_num)
        nlinarith
      exact KatzTaoEstimate.mono h_ineq h_KT_sub_ν
    · have hγ_lt_one : γ < 1 := lt_of_le_of_ne hγ_le_one hγ_eq_one
      set γ' := min 1 (γ + ν γ / 2) with hγ'_def
      have hγ'_pos : 0 < γ' := by
        refine lt_min_iff.mpr ?_
        constructor
        · norm_num
        · nlinarith [hν_pos γ hγ_pos hγ_le_one]
      have hγ'_le_one : γ' ≤ 1 := min_le_left _ _
      have hγ_lt_γ' : γ < γ' := by
        have h_lt : γ < γ + ν γ / 2 := by
          have hνγ_pos : 0 < ν γ := hν_pos γ hγ_pos hγ_le_one
          nlinarith
        refine lt_min_iff.mpr ⟨hγ_lt_one, h_lt⟩
      have hγ_le_γ' : γ ≤ γ' := le_of_lt hγ_lt_γ'
      have hγ'_Ioc : γ' ∈ Set.Ioc (0 : ℝ) 1 := ⟨hγ'_pos, hγ'_le_one⟩
      have h_K_F_γ' : FrostmanEstimate.{0} (EuclideanSpace ℝ (Fin 3)) γ' :=
        KatzTaoEstimate.frostmanEstimate hSFE (by linarith) hγ_lt_γ' hγ'_le_one h_KT_γ
      have h_K_KT_γ' : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) γ' :=
        KatzTaoEstimate.mono hγ_le_γ' h_KT_γ
      have h_K_KT_γ'_sub_ν : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) (γ' - ν γ') :=
        hν_step γ' hγ'_pos hγ'_le_one h_K_KT_γ' h_K_F_γ'
      have h_ineq : γ' - ν γ' ≤ γ - ν γ / 2 := by
        have hνγ_le_νγ' : ν γ ≤ ν γ' := hν_mono hγ hγ'_Ioc hγ_le_γ'
        have hγ'_le : γ' ≤ γ + ν γ / 2 := min_le_right _ _
        nlinarith
      exact KatzTaoEstimate.mono h_ineq h_K_KT_γ'_sub_ν
  have h_Ioc_sub : Set.Ioc (0 : ℝ) 1 ⊆ {γ' | KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) γ'} :=
    ioc_subset_of_sub_mem_of_monotoneOn h_up_closed h_one_KT h_step hf_mono hf_pos
  have hβ_Ioc : β ∈ Set.Ioc (0 : ℝ) 1 := ⟨h1, h2⟩
  simpa only [Set.mem_setOf_eq] using h_Ioc_sub hβ_Ioc

end Kakeya

open MeasureTheory in
/-- Take `h2` to the `β'` power and unfold `mul_rpow`. (extracted by Fuse golfer) -/
private lemma volume_chain_bound_hC1 {β' η : ℝ} (hβ'_pos : 0 < β')
    {δE n c₃ V_B : ENNReal}
    (hδE_pos : 0 < δE) (hδE_ne_top : δE ≠ ⊤)
    (hc₃_ne_top : c₃ ≠ ⊤) (hV_B_ne_top : V_B ≠ ⊤)
    (hn_ne_top : n ≠ ⊤)
    (h2 : n * (c₃ * δE ^ 2) ≤ δE ^ (-η) * V_B) :
    n ^ β' * c₃ ^ β' * δE ^ (2 * β') ≤ δE ^ (-η * β') * V_B ^ β' := by
  have hraw := ENNReal.rpow_le_rpow h2 hβ'_pos.le
  rwa [ENNReal.mul_rpow_of_ne_top hn_ne_top
        (ENNReal.mul_ne_top hc₃_ne_top (by finiteness)),
      ENNReal.mul_rpow_of_ne_top hc₃_ne_top (by finiteness),
      ENNReal.mul_rpow_of_ne_top
        (ENNReal.rpow_ne_top_of_nonneg' hδE_pos hδE_ne_top) hV_B_ne_top,
      ← ENNReal.rpow_mul,
      show (δE ^ (2 : ℕ) : ENNReal) = δE ^ (2 : ℝ) from by
        rw [← ENNReal.rpow_natCast]; rfl,
      ← ENNReal.rpow_mul, ← mul_assoc] at hraw

/-- The exponent-aligned algebraic identity used in `volume_chain_bound`.
(extracted by Fuse golfer) -/
private lemma volume_chain_bound_eq {β' η : ℝ} {δE n c₃ : ENNReal}
    (hδE_ne_zero : δE ≠ 0) (hδE_ne_top : δE ≠ ⊤)
    (hc₃_ne_zero : c₃ ≠ 0) (hc₃_ne_top : c₃ ≠ ⊤) :
    δE ^ η * (n * (c₃ * δE ^ 2)) *
      (c₃ ^ β' * δE ^ (2 * β')) * δE ^ ((η + 1) * β') =
      n * c₃ ^ (1 + β') * δE ^ ((1 + β') * η + 3 * β' + 2) := by
  rw [show δE ^ (2 : ℕ) = δE ^ (2 : ℝ) by rw [← ENNReal.rpow_natCast]; rfl,
    show δE ^ η * (n * (c₃ * δE ^ (2 : ℝ))) *
      (c₃ ^ β' * δE ^ (2 * β')) * δE ^ ((η + 1) * β') =
      n * (c₃ ^ (1 : ℝ) * c₃ ^ β') *
        (δE ^ η * δE ^ (2 : ℝ) * δE ^ (2 * β') * δE ^ ((η + 1) * β')) from by
    rw [ENNReal.rpow_one]; ring, ← ENNReal.rpow_add _ _ hc₃_ne_zero hc₃_ne_top]
  simp_rw [← ENNReal.rpow_add _ _ hδE_ne_zero hδE_ne_top]
  congr 2; ring

/-- Core algebraic chain in the proof of `KakeyaEstimate.of_katzTaoEstimate`.
Given the two key inequalities `h1` (from fullness + Main Lemma) and `h2` (from
Katz-Tao), together with the threshold `δE^ρ ≤ Cthresh = c₃^(1+β')/V_B^β'` and the
exponent bound, conclude `n * δE^(β+2) ≤ U`. (extracted by Fuse golfer) -/
private lemma volume_chain_bound {β β' η ρ : ℝ}
    (hβ'_pos : 0 < β')
    (h_exp_bound : (1 + β') * η + 3 * β' + 2 ≤ β + 2 - ρ)
    {δE U n c₃ V_B Cthresh : ENNReal}
    (hδE_pos : 0 < δE) (hδE_le_one : δE ≤ 1) (hδE_ne_top : δE ≠ ⊤)
    (hc₃_pos : 0 < c₃) (hc₃_ne_top : c₃ ≠ ⊤)
    (hV_B_pos : 0 < V_B) (hV_B_ne_top : V_B ≠ ⊤)
    (hn_ne_top : n ≠ ⊤)
    (hCthresh_def : Cthresh = c₃ ^ (1 + β') / V_B ^ β')
    (hδ_small : δE ^ ρ ≤ Cthresh)
    (h1 : δE ^ η * (n * (c₃ * δE ^ 2)) ≤ δE ^ (-β') * n ^ β' * U)
    (h2 : n * (c₃ * δE ^ 2) ≤ δE ^ (-η) * V_B) :
    n * δE ^ (β + 2) ≤ U := by
  have hδE_ne_zero : δE ≠ 0 := hδE_pos.ne'
  -- Bound n^β' via h2 and rpow_le_rpow.
  have hC1 : n ^ β' * c₃ ^ β' * δE ^ (2 * β') ≤ δE ^ (-η * β') * V_B ^ β' :=
    volume_chain_bound_hC1 hβ'_pos hδE_pos hδE_ne_top hc₃_ne_top hV_B_ne_top hn_ne_top h2
  -- Cthresh * δE^(-ρ) ≥ 1.
  have hCthresh_inv : (1 : ENNReal) ≤ Cthresh * δE ^ (-ρ) := by
    rw [ENNReal.rpow_neg, show Cthresh * (δE ^ ρ)⁻¹ = Cthresh / δE ^ ρ from rfl,
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.rpow_pos hδE_pos hδE_ne_top).ne')
        (Or.inl (ENNReal.rpow_ne_top_of_nonneg' hδE_pos hδE_ne_top)), one_mul]
    exact hδ_small
  have h_δE_exp_ge : δE ^ (β + 2 - ρ) ≤ δE ^ ((1 + β') * η + 3 * β' + 2) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδE_le_one h_exp_bound
  -- Suffices to bound n * Cthresh * δE^((1+β')η + 3β' + 2).
  have hstep : n * δE ^ (β + 2) ≤ n * Cthresh * δE ^ ((1 + β') * η + 3 * β' + 2) := by
    calc n * δE ^ (β + 2)
        = n * (1 * δE ^ (β + 2)) := by rw [one_mul]
      _ ≤ n * (Cthresh * δE ^ (-ρ) * δE ^ (β + 2)) := by gcongr
      _ = n * Cthresh * (δE ^ (-ρ) * δE ^ (β + 2)) := by ring
      _ = n * Cthresh * δE ^ (β + 2 - ρ) := by
          rw [← ENNReal.rpow_add _ _ hδE_ne_zero hδE_ne_top]; ring_nf
      _ ≤ n * Cthresh * δE ^ ((1 + β') * η + 3 * β' + 2) := by gcongr
  refine hstep.trans ?_
  -- Substitute Cthresh and manipulate the V_B^β' factor.
  rw [hCthresh_def, show n * (c₃ ^ (1 + β') / V_B ^ β') * δE ^ ((1 + β') * η + 3 * β' + 2)
      = (n * c₃ ^ (1 + β') * δE ^ ((1 + β') * η + 3 * β' + 2)) / V_B ^ β' from by
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring,
    ENNReal.div_le_iff (ENNReal.rpow_pos hV_B_pos hV_B_ne_top).ne'
      (ENNReal.rpow_ne_top_of_nonneg' hV_B_pos hV_B_ne_top)]
  -- Combine h1 and hC1.
  have h_exp2 : (-β') + (-η * β') + (η + 1) * β' = 0 := by ring
  calc n * c₃ ^ (1 + β') * δE ^ ((1 + β') * η + 3 * β' + 2)
      = δE ^ η * (n * (c₃ * δE ^ 2)) *
          (c₃ ^ β' * δE ^ (2 * β')) * δE ^ ((η + 1) * β') :=
        (volume_chain_bound_eq hδE_ne_zero hδE_ne_top hc₃_pos.ne' hc₃_ne_top).symm
    _ ≤ δE ^ (-β') * n ^ β' * U *
          (c₃ ^ β' * δE ^ (2 * β')) * δE ^ ((η + 1) * β') := by gcongr
    _ = δE ^ (-β') * (n ^ β' * c₃ ^ β' * δE ^ (2 * β')) *
          δE ^ ((η + 1) * β') * U := by ring
    _ ≤ δE ^ (-β') * (δE ^ (-η * β') * V_B ^ β') *
          δE ^ ((η + 1) * β') * U := by gcongr
    _ = (δE ^ (-β') * δE ^ (-η * β') * δE ^ ((η + 1) * β')) * V_B ^ β' * U := by ring
    _ = U * V_B ^ β' := by
        simp_rw [← ENNReal.rpow_add _ _ hδE_ne_zero hδE_ne_top]
        rw [h_exp2, ENNReal.rpow_zero, one_mul, mul_comm]

open Topology Filter ShadedBody Kakeya in
/-- The Katz-Tao partial Kakeya estimate `K_KT(β')` in `ℝ^3` implies the Kakeya estimate
`KakeyaEstimate 3 β η` for some `η > 0`, provided `β > 3 β'`. -/
theorem KakeyaEstimate.of_katzTaoEstimate_pos.{u} {β β' : ℝ}
    (hβ'_pos : 0 < β') (h3β'_lt_β : 3 * β' < β) (hβ_le_one : β ≤ 1)
    (h : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β') :
    ∃ η : ℝ, 0 < η ∧ KakeyaEstimate.{u} 3 β η := by
  let η_target : ℝ := (β - 3 * β') / 4
  obtain ⟨η₁, hη₁_pos, hh⟩ := h β' hβ'_pos
  set η : ℝ := min η₁ η_target
  have hη_pos : 0 < η := lt_min hη₁_pos (div_pos (by linarith) (by linarith))
  refine ⟨η, hη_pos, ?_⟩
  set V_B : ENNReal :=
    volume (ConvexSpaceBody.closedUnitBall (E := EuclideanSpace ℝ (Fin 3))).carrier
  have hsmall : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (δ : ENNReal) ^ ((β - 3 * β') / 2) ≤
      ((Tube.le_volume.c 3 : NNReal) : ENNReal) ^ (1 + β') / V_B ^ β' :=
    ENNReal.eventually_coe_rpow_le_of_pos (by show (0 : ℝ) < (β - 3 * β') / 2; linarith)
      (ENNReal.div_pos
        (ENNReal.rpow_pos (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos 3)) ENNReal.coe_ne_top).ne'
        (ENNReal.rpow_ne_top_of_nonneg' ConvexSpaceBody.closedUnitBall_volume_pos
          ConvexSpaceBody.closedUnitBall.isCompact.measure_ne_top))
  filter_upwards [hh, Ioo_mem_nhdsGT zero_lt_one, hsmall]
    with δ hh_δ ⟨hδ_pos, hδ_lt_one⟩ hδ_small ι s T hball hKT_in hfull
  set δE := (δ : ENNReal)
  have hδE_pos : 0 < δE := ENNReal.coe_lt_coe.mpr hδ_pos
  have hδE_le_one : δE ≤ 1 := ENNReal.coe_le_coe.mpr hδ_lt_one.le
  have hδE_ne_top : δE ≠ ⊤ := ENNReal.coe_ne_top
  -- Rewrite goal δE^β * s.card * δE^2 = s.card * δE^(β+2).
  rw [ge_iff_le, mul_right_comm, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_add _ _ hδE_pos.ne' hδE_ne_top, mul_comm]
  -- Each carrier has volume ≥ c₃ * δ^2.
  have h_carrier_lb : ∀ i ∈ s, (Tube.le_volume.c 3 : ENNReal) * δE ^ 2 ≤
      volume (T i).carrier := fun i _ => by
    have := (T i).toTube.le_volume
    rwa [finrank_euclideanSpace_fin] at this
  -- Exponent bound: (1+β')η + 3β' + 2 ≤ β + 2 - ρ.
  refine volume_chain_bound hβ'_pos ?_ hδE_pos hδE_le_one hδE_ne_top
    (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos 3)) ENNReal.coe_ne_top
    ConvexSpaceBody.closedUnitBall_volume_pos
    ConvexSpaceBody.closedUnitBall.isCompact.measure_ne_top
    (ENNReal.natCast_ne_top _) rfl hδ_small ?_
    (ConvexSpaceBody.IsKatzTao.card_mul_le hKT_in hball h_carrier_lb)
  · have hηt : (1 + β') * η ≤ (1 + β') * ((β - 3 * β') / 4) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
    have hslack : (1 - β') * (β - 3 * β') ≥ 0 :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  · -- Lower bound on ∑ shade.
    rw [show δE ^ η = ((δ ^ η : NNReal) : ENNReal) by
        rw [ENNReal.coe_rpow_of_nonneg _ hη_pos.le]]
    refine (ShadedBody.coe_fullness_mul_le_sum_volume_shade
      s (fun i ↦ (T i).toShadedBody) hfull h_carrier_lb).trans ?_
    -- MERGE NOTE: `KatzTaoEstimate.multiplicity_bound` now concludes in the summed form
    -- `∑ |Y(T)| ≤ c * |U(𝕋, Y)|` directly, so no passage through `multiplicity_le_iff` is needed.
    exact hh_δ s T hball
      (hKT_in.mono (ENNReal.rpow_le_rpow_of_exponent_ge hδE_le_one (by simp [η])))
      ((NNReal.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le (min_le_left _ _)).trans hfull)


open Topology Filter ShadedBody Kakeya in
/-- The Katz-Tao partial Kakeya estimate `K_KT(β')` in `ℝ^3` implies the Kakeya estimate
`KakeyaEstimate 3 β η` for some `η > 0`, provided `β > 3 β'`. -/
theorem KakeyaEstimate.of_katzTaoEstimate.{u} {β β' : ℝ}
    (hβ'_pos : 0 < β') (h3β'_lt_β : 3 * β' < β) (hβ_le_one : β ≤ 1)
    (h : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β') :
    ∃ η : ℝ, KakeyaEstimate.{u} 3 β η :=
  (KakeyaEstimate.of_katzTaoEstimate_pos hβ'_pos h3β'_lt_β hβ_le_one h).imp fun _ h => h.2

open MeasureTheory Topology Filter ShadedBody Kakeya in
/-- [GWZ, Theorem 1.1], with the strict positivity of `η` retained. -/
theorem KakeyaEstimateDimensionThree_pos
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    (β : ℝ) (hβ : 0 < β) :
    ∃ η : ℝ, 0 < η ∧ KakeyaEstimate.{0} 3 β η := by
  wlog hβ_le_one : β ≤ 1 with H
  · obtain ⟨η, hη_pos, hη⟩ := H hSFE 1 zero_lt_one le_rfl
    exact ⟨η, hη_pos, hη.mono (not_le.mp hβ_le_one).le⟩
  -- Pick β' = β/4: then 0 < β' ≤ 1 and 3β' < β.
  have hβ'_pos : 0 < β / 4 := by positivity
  exact KakeyaEstimate.of_katzTaoEstimate_pos.{0} hβ'_pos (by linarith) hβ_le_one
    (Kakeya.katzTaoEstimateDimensionThree hSFE hβ'_pos (by linarith))

/-- [GWZ, Theorem 1.1] -/
theorem KakeyaEstimateDimensionThree
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    (β : ℝ) (hβ : 0 < β) : ∃ η : ℝ, KakeyaEstimate.{0} 3 β η :=
  (KakeyaEstimateDimensionThree_pos hSFE β hβ).imp fun _ h => h.2
