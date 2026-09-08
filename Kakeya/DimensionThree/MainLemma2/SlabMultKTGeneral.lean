/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SlabMultKTProduce
public import Kakeya.DimensionThree.MainLemma2.SplitInputsGeneral

/-!
# The slab Katz–Tao estimate at general `b` (conjunct 4)

General-branch steps **G8** continued: the twin of
`Kakeya.VeryNotSticky.ktRho2ScaleData_of_ckt` and of
`Kakeya.VeryNotSticky.eventually_ktRho2ScaleData_degenerate` at general `b`, cut as **new
declarations**. No existing statement is edited; the degenerate instances are recorded as
tripwire `example`s.

## What the pin was doing, and what replaces it

The existing producer reads `cfg.b = cfg.δ` exactly once, in

  `hρ : cfg.rho2 = cfg.δ ^ (1 - exscal)`,

and that identity is used for three things only: the enclosure threshold `C₀ ρ₂ ≤ 1/8`, the
lower bound `δ ≤ ρ₂`, and the window radius `C₀ ρ₂ ≤ cfg.ckt.wρ`. The middle one is a theorem
of `cfg` alone (`Kakeya.VeryNotSticky.delta_le_rho2_general`). The other two are genuine
smallness conditions, and at general `b` the honest way to state them is **on `ρ₂` itself**:

  `h8 : cfg.rho2 ≤ (8 · bd.C₀)⁻¹`   and   `hwρ : bd.C₀ · cfg.rho2 ≤ cfg.ckt.wρ`.

`Kakeya.VeryNotSticky.ktRho2ScaleData_of_ckt_nonslab` takes exactly those. Everything after the
enclosure — `cfg.ckt.hwin` at tube scale `C₀ ρ₂` and Katz–Tao parameter `τ = δ^{max 1 (10η/wη)}`,
`Kakeya.VeryNotSticky.ktRho2_window_loss_le`, `Kakeya.VeryNotSticky.ktRho2_loss_arith` — never
mentions `b`, so the exponents `(4ϱ, 9η, 3ϱ)` are unchanged. This is the sense in which
"`ckt.hwin`'s window already covers `ρ₂`'s range".

At the non-slab guard `cfg.b ≤ cfg.δ ^ (2 exscal)` one has `ρ₂ ≤ δ^{exscal}`
(`Kakeya.VeryNotSticky.rho2_le_rpow_exscal`), and both conditions then follow from two
thresholds on `δ` alone: `δ^{exscal} ≤ (8 C₀bd)⁻¹` and `δ^{η} ≤ 6 / C₀bd`, the second combining
with `cfg.ckt.hδrad` (`6 δ^{exscal-η} ≤ wρ`).
`Kakeya.VeryNotSticky.eventually_ktRho2ScaleData_nonslab` arranges them, and needs
`0 < exscal` for the first — a hypothesis the degenerate statement did
not carry because its threshold was at the exponent `1 - exscal`, positive by `exscal ≤ 1/2`.

Nothing here changes a existing statement.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped NNReal ENNReal Topology

universe u

namespace Kakeya.VeryNotSticky

/-- At the non-slab guard `b ≤ δ^{2 exscal}` the angular scale satisfies `ρ₂ ≤ δ^{exscal}`. -/
theorem rho2_le_rpow_exscal (cfg : VeryNotSticky.{u})
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal)) : cfg.rho2 ≤ cfg.δ ^ cfg.exscal := by
  have hr₁0 : 0 < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  rw [VeryNotSticky.rho2, div_le_iff₀ hr₁0, rpow_exscal_mul_r₁]
  exact hnotslab

/-- **The slab Katz–Tao estimate at general `b`** (steps G8), the twin of
`Kakeya.VeryNotSticky.ktRho2ScaleData_of_ckt` with the pin `cfg.b = cfg.δ` replaced by the two
smallness conditions read directly on `ρ₂`. -/
theorem ktRho2ScaleData_of_ckt_nonslab (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (hexscal12 : cfg.exscal ≤ 1 / 2) (hϱ1 : cfg.ϱ ≤ 1)
    (h8 : cfg.rho2 ≤ (8 * bd.C₀)⁻¹)
    (hwρ : bd.C₀ * cfg.rho2 ≤ cfg.ckt.wρ)
    (hKη : cfg.δ ^ cfg.η ≤ (ktRho2EnclosureConstant bd.C₀)⁻¹)
    (hKϱ : cfg.δ ^ (cfg.ϱ / 2) ≤ (ktRho2EnclosureConstant bd.C₀)⁻¹) :
    cfg.KTRho2ScaleData bd (4 * cfg.ϱ) (9 * cfg.η) (3 * cfg.ϱ) := by
  intro t T hball hthick hKTt hfull
  rcases t.eq_empty_or_nonempty with rfl | htne
  · simp
  have hδ0 : 0 < cfg.δ := cfg.hδ
  have hδ1 : cfg.δ ≤ 1 := cfg.hδ1
  have hδ1' : (cfg.δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hη : 0 < cfg.η := cfg.hη
  have hC₀ : 1 ≤ bd.C₀ := bd.hC₀
  have hC₀pos : (0 : NNReal) < bd.C₀ := lt_of_lt_of_le zero_lt_one hC₀
  set K : NNReal := ktRho2EnclosureConstant bd.C₀ with hK_def
  have hK1 : (1 : NNReal) ≤ K := one_le_ktRho2EnclosureConstant hC₀
  have hKpos : (0 : NNReal) < K := lt_of_lt_of_le zero_lt_one hK1
  -- the tube scale `r = C₀ ρ₂`
  set r : NNReal := bd.C₀ * cfg.rho2 with hr_def
  have hr8 : (r : ℝ) ≤ 1 / 8 := by
    have : r ≤ 1 / 8 := by
      calc r ≤ bd.C₀ * (8 * bd.C₀)⁻¹ := by rw [hr_def]; exact mul_le_mul' le_rfl h8
        _ = 1 / 8 := by
            rw [mul_inv, ← mul_assoc, mul_comm bd.C₀, mul_assoc, mul_inv_cancel₀ hC₀pos.ne',
              mul_one, one_div]
    exact_mod_cast this
  have hδρ : cfg.δ ≤ cfg.rho2 := delta_le_rho2_general cfg
  have hδr : cfg.δ ≤ r := by
    calc cfg.δ ≤ cfg.rho2 := hδρ
      _ = 1 * cfg.rho2 := (one_mul _).symm
      _ ≤ bd.C₀ * cfg.rho2 := by gcongr
  have hr0 : 0 < r := lt_of_lt_of_le hδ0 hδr
  have hrwρ : r ≤ cfg.ckt.wρ := hwρ
  -- the Katz–Tao parameter `τ = δ^L`, `L = max 1 (10η/wη)`
  have hwη : 0 < cfg.ckt.wη := cfg.ckt.hwη
  set L : ℝ := max 1 (10 * cfg.η / cfg.ckt.wη) with hL_def
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hL2 : 10 * cfg.η ≤ L * cfg.ckt.wη := by
    have := le_max_right 1 (10 * cfg.η / cfg.ckt.wη)
    rwa [div_le_iff₀ hwη] at this
  set τ : NNReal := cfg.δ ^ L with hτ_def
  have hτ0 : 0 < τ := NNReal.rpow_pos hδ0
  have hτr : τ ≤ r := by
    calc τ = cfg.δ ^ L := rfl
      _ ≤ cfg.δ ^ (1 : ℝ) := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hL1
      _ = cfg.δ := NNReal.rpow_one _
      _ ≤ r := hδr
  -- the enclosure
  obtain ⟨T', hball', hmult_eq, hKT', hfull'⟩ :=
    exists_enclosing_shadedTubes_of_ktRho2 cfg bd htne T hball hthick hKTt hr8
  have hball4 : ∀ j, (T' j).carrier ⊆ closedBall 0 (4 : ℝ) := fun j ↦
    (hball' j).trans (closedBall_subset_closedBall (by norm_num))
  -- fullness of the tube family: `τ^{wη} ≤ δ^{10η} = δ^{9η} δ^{η} ≤ δ^{9η} / K`
  have hfullT' : ShadedBody.fullness t (fun j ↦ (T' j).toShadedBody) ≥ τ ^ cfg.ckt.wη := by
    have hτK : τ ^ cfg.ckt.wη * K ≤ cfg.δ ^ (9 * cfg.η) := by
      have hτw : τ ^ cfg.ckt.wη ≤ cfg.δ ^ (10 * cfg.η) := by
        rw [hτ_def, ← NNReal.rpow_mul]
        exact NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hL2
      have hsplit : cfg.δ ^ (10 * cfg.η) = cfg.δ ^ (9 * cfg.η) * cfg.δ ^ cfg.η := by
        rw [← NNReal.rpow_add hδ0.ne']
        congr 1
        ring
      have hηK : cfg.δ ^ cfg.η * K ≤ 1 := by
        calc cfg.δ ^ cfg.η * K ≤ K⁻¹ * K := mul_le_mul_of_nonneg_right hKη bot_le
          _ = 1 := inv_mul_cancel₀ hKpos.ne'
      calc τ ^ cfg.ckt.wη * K ≤ cfg.δ ^ (10 * cfg.η) * K := by gcongr
        _ = cfg.δ ^ (9 * cfg.η) * (cfg.δ ^ cfg.η * K) := by rw [hsplit, mul_assoc]
        _ ≤ cfg.δ ^ (9 * cfg.η) := mul_le_of_le_one_right bot_le hηK
    have := hfull' ((cfg.δ ^ (9 * cfg.η) : NNReal) : ENNReal)
      ((τ ^ cfg.ckt.wη : NNReal) : ENNReal)
      (by exact_mod_cast hfull) (by exact_mod_cast hτK)
    exact_mod_cast this
  -- the window bound at tube scale `r`, parameter `τ`
  have hmult := cfg.ckt.hwin r hr0 hrwρ τ hτ0 hτr t T' hball4 hfullT'
  -- the loss: `τ^{-we} = δ^{-we L} ≤ δ^{-ϱ/2}`
  have hloss : cfg.ckt.we * L ≤ cfg.ϱ / 2 :=
    ktRho2_window_loss_le cfg.hϱ hϱ1 hexscal12 cfg.ckt.hwe0 cfg.ckt.hwe cfg.ckt.hwb cfg.hβ1
      hwη cfg.ckt.hηKT
  have hτloss : (τ : ENNReal) ^ (-cfg.ckt.we) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) := by
    have hcoe : ((τ : NNReal) : ENNReal) = (cfg.δ : ENNReal) ^ L := by
      rw [hτ_def, ENNReal.coe_rpow_of_nonneg _ hL0]
    rw [hcoe, ← ENNReal.rpow_mul]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hδ1' (by nlinarith)
  have hK4 : (K : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) := by
    rw [ENNReal.rpow_neg, ← ENNReal.coe_rpow_of_nonneg _ (half_pos cfg.hϱ).le,
      ← ENNReal.coe_inv (NNReal.rpow_pos hδ0).ne', ENNReal.coe_le_coe,
      le_inv_comm₀ hKpos (NNReal.rpow_pos hδ0)]
    exact hKϱ
  rw [← hmult_eq]
  calc ShadedBody.multiplicity t (fun j ↦ (T' j).toShadedBody)
      ≤ (τ : ENNReal) ^ (-cfg.ckt.we) *
          (maxDensity t fun j ↦ (T' j).toConvexSpaceBody) ^ (1 - cfg.β) *
          (t.card : ENNReal) ^ cfg.β := hmult
    _ ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) *
          (maxDensity t fun j ↦ (T' j).toConvexSpaceBody) ^ (1 - cfg.β) *
          (t.card : ENNReal) ^ cfg.β := by gcongr
    _ ≤ (cfg.δ : ENNReal) ^ (-(4 * cfg.ϱ)) * (t.card : ENNReal) ^ cfg.β :=
        ktRho2_loss_arith hδ0 hδ1 cfg.hϱ cfg.hβ.le cfg.hβ1 (by exact_mod_cast hK1) hK4 hKT' _

/-- **Conjunct 4 at general `b`** (steps G8): the twin of
`Kakeya.VeryNotSticky.eventually_ktRho2ScaleData_degenerate` with the pin `cfg.b = cfg.δ`
replaced by the non-slab guard `cfg.b ≤ cfg.δ ^ (2 exscal)`. The four thresholds are arranged
from the `δ`-free data `C₀bd`, `exscal > 0`, `exscal ≤ 1/2`, `η > 0`, `ϱ > 0` exactly as in the
degenerate case; only the first two change shape, because they are now read on `ρ₂ ≤ δ^{exscal}`
rather than on `ρ₂ = δ^{1-exscal}`. The pin `cfg.β = β` is carried for the consumer and not
read. -/
theorem eventually_ktRho2ScaleData_nonslab {β exscal ϱ η : ℝ} (hη : 0 < η) (hϱ : 0 < ϱ)
    (hϱ1 : ϱ ≤ 1) (hexscal0 : 0 < exscal) (hexscal12 : exscal ≤ 1 / 2)
    (C₀bd : NNReal) (hC₀ : 1 ≤ C₀bd) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) → bd.C₀ = C₀bd →
      cfg.KTRho2ScaleData bd (4 * cfg.ϱ) (9 * cfg.η) (3 * cfg.ϱ) := by
  have hC₀pos : (0 : NNReal) < C₀bd := lt_of_lt_of_le zero_lt_one hC₀
  have hKpos : (0 : NNReal) < ktRho2EnclosureConstant C₀bd :=
    lt_of_lt_of_le zero_lt_one (one_le_ktRho2EnclosureConstant hC₀)
  have hT1 := eventually_rpow_le_of_pos_nnreal (a := exscal) hexscal0
    (c := (8 * C₀bd)⁻¹) (by positivity)
  have hT2 := eventually_rpow_le_of_pos_nnreal (a := η) hη
    (c := 6 / C₀bd) (div_pos (by norm_num) hC₀pos)
  have hT3 := eventually_rpow_le_of_pos_nnreal hη (c := (ktRho2EnclosureConstant C₀bd)⁻¹)
    (by positivity)
  have hT4 := eventually_rpow_le_of_pos_nnreal (half_pos hϱ)
    (c := (ktRho2EnclosureConstant C₀bd)⁻¹) (by positivity)
  filter_upwards [hT1, hT2, hT3, hT4] with δ h1 h2 h3 h4
  intro cfg bd hδ _hβ hη' hex hϱ' hb hC₀'
  subst hδ hη' hex hϱ' hC₀'
  have hρ2 : cfg.rho2 ≤ cfg.δ ^ cfg.exscal := rho2_le_rpow_exscal cfg hb
  refine ktRho2ScaleData_of_ckt_nonslab cfg bd hexscal12 hϱ1
    (le_trans hρ2 h1) ?_ h3 h4
  -- the window radius: `C₀ ρ₂ ≤ (C₀ δ^{η}) δ^{exscal-η} ≤ 6 δ^{exscal-η} ≤ wρ`
  have hsplit : cfg.δ ^ cfg.exscal = cfg.δ ^ cfg.η * cfg.δ ^ (cfg.exscal - cfg.η) := by
    rw [← NNReal.rpow_add cfg.hδ.ne']
    congr 1
    ring
  calc bd.C₀ * cfg.rho2 ≤ bd.C₀ * cfg.δ ^ cfg.exscal := by gcongr
    _ = (bd.C₀ * cfg.δ ^ cfg.η) * cfg.δ ^ (cfg.exscal - cfg.η) := by
        rw [hsplit, mul_assoc]
    _ ≤ 6 * cfg.δ ^ (cfg.exscal - cfg.η) := by
        gcongr
        calc bd.C₀ * cfg.δ ^ cfg.η ≤ bd.C₀ * (6 / bd.C₀) := by gcongr
          _ = 6 := mul_div_cancel₀ (6 : NNReal) hC₀pos.ne'
    _ ≤ cfg.ckt.wρ := cfg.ckt.hδrad

/-! ### Tripwires: the degenerate producers are instances of the twins -/

/-- At `b = δ` the angular scale is `ρ₂ = δ^{1-exscal}`. -/
theorem rho2_eq_of_b_eq_delta (cfg : VeryNotSticky.{u}) (hb : cfg.b = cfg.δ) :
    cfg.rho2 = cfg.δ ^ (1 - cfg.exscal) := by
  rw [VeryNotSticky.rho2, VeryNotSticky.r₁, hb, NNReal.rpow_sub cfg.hδ.ne', NNReal.rpow_one]

example (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (hb : cfg.b = cfg.δ) (hexscal12 : cfg.exscal ≤ 1 / 2) (hϱ1 : cfg.ϱ ≤ 1)
    (h8 : cfg.δ ^ (1 - cfg.exscal) ≤ (8 * bd.C₀)⁻¹)
    (hwρ : cfg.δ ^ (1 - 2 * cfg.exscal + cfg.η) ≤ 6 / bd.C₀)
    (hKη : cfg.δ ^ cfg.η ≤ (ktRho2EnclosureConstant bd.C₀)⁻¹)
    (hKϱ : cfg.δ ^ (cfg.ϱ / 2) ≤ (ktRho2EnclosureConstant bd.C₀)⁻¹) :
    cfg.KTRho2ScaleData bd (4 * cfg.ϱ) (9 * cfg.η) (3 * cfg.ϱ) := by
  have hC₀pos : (0 : NNReal) < bd.C₀ := lt_of_lt_of_le zero_lt_one bd.hC₀
  have hρ := rho2_eq_of_b_eq_delta cfg hb
  refine ktRho2ScaleData_of_ckt_nonslab cfg bd hexscal12 hϱ1 (by rw [hρ]; exact h8) ?_ hKη hKϱ
  have hsplit : cfg.δ ^ (1 - cfg.exscal) =
      cfg.δ ^ (1 - 2 * cfg.exscal + cfg.η) * cfg.δ ^ (cfg.exscal - cfg.η) := by
    rw [← NNReal.rpow_add cfg.hδ.ne']
    congr 1
    ring
  calc bd.C₀ * cfg.rho2 = (bd.C₀ * cfg.δ ^ (1 - 2 * cfg.exscal + cfg.η))
        * cfg.δ ^ (cfg.exscal - cfg.η) := by rw [hρ, hsplit, mul_assoc]
    _ ≤ 6 * cfg.δ ^ (cfg.exscal - cfg.η) := by
        gcongr
        calc bd.C₀ * cfg.δ ^ (1 - 2 * cfg.exscal + cfg.η) ≤ bd.C₀ * (6 / bd.C₀) := by gcongr
          _ = 6 := mul_div_cancel₀ (6 : NNReal) hC₀pos.ne'
    _ ≤ cfg.ckt.wρ := cfg.ckt.hδrad

/-! ### The Katz-Tao estimate at a general `delta`-free comparison constant

**Moved here from `Kakeya.DimensionThree.MainLemma2.TangentialSlabAlign`, byte for byte.** The
declarations below are the existing ones with `bd.C₀` replaced by a parameter `Cmp` and `bd.hC₀`
by `hCmp`; `bd` is otherwise used only for its index type `bd.ω`. Nothing about `bd.C₀` beyond
`1 ≤ bd.C₀` is used anywhere in the chain, so every occurrence of the comparison constant is a
`δ`-free threshold and none of them is an exponent — the exponents `(4ϱ, 9η, 3ϱ)` are
**identical**. They live here rather than in `TangentialSlabAlign` because conjunct 4 of
`Kakeya.VeryNotSticky.SideDataObligations` is read at
`Kakeya.VeryNotSticky.latticeRescaleConstant bd.C₀` since re-cut R5, and this file is where
that conjunct is discharged. -/

/-- **Tripwire**: at `Cmp = bd.C₀` the generalised predicate *is*
`Kakeya.VeryNotSticky.KTRho2ScaleData`, definitionally. This declaration fails to elaborate if
either body moves. -/
theorem ktRho2ScaleDataAt_at_C₀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (ε η₁ κ : ℝ) :
    cfg.KTRho2ScaleDataAt bd bd.C₀ ε η₁ κ ↔ cfg.KTRho2ScaleData bd ε η₁ κ := Iff.rfl

/-- The enclosure of `Kakeya.VeryNotSticky.exists_enclosing_shadedTubes_of_ktRho2` at a general
`δ`-free comparison constant. -/
theorem exists_enclosing_shadedTubes_of_ktRho2_at (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (Cmp : NNReal) (hCmp : 1 ≤ Cmp)
    {t : Finset bd.ω} (htne : t.Nonempty) (T : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ j ∈ t, (T j).carrier ⊆ closedBall 0 1)
    (hthick : ∀ j ∈ t, HasThicknesses (T j).carrier (2 * Cmp)
      ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)])
    {κ : ℝ} (hKTt : ConvexSpaceBody.IsKatzTao t (fun j ↦ (T j).toConvexSpaceBody)
      ((cfg.δ : ENNReal) ^ (-κ)))
    (hr8 : ((Cmp * cfg.rho2 : NNReal) : ℝ) ≤ 1 / 8) :
    ∃ T' : bd.ω → ShadedTube (Cmp * cfg.rho2) (EuclideanSpace ℝ (Fin 3)),
      (∀ j, (T' j).carrier ⊆ closedBall 0 1) ∧
      ShadedBody.multiplicity t (fun j ↦ (T' j).toShadedBody) = ShadedBody.multiplicity t T ∧
      ConvexSpaceBody.IsKatzTao t (fun j ↦ (T' j).toConvexSpaceBody)
        ((ktRho2EnclosureConstant Cmp : ENNReal) * (cfg.δ : ENNReal) ^ (-κ)) ∧
      ∀ x y : ENNReal, x ≤ (ShadedBody.fullness t T : ENNReal) →
        y * (ktRho2EnclosureConstant Cmp : ENNReal) ≤ x →
        y ≤ (ShadedBody.fullness t (fun j ↦ (T' j).toShadedBody) : ENNReal) := by
  have hδ0 : 0 < cfg.δ := cfg.hδ
  have hδ1 : cfg.δ ≤ 1 := cfg.hδ1
  have hC₀ : 1 ≤ Cmp := hCmp
  have hC₀pos : (0 : NNReal) < Cmp := lt_of_lt_of_le zero_lt_one hC₀
  set K : NNReal := ktRho2EnclosureConstant Cmp with hK_def
  set ρ : NNReal := cfg.rho2 with hρ_def
  -- `δ ≤ b ≤ ρ₂`
  have hr₁pos : 0 < cfg.r₁ := NNReal.rpow_pos hδ0
  have hr₁le : cfg.r₁ ≤ 1 := NNReal.rpow_le_one hδ1 cfg.hexscal.le
  have hδρ : cfg.δ ≤ ρ := by
    have hb : cfg.δ ≤ cfg.b := cfg.hdims.1.trans cfg.hdims.2.1
    refine hb.trans ?_
    rw [hρ_def, VeryNotSticky.rho2, le_div_iff₀ hr₁pos]
    exact mul_le_of_le_one_right bot_le hr₁le
  have hρpos : 0 < ρ := lt_of_lt_of_le hδ0 hδρ
  -- the tube scale `r = C₀ ρ₂`
  set r : NNReal := Cmp * ρ with hr_def
  have hr1 : r ≤ 1 := by
    have : (r : ℝ) ≤ 1 := hr8.trans (by norm_num)
    exact_mod_cast this
  -- the `1/8`-homothety of the family
  have h8 : (8⁻¹ : ℝ) ≠ 0 := by norm_num
  set W' : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j ↦ (T j).homothety (0 : EuclideanSpace ℝ (Fin 3)) h8 with hW'_def
  have hone_le_two : (1 : NNReal) ≤ 2 * Cmp := by
    calc (1 : NNReal) ≤ Cmp := hC₀
      _ = 1 * Cmp := (one_mul _).symm
      _ ≤ 2 * Cmp := by gcongr; norm_num
  -- enclosing tubes, shaded by the shrunk bodies; a default tube off `t`
  have hencl : ∀ j, ∃ Z : ShadedTube r (EuclideanSpace ℝ (Fin 3)), Z.carrier ⊆ closedBall 0 1 ∧
      (j ∈ t → (W' j).carrier ⊆ Z.carrier ∧ Z.shade = (W' j).shade ∧
        volume Z.carrier ≤ (K : ENNReal) * volume (W' j).carrier) := by
    intro j
    by_cases hj : j ∈ t
    · have hbdd : Bornology.IsBounded (W' j).carrier := (W' j).isCompact'.isBounded
      have hne : (W' j).carrier.Nonempty := (W' j).nonempty'
      have hball' : (W' j).carrier ⊆ closedBall 0 (1 / 8) :=
        homothety_carrier_subset_closedBall_eighth (T j).toConvexSpaceBody (hball j hj)
      have hth : thickness ℝ (W' j).carrier 1 ≤ r := by
        have h2C : thickness ℝ (T j).carrier 1 ≤ 2 * (Cmp : ℝ) * (ρ : ℝ) := by
          simpa using (hthick j hj 1).2
        have hbddT : Bornology.IsBounded (T j).carrier := (T j).isCompact'.isBounded
        calc thickness ℝ (W' j).carrier 1
            = thickness ℝ (AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) (8⁻¹ : ℝ) ''
                (T j).carrier) 1 := rfl
          _ = |(8⁻¹ : ℝ)| * thickness ℝ (T j).carrier 1 :=
              thickness_homothety_image_eq hbddT 0 h8 1
          _ ≤ |(8⁻¹ : ℝ)| * (2 * (Cmp : ℝ) * (ρ : ℝ)) := by gcongr
          _ ≤ (r : ℝ) := by
              rw [hr_def, NNReal.coe_mul, abs_of_pos (by norm_num : (0:ℝ) < 8⁻¹)]
              have : (0 : ℝ) ≤ (Cmp : ℝ) * ρ := by positivity
              nlinarith
      obtain ⟨x, y, hxy, hsubK, htube⟩ :=
        exists_tube_of_thickness_one_le hbdd hne hball' hth hr8
      refine ⟨shadedTubeOfSubset (Tube.mk' r hxy) (W' j) hsubK, htube, fun _ ↦
        ⟨hsubK, rfl, ?_⟩⟩
      -- volume comparison: `16 r² = K · 8⁻³ · ρ₂² / (6 (2C₀)³)`
      have hvolT : ENNReal.ofReal (((ρ : ℝ) ^ 2) / (6 * ((2 * Cmp : NNReal) : ℝ) ^ 3)) ≤
          volume (T j).carrier :=
        ofReal_le_volume_of_tubeProfile (T j).toConvexSpaceBody hone_le_two (hthick j hj)
      have hvolW' : volume (W' j).carrier = ENNReal.ofReal (1 / 512) * volume (T j).carrier :=
        volume_homothety_eighth (T j).toConvexSpaceBody
      calc volume (shadedTubeOfSubset (Tube.mk' r hxy) (W' j) hsubK).carrier
          = volume (Tube.mk' r hxy).carrier := rfl
        _ ≤ ((16 : NNReal) : ENNReal) * ((r : ENNReal) ^ (2 : ℕ)) :=
            tube_volume_le_sixteen_mul_sq hr1 _
        _ = (K : ENNReal) * (ENNReal.ofReal (1 / 512) *
              ENNReal.ofReal (((ρ : ℝ) ^ 2) / (6 * ((2 * Cmp : NNReal) : ℝ) ^ 3))) := by
            have hreal : (16 : ℝ) * ((r : ℝ)) ^ 2 =
                (K : ℝ) * (1 / 512 * (((ρ : ℝ) ^ 2) / (6 * ((2 * Cmp : NNReal) : ℝ) ^ 3))) := by
              rw [hK_def, ktRho2EnclosureConstant, hr_def]
              push_cast
              field_simp
              ring
            calc ((16 : NNReal) : ENNReal) * ((r : ENNReal) ^ (2 : ℕ))
                = ENNReal.ofReal ((16 : ℝ) * ((r : ℝ)) ^ 2) := by
                  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow r.coe_nonneg,
                    ENNReal.ofReal_coe_nnreal]
                  congr 1
                  simp
              _ = ENNReal.ofReal ((K : ℝ) *
                    (1 / 512 * (((ρ : ℝ) ^ 2) / (6 * ((2 * Cmp : NNReal) : ℝ) ^ 3)))) := by
                  rw [hreal]
              _ = (K : ENNReal) * (ENNReal.ofReal (1 / 512) *
                    ENNReal.ofReal (((ρ : ℝ) ^ 2) / (6 * ((2 * Cmp : NNReal) : ℝ) ^ 3))) := by
                  rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_mul (by norm_num),
                    ENNReal.ofReal_coe_nnreal]
        _ ≤ (K : ENNReal) * (ENNReal.ofReal (1 / 512) * volume (T j).carrier) := by gcongr
        _ = (K : ENNReal) * volume (W' j).carrier := by rw [hvolW']
    · -- default tube with empty shade, around the origin
      have hth0 : thickness ℝ ({(0 : EuclideanSpace ℝ (Fin 3))} : Set _) 1 ≤ r :=
        thickness_le_of_subset_closedBall (x := (0 : EuclideanSpace ℝ (Fin 3))) (by simp)
          r.coe_nonneg 1
      obtain ⟨x, y, hxy, -, htube⟩ :=
        exists_tube_of_thickness_one_le (K := {(0 : EuclideanSpace ℝ (Fin 3))})
          Bornology.isBounded_singleton (Set.singleton_nonempty _) (by simp) hth0 hr8
      let Z : ShadedTube r (EuclideanSpace ℝ (Fin 3)) :=
        { toTube := Tube.mk' r hxy
          shade := ∅
          measurableSet_shade := MeasurableSet.empty
          shade_subset := Set.empty_subset _ }
      exact ⟨Z, htube, fun h ↦ absurd h hj⟩
  choose T' hT' using hencl
  have hball' : ∀ j, (T' j).carrier ⊆ closedBall 0 1 := fun j ↦ (hT' j).1
  have hsubj : ∀ j ∈ t, (W' j).carrier ⊆ (T' j).carrier := fun j hj ↦ ((hT' j).2 hj).1
  have hshj : ∀ j ∈ t, (T' j).shade = (W' j).shade := fun j hj ↦ ((hT' j).2 hj).2.1
  have hvolj : ∀ j ∈ t, volume (T' j).carrier ≤ (K : ENNReal) * volume (W' j).carrier :=
    fun j hj ↦ ((hT' j).2 hj).2.2
  -- Katz–Tao control of the tube family: `Δ_max ≤ K δ^{-κ}`
  have hvce : ConvexSpaceBody.IsVolumeControlledEnlargement t (fun j ↦ (W' j).toConvexSpaceBody)
      (fun j ↦ (T' j).toConvexSpaceBody) (K : ENNReal) :=
    fun j hj ↦ ⟨hsubj j hj, hvolj j hj⟩
  have hKT' : ConvexSpaceBody.IsKatzTao t (fun j ↦ (T' j).toConvexSpaceBody)
      ((K : ENNReal) * (cfg.δ : ENNReal) ^ (-κ)) :=
    hvce.isKatzTao (hKTt.homothety 0 h8)
  refine ⟨T', hball', ?_, hKT', ?_⟩
  · -- same shades, and the homothety is exact for `μ`
    rw [ktRho2_multiplicity_congr_shade t (W := W') (fun j hj ↦ hshj j hj), hW'_def,
      ShadedBody.multiplicity_homothety]
  · intro x y hx hxy
    have hfullW' : x ≤ (ShadedBody.fullness t W' : ENNReal) := by
      rw [hW'_def, ShadedBody.fullness_homothety]
      exact hx
    have h0 : ∑ j ∈ t, volume (W' j).carrier ≠ 0 := by
      intro h
      obtain ⟨j, hj⟩ := htne
      have hj0 : volume (W' j).carrier = 0 := (Finset.sum_eq_zero_iff.mp h) j hj
      have hpos : 0 < volume (W' j).carrier := by
        rw [show volume (W' j).carrier = ENNReal.ofReal (1 / 512) * volume (T j).carrier from
          volume_homothety_eighth (T j).toConvexSpaceBody]
        have hT0 : 0 < volume (T j).carrier := by
          refine lt_of_lt_of_le ?_
            (ofReal_le_volume_of_tubeProfile (T j).toConvexSpaceBody hone_le_two (hthick j hj))
          rw [ENNReal.ofReal_pos]
          have : (0 : ℝ) < ρ := hρpos
          have : (0 : ℝ) < Cmp := hC₀pos
          positivity
        exact ENNReal.mul_pos (by simp) hT0.ne'
      exact hpos.ne' hj0
    exact le_fullness_of_enlargement (t := t) (V := W') (W := fun j ↦ (T' j).toShadedBody)
      (K := (K : ENNReal)) (fun j hj ↦ hshj j hj)
      (fun j hj ↦ measure_mono (hsubj j hj)) (fun j hj ↦ hvolj j hj) h0 hfullW' hxy


/-- The estimate of `Kakeya.VeryNotSticky.ktRho2ScaleData_of_ckt_nonslab` at a general `δ`-free
comparison constant, **at the same exponents `(4ϱ, 9η, 3ϱ)`**. -/
theorem ktRho2ScaleData_of_ckt_nonslab_at (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (Cmp : NNReal) (hCmp : 1 ≤ Cmp)
    (hexscal12 : cfg.exscal ≤ 1 / 2) (hϱ1 : cfg.ϱ ≤ 1)
    (h8 : cfg.rho2 ≤ (8 * Cmp)⁻¹)
    (hwρ : Cmp * cfg.rho2 ≤ cfg.ckt.wρ)
    (hKη : cfg.δ ^ cfg.η ≤ (ktRho2EnclosureConstant Cmp)⁻¹)
    (hKϱ : cfg.δ ^ (cfg.ϱ / 2) ≤ (ktRho2EnclosureConstant Cmp)⁻¹) :
    cfg.KTRho2ScaleDataAt bd Cmp (4 * cfg.ϱ) (9 * cfg.η) (3 * cfg.ϱ) := by
  intro t T hball hthick hKTt hfull
  rcases t.eq_empty_or_nonempty with rfl | htne
  · simp
  have hδ0 : 0 < cfg.δ := cfg.hδ
  have hδ1 : cfg.δ ≤ 1 := cfg.hδ1
  have hδ1' : (cfg.δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hη : 0 < cfg.η := cfg.hη
  have hC₀ : 1 ≤ Cmp := hCmp
  have hC₀pos : (0 : NNReal) < Cmp := lt_of_lt_of_le zero_lt_one hC₀
  set K : NNReal := ktRho2EnclosureConstant Cmp with hK_def
  have hK1 : (1 : NNReal) ≤ K := one_le_ktRho2EnclosureConstant hC₀
  have hKpos : (0 : NNReal) < K := lt_of_lt_of_le zero_lt_one hK1
  -- the tube scale `r = C₀ ρ₂`
  set r : NNReal := Cmp * cfg.rho2 with hr_def
  have hr8 : (r : ℝ) ≤ 1 / 8 := by
    have : r ≤ 1 / 8 := by
      calc r ≤ Cmp * (8 * Cmp)⁻¹ := by rw [hr_def]; exact mul_le_mul' le_rfl h8
        _ = 1 / 8 := by
            rw [mul_inv, ← mul_assoc, mul_comm Cmp, mul_assoc, mul_inv_cancel₀ hC₀pos.ne',
              mul_one, one_div]
    exact_mod_cast this
  have hδρ : cfg.δ ≤ cfg.rho2 := delta_le_rho2_general cfg
  have hδr : cfg.δ ≤ r := by
    calc cfg.δ ≤ cfg.rho2 := hδρ
      _ = 1 * cfg.rho2 := (one_mul _).symm
      _ ≤ Cmp * cfg.rho2 := by gcongr
  have hr0 : 0 < r := lt_of_lt_of_le hδ0 hδr
  have hrwρ : r ≤ cfg.ckt.wρ := hwρ
  -- the Katz–Tao parameter `τ = δ^L`, `L = max 1 (10η/wη)`
  have hwη : 0 < cfg.ckt.wη := cfg.ckt.hwη
  set L : ℝ := max 1 (10 * cfg.η / cfg.ckt.wη) with hL_def
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hL2 : 10 * cfg.η ≤ L * cfg.ckt.wη := by
    have := le_max_right 1 (10 * cfg.η / cfg.ckt.wη)
    rwa [div_le_iff₀ hwη] at this
  set τ : NNReal := cfg.δ ^ L with hτ_def
  have hτ0 : 0 < τ := NNReal.rpow_pos hδ0
  have hτr : τ ≤ r := by
    calc τ = cfg.δ ^ L := rfl
      _ ≤ cfg.δ ^ (1 : ℝ) := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hL1
      _ = cfg.δ := NNReal.rpow_one _
      _ ≤ r := hδr
  -- the enclosure
  obtain ⟨T', hball', hmult_eq, hKT', hfull'⟩ :=
    exists_enclosing_shadedTubes_of_ktRho2_at cfg bd Cmp hCmp htne T hball hthick hKTt hr8
  have hball4 : ∀ j, (T' j).carrier ⊆ closedBall 0 (4 : ℝ) := fun j ↦
    (hball' j).trans (closedBall_subset_closedBall (by norm_num))
  -- fullness of the tube family: `τ^{wη} ≤ δ^{10η} = δ^{9η} δ^{η} ≤ δ^{9η} / K`
  have hfullT' : ShadedBody.fullness t (fun j ↦ (T' j).toShadedBody) ≥ τ ^ cfg.ckt.wη := by
    have hτK : τ ^ cfg.ckt.wη * K ≤ cfg.δ ^ (9 * cfg.η) := by
      have hτw : τ ^ cfg.ckt.wη ≤ cfg.δ ^ (10 * cfg.η) := by
        rw [hτ_def, ← NNReal.rpow_mul]
        exact NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hL2
      have hsplit : cfg.δ ^ (10 * cfg.η) = cfg.δ ^ (9 * cfg.η) * cfg.δ ^ cfg.η := by
        rw [← NNReal.rpow_add hδ0.ne']
        congr 1
        ring
      have hηK : cfg.δ ^ cfg.η * K ≤ 1 := by
        calc cfg.δ ^ cfg.η * K ≤ K⁻¹ * K := mul_le_mul_of_nonneg_right hKη bot_le
          _ = 1 := inv_mul_cancel₀ hKpos.ne'
      calc τ ^ cfg.ckt.wη * K ≤ cfg.δ ^ (10 * cfg.η) * K := by gcongr
        _ = cfg.δ ^ (9 * cfg.η) * (cfg.δ ^ cfg.η * K) := by rw [hsplit, mul_assoc]
        _ ≤ cfg.δ ^ (9 * cfg.η) := mul_le_of_le_one_right bot_le hηK
    have := hfull' ((cfg.δ ^ (9 * cfg.η) : NNReal) : ENNReal)
      ((τ ^ cfg.ckt.wη : NNReal) : ENNReal)
      (by exact_mod_cast hfull) (by exact_mod_cast hτK)
    exact_mod_cast this
  -- the window bound at tube scale `r`, parameter `τ`
  have hmult := cfg.ckt.hwin r hr0 hrwρ τ hτ0 hτr t T' hball4 hfullT'
  -- the loss: `τ^{-we} = δ^{-we L} ≤ δ^{-ϱ/2}`
  have hloss : cfg.ckt.we * L ≤ cfg.ϱ / 2 :=
    ktRho2_window_loss_le cfg.hϱ hϱ1 hexscal12 cfg.ckt.hwe0 cfg.ckt.hwe cfg.ckt.hwb cfg.hβ1
      hwη cfg.ckt.hηKT
  have hτloss : (τ : ENNReal) ^ (-cfg.ckt.we) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) := by
    have hcoe : ((τ : NNReal) : ENNReal) = (cfg.δ : ENNReal) ^ L := by
      rw [hτ_def, ENNReal.coe_rpow_of_nonneg _ hL0]
    rw [hcoe, ← ENNReal.rpow_mul]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hδ1' (by nlinarith)
  have hK4 : (K : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) := by
    rw [ENNReal.rpow_neg, ← ENNReal.coe_rpow_of_nonneg _ (half_pos cfg.hϱ).le,
      ← ENNReal.coe_inv (NNReal.rpow_pos hδ0).ne', ENNReal.coe_le_coe,
      le_inv_comm₀ hKpos (NNReal.rpow_pos hδ0)]
    exact hKϱ
  rw [← hmult_eq]
  calc ShadedBody.multiplicity t (fun j ↦ (T' j).toShadedBody)
      ≤ (τ : ENNReal) ^ (-cfg.ckt.we) *
          (maxDensity t fun j ↦ (T' j).toConvexSpaceBody) ^ (1 - cfg.β) *
          (t.card : ENNReal) ^ cfg.β := hmult
    _ ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) *
          (maxDensity t fun j ↦ (T' j).toConvexSpaceBody) ^ (1 - cfg.β) *
          (t.card : ENNReal) ^ cfg.β := by gcongr
    _ ≤ (cfg.δ : ENNReal) ^ (-(4 * cfg.ϱ)) * (t.card : ENNReal) ^ cfg.β :=
        ktRho2_loss_arith hδ0 hδ1 cfg.hϱ cfg.hβ.le cfg.hβ1 (by exact_mod_cast hK1) hK4 hKT' _

/-- **The `∀ᶠ δ` form at a general `δ`-free comparison constant** — the measurement R3–R6 asks
for. The four thresholds `hT1`–`hT4` are re-arranged at `Cmp` and the conclusion carries the
**unchanged** exponents `(4ϱ, 9η, 3ϱ)`; the binder `bd.C₀ = C₀bd` of the existing statement is
gone, because `bd.C₀` no longer occurs. -/
theorem eventually_ktRho2ScaleDataAt_nonslab {β exscal ϱ η : ℝ} (hη : 0 < η) (hϱ : 0 < ϱ)
    (hϱ1 : ϱ ≤ 1) (hexscal0 : 0 < exscal) (hexscal12 : exscal ≤ 1 / 2)
    (Cmp : NNReal) (hCmp : 1 ≤ Cmp) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) →
      cfg.KTRho2ScaleDataAt bd Cmp (4 * cfg.ϱ) (9 * cfg.η) (3 * cfg.ϱ) := by
  have hC₀pos : (0 : NNReal) < Cmp := lt_of_lt_of_le zero_lt_one hCmp
  have hKpos : (0 : NNReal) < ktRho2EnclosureConstant Cmp :=
    lt_of_lt_of_le zero_lt_one (one_le_ktRho2EnclosureConstant hCmp)
  have hT1 := eventually_rpow_le_of_pos_nnreal (a := exscal) hexscal0
    (c := (8 * Cmp)⁻¹) (by positivity)
  have hT2 := eventually_rpow_le_of_pos_nnreal (a := η) hη
    (c := 6 / Cmp) (div_pos (by norm_num) hC₀pos)
  have hT3 := eventually_rpow_le_of_pos_nnreal hη (c := (ktRho2EnclosureConstant Cmp)⁻¹)
    (by positivity)
  have hT4 := eventually_rpow_le_of_pos_nnreal (half_pos hϱ)
    (c := (ktRho2EnclosureConstant Cmp)⁻¹) (by positivity)
  filter_upwards [hT1, hT2, hT3, hT4] with δ h1 h2 h3 h4
  intro cfg bd hδ _hβ hη' hex hϱ' hb
  subst hδ hη' hex hϱ'
  have hρ2 : cfg.rho2 ≤ cfg.δ ^ cfg.exscal := rho2_le_rpow_exscal cfg hb
  refine ktRho2ScaleData_of_ckt_nonslab_at cfg bd Cmp hCmp hexscal12 hϱ1
    (le_trans hρ2 h1) ?_ h3 h4
  -- the window radius: `C₀ ρ₂ ≤ (C₀ δ^{η}) δ^{exscal-η} ≤ 6 δ^{exscal-η} ≤ wρ`
  have hsplit : cfg.δ ^ cfg.exscal = cfg.δ ^ cfg.η * cfg.δ ^ (cfg.exscal - cfg.η) := by
    rw [← NNReal.rpow_add cfg.hδ.ne']
    congr 1
    ring
  calc Cmp * cfg.rho2 ≤ Cmp * cfg.δ ^ cfg.exscal := by gcongr
    _ = (Cmp * cfg.δ ^ cfg.η) * cfg.δ ^ (cfg.exscal - cfg.η) := by
        rw [hsplit, mul_assoc]
    _ ≤ 6 * cfg.δ ^ (cfg.exscal - cfg.η) := by
        gcongr
        calc Cmp * cfg.δ ^ cfg.η ≤ Cmp * (6 / Cmp) := by gcongr
          _ = 6 := mul_div_cancel₀ (6 : NNReal) hC₀pos.ne'
    _ ≤ cfg.ckt.wρ := cfg.ckt.hδrad

/-- **The punchline: (A2) at `Kakeya.VeryNotSticky.alignedRescaleConstant bd.C₀ κ` feeds the
Katz–Tao estimate at the existing exponents.** A direct instantiation of
`Kakeya.VeryNotSticky.eventually_ktRho2ScaleDataAt_nonslab` at
`Cmp := alignedRescaleConstant C₀bd κ`. No exponent moves; only the `∀ᶠ δ` threshold does.
This is the compiled form of "R3–R6 cost nothing". -/
theorem eventually_ktRho2ScaleDataAt_aligned {β exscal ϱ η : ℝ} (hη : 0 < η) (hϱ : 0 < ϱ)
    (hϱ1 : ϱ ≤ 1) (hexscal0 : 0 < exscal) (hexscal12 : exscal ≤ 1 / 2)
    (C₀bd κ : NNReal) (hC₀ : 1 ≤ C₀bd) (hκ : 1 ≤ κ) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) →
      cfg.KTRho2ScaleDataAt bd (alignedRescaleConstant C₀bd κ)
        (4 * cfg.ϱ) (9 * cfg.η) (3 * cfg.ϱ) := by
  have hone : (1 : NNReal) ≤ alignedRescaleConstant C₀bd κ := by
    have h4 : (1 : NNReal) ≤ C₀bd ^ 4 := one_le_pow₀ hC₀
    calc (1 : NNReal) = 1 * 1 * 1 := by norm_num
      _ ≤ 2304 * (3 + κ) * C₀bd ^ 4 := by
          gcongr
          · norm_num
          · exact hκ.trans le_add_self
      _ = alignedRescaleConstant C₀bd κ := rfl
  exact eventually_ktRho2ScaleDataAt_nonslab hη hϱ hϱ1 hexscal0 hexscal12 _ hone

/-! ### Conjunct 4 at the aligned comparison constant, and the `SlabMultKT` producer -/

/-- **Conjunct 4 of `Kakeya.VeryNotSticky.SideDataObligations`** (T10, route R15; re-cut R5):
for every small `δ`, every configuration at `(δ, β, η, exscal, ϱ)` with `b = δ` and every `bd`
with `bd.C₀ = C₀bd` satisfies
`cfg.KTRho2ScaleDataAt bd (latticeRescaleConstant bd.C₀) (4ϱ) (9·cfg.η) (3ϱ)`.

**Why the comparison constant moved.** Clauses (A2)/(A2′) of
`Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` are stated at
`Kakeya.VeryNotSticky.latticeRescaleConstant bd.C₀` :
at `bd.C₀` alone the transport does **not** deliver them at general `(a, b)`
(`Kakeya.VeryNotSticky.aniLin_rank_two_gap`). `Kakeya.VeryNotSticky.tangentialSlabMult` feeds
those clauses to `Kakeya.VeryNotSticky.SlabMultKT.estimate`, so the estimate is read at the same
constant. **No exponent moves**: `Kakeya.VeryNotSticky.eventually_ktRho2ScaleDataAt_aligned`
gives it at the unchanged `(4ϱ, 9η, 3ϱ)`, only the four `∀ᶠ δ` thresholds do. The pin
`cfg.β = β` is carried for the consumer and not read. -/
theorem eventually_ktRho2ScaleDataAt_degenerate {β exscal ϱ η : ℝ} (hη : 0 < η) (hϱ : 0 < ϱ)
    (hϱ1 : ϱ ≤ 1) (hexscal0 : 0 < exscal) (hexscal12 : exscal ≤ 1 / 2)
    (C₀bd : NNReal) (hC₀ : 1 ≤ C₀bd) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      cfg.KTRho2ScaleDataAt bd (latticeRescaleConstant bd.C₀)
        (4 * cfg.ϱ) (9 * cfg.η) (3 * cfg.ϱ) := by
  filter_upwards [eventually_ktRho2ScaleDataAt_nonslab (β := β) hη hϱ hϱ1 hexscal0 hexscal12
    (latticeRescaleConstant C₀bd) (one_le_latticeRescaleConstant hC₀)] with δ hm
  intro cfg bd hδ hβ hη' hex hϱ' hb hC₀'
  subst hC₀'
  have hguard : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) := by
    rw [hb]
    calc cfg.δ = cfg.δ ^ (1 : ℝ) := (NNReal.rpow_one _).symm
      _ ≤ cfg.δ ^ (2 * cfg.exscal) := by
          refine NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1 ?_
          rw [hex]; linarith
  exact hm cfg bd hδ hβ hη' hex hϱ' hguard

/-- **`SlabMultKT` on the degenerate path**, `∀ᶠ δ`: from the pins of conjunct 4 and the
density-constant threshold (T6's), `Nonempty (SlabMultKT cfg tc)`. -/
theorem eventually_nonempty_slabMultKT_degenerate {β exscal ϱ η : ℝ} (hη : 0 < η) (hϱ : 0 < ϱ)
    (hϱ1 : ϱ ≤ 1) (hexscal0 : 0 < exscal) (hexscal12 : exscal ≤ 1 / 2)
    (C₀bd : NNReal) (hC₀ : 1 ≤ C₀bd) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
      (tc : ThinConfig cfg bd),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) →
      Nonempty (SlabMultKT cfg tc) := by
  filter_upwards [eventually_ktRho2ScaleDataAt_degenerate (β := β) hη hϱ hϱ1 hexscal0
    hexscal12 C₀bd hC₀] with δ h
  intro cfg bd tc hδ hβ hη' hex hϱ' hb hC₀' hdens
  exact ⟨slabMultKTOfThresholds cfg tc (h cfg bd hδ hβ hη' hex hϱ' hb hC₀') hdens⟩

/-! ### Tripwires against `SideDataObligations` -/

/-- Tripwire (T10): the conclusion of `eventually_ktRho2ScaleDataAt_degenerate` **is** conjunct 4 of
`Kakeya.VeryNotSticky.SideDataObligations` — the other five conjuncts of a given
`SideDataObligations` re-assemble around it. -/
example {β exscal ϱ η τ τ' : ℝ} (hη : 0 < η) (hϱ : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hexscal0 : 0 < exscal) (hexscal12 : exscal ≤ 1 / 2)
    {C₀bd Cbias CF Cdil c₁ Cg : NNReal} (hC₀ : 1 ≤ C₀bd) {D : ℕ}
    (h : SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D) :
    SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D :=
  ⟨h.1, h.2.1, h.2.2.1,
    eventually_ktRho2ScaleDataAt_degenerate hη hϱ hϱ1 hexscal0 hexscal12 C₀bd hC₀,
    h.2.2.2.2⟩

/-- Tripwire (T10): conjunct 4 spelled out, as the expected type of `eventually_ktRho2ScaleDataAt_degenerate`. -/
example {β exscal ϱ η : ℝ} (hη : 0 < η) (hϱ : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hexscal0 : 0 < exscal) (hexscal12 : exscal ≤ 1 / 2)
    (C₀bd : NNReal) (hC₀ : 1 ≤ C₀bd) :
    (∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      cfg.KTRho2ScaleDataAt bd (latticeRescaleConstant bd.C₀)
        (4 * cfg.ϱ) (9 * cfg.η) (3 * cfg.ϱ)) :=
  eventually_ktRho2ScaleDataAt_degenerate hη hϱ hϱ1 hexscal0 hexscal12 C₀bd hC₀

/-- Tripwire (T10 → T12): the boundary theorem consumes `SideDataObligations` with conjunct 4
supplied by this file (the five remaining obligations as hypotheses). -/
example {β ζ exscal ϱ η τ τ' : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (hϱ1 : ϱ ≤ 1) (hexscal0 : 0 < exscal) (hexscal12 : exscal ≤ 1 / 2)
    {C₀bd Cbias CF Cdil c₁ Cg : NNReal} (hC₀bd : 4 ≤ C₀bd) {D : ℕ} (hD : ballCoverConstant ≤ D)
    (h : SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D) :
    SideDataResidue.{u} β ζ exscal ϱ η τ τ' :=
  sideDataResidue_of_sideDataObligations hβ hβ1 hζ hexscal hϱ hη hC₀bd hD
    ⟨h.1, h.2.1, h.2.2.1,
      eventually_ktRho2ScaleDataAt_degenerate hη hϱ hϱ1 hexscal0 hexscal12 C₀bd
        (le_trans (by norm_num) hC₀bd),
      h.2.2.2.2⟩

end Kakeya.VeryNotSticky
