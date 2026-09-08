/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SplitInputsFibreCount

/-!
# The splitting inputs and the fibre scale count at general `b`

General-branch steps **G8** and **G8b**, cut as **new
twins** of the existing degenerate theorems — the licence-free alternative  names
itself. **No existing statement is edited**; each twin's degenerate instance is recorded as a
tripwire `example` below, which is the compiled certificate that the twin really does generalise
its degenerate ancestor.

## The one hypothesis that moves

Every existing degenerate producer in this chain spends `cfg.b = cfg.δ` **exactly once**, and only
to derive the non-slab hypothesis

  `cfg.b ≤ cfg.δ ^ exscal · r₁`   (`Kakeya.VeryNotSticky.rho2Star_range`,
                                   `Kakeya.VeryNotSticky.rho2_range`).

Since `Kakeya.VeryNotSticky.r₁ = cfg.δ ^ exscal`, that hypothesis is literally
`cfg.b ≤ cfg.δ ^ (2 exscal)` (`Kakeya.VeryNotSticky.rpow_exscal_mul_r₁`), which is the guard the
statement pack SP-A puts in place of the pin. So the twins take `cfg.b ≤ cfg.δ ^ (2 exscal)` and
are otherwise the existing proofs verbatim.

Two facts that were *consequences of the pin* in the degenerate proofs are theorems of `cfg`
alone at general `b` and are therefore **not** hypotheses here:

* `cfg.a ≤ cfg.rho2Star C₀` — from `cfg.hdims` (`a ≤ b`) and `b ≤ b / r₁ = ρ₂`
  (`Kakeya.VeryNotSticky.b_le_rho2`, using `r₁ ≤ 1`), never from `b = δ`;
* `cfg.δ ≤ cfg.rho2` — likewise (`Kakeya.VeryNotSticky.delta_le_rho2_general`).

`Kakeya.VeryNotSticky.exists_splitLevel` moreover needed `exscal ≤ 1/2` **only** to turn
`b = δ` into the non-slab hypothesis; `Kakeya.VeryNotSticky.exists_splitLevel_of_notslab` does
not take it. That is a hypothesis deleted rather than kept as decoration.

## What is discharged

* `Kakeya.VeryNotSticky.eventually_exists_splitInputs_nonslab` — T8 at general `b`, hence
  conjunct 4's antecedent chain.
* `Kakeya.VeryNotSticky.eventually_exists_fibreScaleCount_nonslab` — conjunct 5 (R17) at
  general `b`, at the same measured exponent `M = 18`.

Nothing here changes a existing statement.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped NNReal ENNReal Topology

universe u

namespace Kakeya.VeryNotSticky

/-! ### The non-slab hypothesis, written without `r₁` -/

/-- `δ^{exscal} · r₁ = δ^{2 exscal}`: the non-slab hypothesis of
`Kakeya.VeryNotSticky.rho2Star_range` is the guard `b ≤ δ^{2 exscal}` of the general-branch
statement pack, on the nose. -/
theorem rpow_exscal_mul_r₁ (cfg : VeryNotSticky.{u}) :
    cfg.δ ^ cfg.exscal * cfg.r₁ = cfg.δ ^ (2 * cfg.exscal) := by
  rw [VeryNotSticky.r₁, ← NNReal.rpow_add cfg.hδ.ne']
  congr 1
  ring

/-- The two forms of the non-slab hypothesis agree. -/
theorem notSlab_iff (cfg : VeryNotSticky.{u}) :
    cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁ ↔ cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) := by
  rw [rpow_exscal_mul_r₁]

theorem r₁_le_one' (cfg : VeryNotSticky.{u}) : cfg.r₁ ≤ 1 :=
  NNReal.rpow_le_one cfg.hδ1 cfg.hexscal.le

/-- `b ≤ ρ₂ = b / r₁`, since `r₁ ≤ 1`. No hypothesis on `b` is involved. -/
theorem b_le_rho2 (cfg : VeryNotSticky.{u}) : cfg.b ≤ cfg.rho2 := by
  have hr₁0 : 0 < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  rw [VeryNotSticky.rho2, le_div_iff₀ hr₁0]
  calc cfg.b * cfg.r₁ ≤ cfg.b * 1 := by gcongr; exact r₁_le_one' cfg
    _ = cfg.b := mul_one _

/-- `δ ≤ ρ₂` at general `b`, from `cfg.hdims` alone. -/
theorem delta_le_rho2_general (cfg : VeryNotSticky.{u}) : cfg.δ ≤ cfg.rho2 :=
  le_trans (cfg.hdims.1.trans cfg.hdims.2.1) (b_le_rho2 cfg)

/-- `a ≤ ρ₂* (C₀)` at general `b`, from `cfg.hdims` and `r₁ ≤ 1`. In the degenerate proofs this
came out of the pin `b = δ`; it does not need it. -/
theorem a_le_rho2Star (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    cfg.a ≤ cfg.rho2Star C₀ :=
  le_trans (le_trans cfg.hdims.2.1 (b_le_rho2 cfg)) (rho2_le_rho2Star cfg hC₀)

/-! ### G8: the grid level at `ρ₂*` at general `b` -/

/-- **`Kakeya.VeryNotSticky.exists_splitLevel` at general `b`** (steps G8). The degenerate
theorem's hypotheses `cfg.exscal ≤ 1/2` and `cfg.b = cfg.δ` served only to produce the non-slab
hypothesis; taking the latter directly, both disappear. -/
theorem exists_splitLevel_of_notslab (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    (hscale : cfg.δ ^ cfg.exscal ≤ (2 * NonSlab.bodyAngleConstant C₀)⁻¹)
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal)) :
    ∃ k ≤ Tube.ssfGridLen cfg.δ,
      cfg.rho2Star C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ∧
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star C₀ := by
  obtain ⟨-, -, hρ1⟩ := rho2Star_range cfg cfg.hδ cfg.hδ1 hC₀ hscale
    ((notSlab_iff cfg).2 hnotslab)
  exact exists_gridIndex cfg (a_le_rho2Star cfg hC₀) hρ1

/-- **T8 at general `b`** (steps G8): the twin of
`Kakeya.VeryNotSticky.eventually_exists_splitInputs_degenerate` with the pin `cfg.b = cfg.δ`
replaced by the non-slab guard `cfg.b ≤ cfg.δ ^ (2 exscal)`. Every other hypothesis, and the
whole `∀ Cang … ∀ Ccnt …` tail, is unchanged. -/
theorem eventually_exists_splitInputs_nonslab (C₀ : NNReal) (hC₀ : 1 ≤ C₀)
    {exscal ϱ η : ℝ} (hη : 0 < η) (hexscal0 : 0 < exscal) (hexscal : exscal ≤ 1 / 2)
    (hϱ1 : ϱ ≤ 1) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
        cfg.δ = d → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → bd.C₀ = C₀ →
        cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) →
        ∃ k ≤ Tube.ssfGridLen cfg.δ,
          cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ∧
          Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ ∧
          ∀ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) →
            (∀ j ∈ cfg.activeTubeNodes cfg.splitHierarchy k,
              ∀ x v : EuclideanSpace ℝ (Fin 3),
                (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                  (Cang : ENNReal) *
                    ShadedBody.multiplicity (cfg.tubeFibre cfg.splitHierarchy k j)
                      (fun i ↦ (cfg.T i).toShadedBody)) →
            ∀ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) →
              (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
                (Ccnt : ℝ) * ((cfg.splitHierarchy.cover.indexSet k).card : ℝ) →
              Nonempty (SplitInputs cfg bd) := by
  have hpos : (0 : NNReal) < (2 * NonSlab.bodyAngleConstant C₀)⁻¹ := by
    have h1 : (1 : NNReal) ≤ 2 * NonSlab.bodyAngleConstant C₀ :=
      one_le_mul_of_one_le_of_one_le (by norm_num) (NonSlab.one_le_bodyAngleConstant hC₀)
    exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one h1)
  have hKtop : ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ENNReal) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.coe_ne_top
  filter_upwards [eventually_nnreal_mul_rpow_le_const 1 _ hpos hexscal0,
    eventually_ennreal_le_rpow_neg hKtop (by positivity : (0 : ℝ) < 3 * η / 4)]
    with d hscale hthr
  intro cfg bd hδ hη' hexs hϱ' hC₀' hb
  subst hδ hη' hexs hϱ' hC₀'
  rw [one_mul] at hscale
  obtain ⟨k, hk, hge, hle⟩ := exists_splitLevel_of_notslab cfg hC₀ hscale hb
  refine ⟨k, hk, hge, hle, fun Cang hCang hang Ccnt hCcnt hfsc ↦ ?_⟩
  exact ⟨SplitInputs.ofLevel cfg bd cfg.splitHierarchy hk hge hle
    (ktScaleData_of_ckt cfg hexscal hϱ1) (fibreConstant_of_threshold cfg hthr)
    Cang hCang hang Ccnt hCcnt hfsc⟩

/-! ### G8b: conjunct 5 (R17) at general `b` -/

/-- **`Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData` at general `b`** (steps
G8b). The existing proof reads the pin `cfg.b = cfg.δ` exactly once, to produce the non-slab
hypothesis of `Kakeya.VeryNotSticky.rho2_range`; the rest of the chain — the count clause at
`ρ = ρ₂`, `Kakeya.VeryNotSticky.card_count_le_mul_card_indexSet`,
`Kakeya.VeryNotSticky.card_indexSet_parent_le`, and the packing arithmetic ending at
`A δ^{-17η}` — never mentions `b`. The measured exponent `M = 18` is unchanged. -/
theorem exists_fibreScaleCount_of_rhoParentData_nonslab (cfg : VeryNotSticky.{u})
    (bd : BallData cfg) (hC₀bd : 1 ≤ bd.C₀) (hexscal : cfg.exscal ≤ 1 / 2)
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    (hthr : (fibreCountConstant bd.C₀ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η))
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hle : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k
      ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀) :
    ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
      (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
        ((cfg.splitHierarchy.cover.indexSet k).card : ℝ) := by
  classical
  have hδ0 : 0 < cfg.δ := cfg.hδ
  have hδ1 : cfg.δ ≤ 1 := cfg.hδ1
  have hCba : (1 : NNReal) ≤ NonSlab.bodyAngleConstant bd.C₀ :=
    NonSlab.one_le_bodyAngleConstant hC₀bd
  set ρk : NNReal := Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k with hρk
  set ρ2 : NNReal := cfg.rho2 with hρ2
  obtain ⟨hwin, -⟩ := rho2_range cfg hδ0 hδ1 hexscal ((notSlab_iff cfg).2 hnotslab)
  have hwinb : ρ2 ∈ Set.Icc (cfg.δ ^ (1 - cfg.exscalb)) (cfg.δ ^ cfg.exscalb) := by
    rw [← cfg.hscale]; exact hwin
  have hρ20 : 0 < ρ2 := lt_of_lt_of_le (NNReal.rpow_pos hδ0) hwinb.1
  have hρk1 : ρk ≤ 1 := Tube.gridScale_le_one hδ1 _ _
  have hρ2ρk : ρ2 ≤ ρk := (rho2_le_rho2Star cfg hC₀bd).trans hge
  -- the parent datum
  obtain ⟨sPar, hsub, -, -, hretE, ⟨Cpar, hCpar1, hCparE, ⟨𝒰par⟩⟩, hcount⟩ := cfg.rho_count
  obtain ⟨κ, tρ, Tρ, hED, hused, hcard⟩ := hcount ρ2 hwinb
  have hCpar : Cpar ≤ cfg.δ ^ (-cfg.η) := le_rpow_neg_of_coe_le hδ0 hCparE
  have hret : cfg.δ ^ (2 * cfg.η) * (sPar.card : NNReal) ≤ (cfg.s.card : NNReal) :=
    mul_le_of_coe_mul_le hδ0 hretE
  have hne : sPar.Nonempty := by
    rcases tρ.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
    · exfalso
      simp only [Finset.card_empty, Nat.cast_zero] at hcard
      exact absurd hcard (not_le.2 (Real.rpow_pos_of_pos (NNReal.coe_pos.2 hρ20) _))
    · obtain ⟨i₀, hi₀, -⟩ := hused j₀ hj₀
      exact ⟨i₀, hi₀⟩
  -- step 1: the count on the parent's nodes
  have hstep1 : (tρ.card : ℝ) ≤
      (Tube.essDistinctTubesInSelfDilate.C 3 (32 * (ρk : ℝ) / (ρ2 : ℝ)) : ℝ)
        * ((𝒰par.cover.indexSet k).card : ℝ) :=
    card_count_le_mul_card_indexSet 𝒰par hk hρ20 (by exact_mod_cast hρ2ρk)
      (by exact_mod_cast hρk1) tρ Tρ hED hused
  -- step 2: the parent's nodes against the family's
  have hstep2 : cfg.δ ^ (2 * cfg.η) * ((𝒰par.cover.indexSet k).card : NNReal)
      ≤ Cpar ^ 3 * ((cfg.splitHierarchy.cover.indexSet k).card : NNReal) :=
    card_indexSet_parent_le 𝒰par cfg.splitHierarchy hsub hne hk hret
  set A : NNReal := fibreCountConstant bd.C₀ with hA
  set R : NNReal := 64 * NonSlab.bodyAngleConstant bd.C₀ * cfg.δ ^ (-cfg.η) with hR
  have hρ20R : (0 : ℝ) < (ρ2 : ℝ) := NNReal.coe_pos.2 hρ20
  rw [rho2Star] at hle
  have hNN : 32 * ρk ≤ R * ρ2 := by
    calc 32 * ρk
        ≤ 32 * (cfg.δ ^ (-cfg.η) * (2 * NonSlab.bodyAngleConstant bd.C₀ * ρ2)) := by
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = R * ρ2 := by rw [hR]; ring
  have hratio : 32 * (ρk : ℝ) / (ρ2 : ℝ) ≤ (R : ℝ) := by
    rw [div_le_iff₀ hρ20R]
    have := NNReal.coe_le_coe.2 hNN
    push_cast at this
    linarith [this]
  have hratio1 : (1 : ℝ) ≤ 32 * (ρk : ℝ) / (ρ2 : ℝ) := by
    rw [le_div_iff₀ hρ20R]
    have : (ρ2 : ℝ) ≤ (ρk : ℝ) := by exact_mod_cast hρ2ρk
    linarith
  have hpow3 : (cfg.δ ^ (-cfg.η)) ^ (3 : ℕ) = cfg.δ ^ (-((3 : ℝ) * cfg.η)) := by
    rw [← NNReal.rpow_natCast (cfg.δ ^ (-cfg.η)) 3, ← NNReal.rpow_mul]
    congr 1
    push_cast
    ring
  have hpow12 : (cfg.δ ^ (-cfg.η)) ^ (12 : ℕ) = cfg.δ ^ (-((12 : ℝ) * cfg.η)) := by
    rw [← NNReal.rpow_natCast (cfg.δ ^ (-cfg.η)) 12, ← NNReal.rpow_mul]
    congr 1
    push_cast
    ring
  have hPle : Tube.essDistinctTubesInSelfDilate.C 3 (32 * (ρk : ℝ) / (ρ2 : ℝ))
      ≤ A * cfg.δ ^ (-((12 : ℝ) * cfg.η)) := by
    refine (essDistinctTubesInSelfDilate_C_le hratio1).trans ?_
    have hR12 : (32 * (ρk : ℝ) / (ρ2 : ℝ)).toNNReal ^ 12 ≤ R ^ 12 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 12
      have h := Real.toNNReal_le_toNNReal hratio
      rwa [Real.toNNReal_coe] at h
    refine le_trans (mul_le_mul_of_nonneg_left hR12 (by positivity)) ?_
    rw [hR, hA, fibreCountConstant, mul_pow, ← mul_assoc, hpow12]
  have hc0 : (0 : NNReal) < cfg.δ ^ (2 * cfg.η) := NNReal.rpow_pos hδ0
  have hIdx : ((𝒰par.cover.indexSet k).card : NNReal)
      ≤ Cpar ^ 3 * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
          ((cfg.splitHierarchy.cover.indexSet k).card : NNReal) := by
    have hinv : cfg.δ ^ (-((2 : ℝ) * cfg.η)) = (cfg.δ ^ (2 * cfg.η))⁻¹ := by
      rw [← NNReal.rpow_neg]
    calc ((𝒰par.cover.indexSet k).card : NNReal)
        = (cfg.δ ^ (2 * cfg.η))⁻¹ * (cfg.δ ^ (2 * cfg.η)
            * ((𝒰par.cover.indexSet k).card : NNReal)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul]
      _ ≤ (cfg.δ ^ (2 * cfg.η))⁻¹ * (Cpar ^ 3
            * ((cfg.splitHierarchy.cover.indexSet k).card : NNReal)) := by gcongr
      _ = Cpar ^ 3 * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
            ((cfg.splitHierarchy.cover.indexSet k).card : NNReal) := by rw [hinv]; ring
  have hCpar3 : Cpar ^ 3 ≤ cfg.δ ^ (-((3 : ℝ) * cfg.η)) := by
    refine le_trans (pow_le_pow_left₀ (by positivity) hCpar 3) ?_
    rw [hpow3]
  have hadd : cfg.δ ^ (-((12 : ℝ) * cfg.η)) * (cfg.δ ^ (-((3 : ℝ) * cfg.η))
      * cfg.δ ^ (-((2 : ℝ) * cfg.η))) = cfg.δ ^ (-((17 : ℝ) * cfg.η)) := by
    rw [← NNReal.rpow_add hδ0.ne', ← NNReal.rpow_add hδ0.ne']
    congr 1
    ring
  refine ⟨A * cfg.δ ^ (-((17 : ℝ) * cfg.η)), ?_, ?_⟩
  · have hAle : A ≤ cfg.δ ^ (-cfg.η) := le_rpow_neg_of_coe_le hδ0 hthr
    have : A * cfg.δ ^ (-((17 : ℝ) * cfg.η)) ≤ cfg.δ ^ (-(18 * cfg.η)) := by
      refine le_trans (mul_le_mul_of_nonneg_right hAle (by positivity)) ?_
      rw [← NNReal.rpow_add hδ0.ne']
      exact le_of_eq (by congr 1; ring)
    calc ((A * cfg.δ ^ (-((17 : ℝ) * cfg.η)) : NNReal) : ENNReal)
        ≤ ((cfg.δ ^ (-(18 * cfg.η)) : NNReal) : ENNReal) := by exact_mod_cast this
      _ = (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) :=
          ENNReal.coe_rpow_of_ne_zero hδ0.ne' _
  · have hkeyN : Tube.essDistinctTubesInSelfDilate.C 3 (32 * (ρk : ℝ) / (ρ2 : ℝ))
        * ((𝒰par.cover.indexSet k).card : NNReal)
        ≤ A * cfg.δ ^ (-((17 : ℝ) * cfg.η))
          * ((cfg.splitHierarchy.cover.indexSet k).card : NNReal) := by
      calc Tube.essDistinctTubesInSelfDilate.C 3 (32 * (ρk : ℝ) / (ρ2 : ℝ))
            * ((𝒰par.cover.indexSet k).card : NNReal)
          ≤ (A * cfg.δ ^ (-((12 : ℝ) * cfg.η)))
              * (Cpar ^ 3 * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
                ((cfg.splitHierarchy.cover.indexSet k).card : NNReal)) := by
            exact mul_le_mul' hPle hIdx
        _ ≤ (A * cfg.δ ^ (-((12 : ℝ) * cfg.η)))
              * (cfg.δ ^ (-((3 : ℝ) * cfg.η)) * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
                ((cfg.splitHierarchy.cover.indexSet k).card : NNReal)) := by
            gcongr
        _ = A * (cfg.δ ^ (-((12 : ℝ) * cfg.η)) * (cfg.δ ^ (-((3 : ℝ) * cfg.η))
              * cfg.δ ^ (-((2 : ℝ) * cfg.η))))
              * ((cfg.splitHierarchy.cover.indexSet k).card : NNReal) := by ring
        _ = A * cfg.δ ^ (-((17 : ℝ) * cfg.η))
              * ((cfg.splitHierarchy.cover.indexSet k).card : NNReal) := by rw [hadd]
    have hkeyR : (Tube.essDistinctTubesInSelfDilate.C 3 (32 * (ρk : ℝ) / (ρ2 : ℝ)) : ℝ)
        * ((𝒰par.cover.indexSet k).card : ℝ)
        ≤ ((A * cfg.δ ^ (-((17 : ℝ) * cfg.η)) : NNReal) : ℝ)
          * ((cfg.splitHierarchy.cover.indexSet k).card : ℝ) := by
      have := NNReal.coe_le_coe.2 hkeyN
      push_cast at this ⊢
      linarith [this]
    linarith [hcard, hstep1, hkeyR]

/-- **Conjunct 5 at general `b`** (steps G8b): the twin of
`Kakeya.VeryNotSticky.eventually_exists_fibreScaleCount` with the pin replaced by the non-slab
guard. The single threshold on `δ` is unchanged (the absorption of the `δ`-free
`Kakeya.VeryNotSticky.fibreCountConstant C₀bd` into one `η`). -/
theorem eventually_exists_fibreScaleCount_nonslab (exscal η : ℝ) (C₀bd : NNReal)
    (hC₀bd : 1 ≤ C₀bd) (hexscal : exscal ≤ 1 / 2) (hη : 0 < η) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal →
      cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) → bd.C₀ = C₀bd →
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
          (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
            ((cfg.splitHierarchy.cover.indexSet k).card : ℝ) := by
  filter_upwards [eventually_ennreal_le_rpow_neg
    (K := ((fibreCountConstant C₀bd : NNReal) : ENNReal)) ENNReal.coe_ne_top hη] with δ hδthr
  intro cfg bd hδ hη' hex hb hC₀ k hk hge hle
  refine exists_fibreScaleCount_of_rhoParentData_nonslab cfg bd (by rw [hC₀]; exact hC₀bd)
    (by rw [hex]; exact hexscal) hb ?_ hk hge hle
  rw [hC₀, hδ, hη']
  exact hδthr

/-! ### Tripwires: the degenerate statements are instances of the twins

The three `example`s below are the compiled certificates that the twins really generalise their
existing degenerate ancestors: each states the *existing* statement's conclusion under the *existing*
hypotheses and proves it from the twin, the pin `cfg.b = cfg.δ` being converted to the non-slab
guard by `δ ≤ δ^{2 exscal}` at `exscal ≤ 1/2`. No existing declaration is edited; the corollary
direction is recorded here instead. -/

/-- `b = δ` and `exscal ≤ 1/2` imply the non-slab guard. -/
theorem notslab_of_b_eq_delta (cfg : VeryNotSticky.{u}) (hexscal : cfg.exscal ≤ 1 / 2)
    (hb : cfg.b = cfg.δ) : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) := by
  rw [hb]
  calc cfg.δ = cfg.δ ^ (1 : ℝ) := (NNReal.rpow_one _).symm
    _ ≤ cfg.δ ^ (2 * cfg.exscal) :=
        NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1 (by linarith)

example (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    (hexscal : cfg.exscal ≤ 1 / 2)
    (hscale : cfg.δ ^ cfg.exscal ≤ (2 * NonSlab.bodyAngleConstant C₀)⁻¹)
    (hb : cfg.b = cfg.δ) :
    ∃ k ≤ Tube.ssfGridLen cfg.δ,
      cfg.rho2Star C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ∧
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star C₀ :=
  exists_splitLevel_of_notslab cfg hC₀ hscale (notslab_of_b_eq_delta cfg hexscal hb)

example (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (hC₀bd : 1 ≤ bd.C₀)
    (hexscal : cfg.exscal ≤ 1 / 2) (hb : cfg.b = cfg.δ)
    (hthr : (fibreCountConstant bd.C₀ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η))
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hle : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k
      ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀) :
    ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
      (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
        ((cfg.splitHierarchy.cover.indexSet k).card : ℝ) :=
  exists_fibreScaleCount_of_rhoParentData_nonslab cfg bd hC₀bd hexscal
    (notslab_of_b_eq_delta cfg hexscal hb) hthr hk hge hle

end Kakeya.VeryNotSticky
