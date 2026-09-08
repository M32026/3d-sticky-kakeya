/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SplitInputsGeneral
public import Kakeya.DimensionThree.MainLemma2.SplitInputsFibreCountDischarge

/-!
`Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData_hier`
(`SplitInputsFibreCountDischarge.lean`) makes the hierarchy choice immaterial to
conjunct 5 on the degenerate path `b = δ`: the count holds at *every* exact uniform hierarchy of
`cfg.s`, at every uniformity constant, not only at the `Classical.choice` pick
`Kakeya.VeryNotSticky.splitHierarchy = cfg.uniform.some.tubeUniform`.

The general-`b` twin `Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData_nonslab`
(steps G8b, `SplitInputsGeneral.lean`) carries the same defect, for the same reason and with the
same remedy. This file replays the substitution there:

* `Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData_nonslab_hier` — the general-`b`
  count over an explicit binder `𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
  (Tube.ssfGridLen cfg.δ) C`, at arbitrary `C`;
* `Kakeya.VeryNotSticky.eventually_exists_fibreScaleCount_nonslab_forall_hier` — its `∀ᶠ δ` form
  with the hierarchy binder *inside*, so one `δ`-threshold serves every hierarchy;
* `Kakeya.VeryNotSticky.exists_fibreScaleCount_nonslab_iff_of_hier` — the clause at `𝒰` iff the
  clause at `𝒱`, with no comparison loss.

As in `SplitInputsGeneral.lean`, **no existing statement is edited**: the two existing theorems this
generalises are recorded below as tripwire `example`s, which are the compiled certificates that
the binder version really does subsume them — the general-`b` existing twin at
`𝒰 := cfg.splitHierarchy`, and the degenerate binder version at the pin `cfg.b = cfg.δ` via
`Kakeya.VeryNotSticky.notslab_of_b_eq_delta`.

The exponent is the measured `M = 18` throughout, unchanged: the target hierarchy is consumed
only by `Kakeya.VeryNotSticky.card_indexSet_parent_le`, whose second hierarchy argument is a bare
binder and whose loss `Cpar³/δ^{2η}` involves only the *parent's* Definition 2.1 constant and the
retention of `cfg.rho_count : Kakeya.VeryNotSticky.RhoParentData`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped NNReal ENNReal Topology

namespace Kakeya.VeryNotSticky

open Produce

universe u

/-! ### G8b at an arbitrary exact uniform hierarchy of `cfg.s` -/

/-- **`Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData_nonslab` at any hierarchy.**

Word for word the existing general-`b` twin, except that the `Classical.choice` pick
`cfg.splitHierarchy` is replaced by an explicit binder `𝒰` ranging over every exact uniform
hierarchy of `cfg.s` at the grid length `Tube.ssfGridLen cfg.δ`, at an arbitrary constant `C`.

Both moving parts are therefore removed at once: the pin `cfg.b = cfg.δ` (already replaced by
the non-slab guard `cfg.b ≤ cfg.δ ^ (2 exscal)` in the existing twin) and the choice of hierarchy. The measured exponent `M = 18` and the threshold `hthr` are
unchanged, because no factor of the target hierarchy's own constant is ever incurred. -/
theorem exists_fibreScaleCount_of_rhoParentData_nonslab_hier (cfg : VeryNotSticky.{u})
    (bd : BallData cfg) {C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) C)
    (hC₀bd : 1 ≤ bd.C₀) (hexscal : cfg.exscal ≤ 1 / 2)
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    (hthr : (fibreCountConstant bd.C₀ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η))
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hle : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k
      ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀) :
    ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
      (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
        ((𝒰.cover.indexSet k).card : ℝ) := by
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
      ≤ Cpar ^ 3 * ((𝒰.cover.indexSet k).card : NNReal) :=
    card_indexSet_parent_le 𝒰par 𝒰 hsub hne hk hret
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
          ((𝒰.cover.indexSet k).card : NNReal) := by
    have hinv : cfg.δ ^ (-((2 : ℝ) * cfg.η)) = (cfg.δ ^ (2 * cfg.η))⁻¹ := by
      rw [← NNReal.rpow_neg]
    calc ((𝒰par.cover.indexSet k).card : NNReal)
        = (cfg.δ ^ (2 * cfg.η))⁻¹ * (cfg.δ ^ (2 * cfg.η)
            * ((𝒰par.cover.indexSet k).card : NNReal)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul]
      _ ≤ (cfg.δ ^ (2 * cfg.η))⁻¹ * (Cpar ^ 3
            * ((𝒰.cover.indexSet k).card : NNReal)) := by gcongr
      _ = Cpar ^ 3 * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
            ((𝒰.cover.indexSet k).card : NNReal) := by rw [hinv]; ring
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
          * ((𝒰.cover.indexSet k).card : NNReal) := by
      calc Tube.essDistinctTubesInSelfDilate.C 3 (32 * (ρk : ℝ) / (ρ2 : ℝ))
            * ((𝒰par.cover.indexSet k).card : NNReal)
          ≤ (A * cfg.δ ^ (-((12 : ℝ) * cfg.η)))
              * (Cpar ^ 3 * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
                ((𝒰.cover.indexSet k).card : NNReal)) := by
            exact mul_le_mul' hPle hIdx
        _ ≤ (A * cfg.δ ^ (-((12 : ℝ) * cfg.η)))
              * (cfg.δ ^ (-((3 : ℝ) * cfg.η)) * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
                ((𝒰.cover.indexSet k).card : NNReal)) := by
            gcongr
        _ = A * (cfg.δ ^ (-((12 : ℝ) * cfg.η)) * (cfg.δ ^ (-((3 : ℝ) * cfg.η))
              * cfg.δ ^ (-((2 : ℝ) * cfg.η))))
              * ((𝒰.cover.indexSet k).card : NNReal) := by ring
        _ = A * cfg.δ ^ (-((17 : ℝ) * cfg.η))
              * ((𝒰.cover.indexSet k).card : NNReal) := by rw [hadd]
    have hkeyR : (Tube.essDistinctTubesInSelfDilate.C 3 (32 * (ρk : ℝ) / (ρ2 : ℝ)) : ℝ)
        * ((𝒰par.cover.indexSet k).card : ℝ)
        ≤ ((A * cfg.δ ^ (-((17 : ℝ) * cfg.η)) : NNReal) : ℝ)
          * ((𝒰.cover.indexSet k).card : ℝ) := by
      have := NNReal.coe_le_coe.2 hkeyN
      push_cast at this ⊢
      linarith [this]
    linarith [hcard, hstep1, hkeyR]

/-! ### The `∀ᶠ δ` form, hierarchy binder inside -/

/-- **One `δ`-threshold, every hierarchy, at general `b`.** The general-`b` twin of
`Kakeya.VeryNotSticky.eventually_exists_fibreScaleCount_forall_hier`; equivalently, the existing
`Kakeya.VeryNotSticky.eventually_exists_fibreScaleCount_nonslab` with the hierarchy quantified
inside. The single threshold on `δ` is again the absorption of the `δ`-free
`Kakeya.VeryNotSticky.fibreCountConstant C₀bd` into one `η`, and it does not depend on `𝒰`. -/
theorem eventually_exists_fibreScaleCount_nonslab_forall_hier (exscal η : ℝ) (C₀bd : NNReal)
    (hC₀bd : 1 ≤ C₀bd) (hexscal : exscal ≤ 1 / 2) (hη : 0 < η) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal →
      cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) → bd.C₀ = C₀bd →
      ∀ (C : NNReal)
        (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) C),
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
          (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
            ((𝒰.cover.indexSet k).card : ℝ) := by
  filter_upwards [eventually_ennreal_le_rpow_neg
    (K := ((fibreCountConstant C₀bd : NNReal) : ENNReal)) ENNReal.coe_ne_top hη] with δ hδthr
  intro cfg bd hδ hη' hex hb hC₀ C 𝒰 k hk hge hle
  refine exists_fibreScaleCount_of_rhoParentData_nonslab_hier cfg bd 𝒰
    (by rw [hC₀]; exact hC₀bd) (by rw [hex]; exact hexscal) hb ?_ hk hge hle
  rw [hC₀, hδ, hη']
  exact hδthr

/-- **The clause does not distinguish two hierarchies, at general `b`.** Under the shared
hypotheses both sides are theorems, so the `Iff` costs nothing — in particular it does **not**
go through `Kakeya.VeryNotSticky.card_indexSet_le_of_uniform_of_uniform`, whose `C³` the count
never has to pay. -/
theorem exists_fibreScaleCount_nonslab_iff_of_hier (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {C C' : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) C)
    (𝒱 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) C')
    (hC₀bd : 1 ≤ bd.C₀) (hexscal : cfg.exscal ≤ 1 / 2)
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    (hthr : (fibreCountConstant bd.C₀ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η))
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hle : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k
      ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀) :
    (∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
        (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) * ((𝒰.cover.indexSet k).card : ℝ)) ↔
      (∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
        (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) * ((𝒱.cover.indexSet k).card : ℝ)) :=
  ⟨fun _ ↦ exists_fibreScaleCount_of_rhoParentData_nonslab_hier cfg bd 𝒱 hC₀bd hexscal
      hnotslab hthr hk hge hle,
    fun _ ↦ exists_fibreScaleCount_of_rhoParentData_nonslab_hier cfg bd 𝒰 hC₀bd hexscal
      hnotslab hthr hk hge hle⟩

/-! ### Tripwires: the two existing theorems are instances of the binder version

Following `SplitInputsGeneral.lean`'s own convention — no existing declaration is edited, and the
corollary direction is recorded here as compiled `example`s. Between them they pin both moving
parts: the first specialises the hierarchy binder to the `Classical.choice` pick, the second
specialises the non-slab guard back to the degenerate pin. -/

/-- **Tripwire 1**: the existing general-`b` twin
`Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData_nonslab` is this file's theorem at
`𝒰 := cfg.splitHierarchy`. This elaborates only if the two conclusions agree definitionally once
the binder is instantiated, so any drift in the existing statement breaks *this* declaration. -/
example (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (hC₀bd : 1 ≤ bd.C₀)
    (hexscal : cfg.exscal ≤ 1 / 2) (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    (hthr : (fibreCountConstant bd.C₀ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η))
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hle : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k
      ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀) :
    ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
      (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
        ((cfg.splitHierarchy.cover.indexSet k).card : ℝ) :=
  exists_fibreScaleCount_of_rhoParentData_nonslab_hier cfg bd cfg.splitHierarchy hC₀bd hexscal
    hnotslab hthr hk hge hle

/-- **Tripwire 2**: the degenerate binder version
`Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData_hier` is this file's theorem at the
pin `cfg.b = cfg.δ`, converted by `Kakeya.VeryNotSticky.notslab_of_b_eq_delta`. The two D2-free
statements therefore form one chain rather than two parallel developments. -/
example (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) C)
    (hC₀bd : 1 ≤ bd.C₀) (hexscal : cfg.exscal ≤ 1 / 2) (hb : cfg.b = cfg.δ)
    (hthr : (fibreCountConstant bd.C₀ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η))
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hle : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k
      ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀) :
    ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
      (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
        ((𝒰.cover.indexSet k).card : ℝ) :=
  exists_fibreScaleCount_of_rhoParentData_nonslab_hier cfg bd 𝒰 hC₀bd hexscal
    (notslab_of_b_eq_delta cfg hexscal hb) hthr hk hge hle

end Kakeya.VeryNotSticky

end
