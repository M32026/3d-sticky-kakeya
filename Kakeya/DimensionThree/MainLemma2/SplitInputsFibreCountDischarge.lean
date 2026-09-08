/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SplitInputsFibreCount

/-!
`Kakeya.VeryNotSticky.SplitInputsFibreCount` closes conjunct 5 of
`Kakeya.VeryNotSticky.SideDataObligations` at the one hierarchy
`Kakeya.VeryNotSticky.splitHierarchy`, which is
`SplitInputsProduce.lean`'s `cfg.uniform.some.tubeUniform` — a `Classical.choice` pick of the
type `cfg.uniform`, where GWZ *choose* the `ρ`-family their count is spent on (`gwz.txt`
l.194-196: "there exists ..."). For this comparison, the "admissible hierarchies agree up to `⪅1`" of the source is not free.

This file removes D2 from conjunct 5, by proving that the count never sees the choice:

* `Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData_hier` is the counting theorem
  over an **explicit binder** `𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
  (Tube.ssfGridLen cfg.δ) C` — an arbitrary exact uniform hierarchy of the configuration's own
  family, at an **arbitrary** uniformity constant `C`, not tied to `cfg.C₀`;
* `Kakeya.VeryNotSticky.eventually_exists_fibreScaleCount_forall_hier` is its `∀ᶠ δ` form with
  the hierarchy quantified *inside*, so a single `δ`-threshold serves every hierarchy at once;
* `Kakeya.VeryNotSticky.fibreScaleCount_hierarchy_independent` states the consequence in the
  form the defect asks about: whichever two hierarchies are picked, each one's count clause
  transfers to the other with the same constant bound `δ^{-18η}`;
* `Kakeya.VeryNotSticky.sideDataObligations_conjunct5` is conjunct 5 itself, in the
  `Kakeya.VeryNotSticky.CaseParams` shape used by
  `Kakeya.VeryNotSticky.sideDataObligations_conjunct2` and
  `Kakeya.VeryNotSticky.sideDataObligations_conjunct3_of_margin`, obtained by instantiating the
  binder at `𝒰 := cfg.splitHierarchy`. Its tripwire `example` rebuilds `SideDataObligations`
  with its **fifth** component replaced, so the identification of the conclusion with conjunct 5
  is a kernel `rfl` and not an source versions comparison.

**Finding : the count does not depend on the choice
of hierarchy.** The reason is structural rather than numerical, and is visible in the chain of count comparisons: the only place the target hierarchy enters is
`Kakeya.VeryNotSticky.card_indexSet_parent_le`, whose second hierarchy argument is a bare
`Tube.UniformTubeSet` binder whose constant does not appear in its conclusion. The cancellation
there is against `|sPar|`, using the parent's branching number on both sides
(`Kakeya.VeryNotSticky.card_indexSet_mul_branchingN_le` and
`Kakeya.VeryNotSticky.card_filter_le_of_uniform`, both applied to the **parent**), so the loss
`Cpar³` is the *parent's* Definition 2.1 constant and no factor of the target hierarchy's own
constant is incurred. The measured exponent is therefore the same `M = 18` as at
`cfg.splitHierarchy`, with the same `δ`-threshold.

Nothing here weakens, restates, or adds a hypothesis to any existing declaration;
`SetupSideData.lean` is not edited (conjunct 5 stays in the `Prop`, as a proved conjunct).
-/

@[expose] public section

open Filter Topology MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

open Produce

universe u

/-! ### The count at an arbitrary exact uniform hierarchy of `cfg.s` -/

/-- **The `fibreScaleCount` obligation from the parent datum, at any hierarchy.**

Word for word `Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData`, except that the
`Classical.choice` pick `cfg.splitHierarchy` is replaced by an explicit binder `𝒰` ranging over
**every** exact uniform hierarchy of `cfg.s` at the grid length `Tube.ssfGridLen cfg.δ`, at an
arbitrary constant `C`. The proof is unchanged: the target hierarchy is consumed only by
`Kakeya.VeryNotSticky.card_indexSet_parent_le`, which takes it as a bare binder and whose loss
`Cpar³/δ^{2η}` involves only the *parent's* constant and the retention, so neither the choice
nor the constant `C` costs anything. In particular the exponent stays at the measured `M = 18`
and the threshold `hthr` is the same one.

This settles the choice of hierarchy  for conjunct 5: the clause is not a statement
about one uncontrolled pick, and no `⪅1` comparison between admissible hierarchies is needed. -/
theorem exists_fibreScaleCount_of_rhoParentData_hier (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) C)
    (hC₀bd : 1 ≤ bd.C₀) (hexscal : cfg.exscal ≤ 1 / 2) (hb : cfg.b = cfg.δ)
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
  -- the non-slab hypothesis at `b = δ`
  have hnotslab : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁ := by
    rw [hb]
    unfold r₁
    rw [← NNReal.rpow_add hδ0.ne']
    calc cfg.δ = cfg.δ ^ (1 : ℝ) := (NNReal.rpow_one _).symm
      _ ≤ cfg.δ ^ (cfg.exscal + cfg.exscal) :=
        NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  obtain ⟨hwin, -⟩ := rho2_range cfg hδ0 hδ1 hexscal hnotslab
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
  -- the ratio bound `32 ρ_k/ρ₂ ≤ 64 C_bodyAngle δ^{-η}`
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
  -- the powers of `δ^{-η}`
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
  -- the packing constant against `A δ^{-12η}`
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
  -- assemble in `NNReal`
  have hCpar3 : Cpar ^ 3 ≤ cfg.δ ^ (-((3 : ℝ) * cfg.η)) := by
    refine le_trans (pow_le_pow_left₀ (by positivity) hCpar 3) ?_
    rw [hpow3]
  have hadd : cfg.δ ^ (-((12:ℝ) * cfg.η)) * (cfg.δ ^ (-((3:ℝ) * cfg.η))
      * cfg.δ ^ (-((2:ℝ) * cfg.η))) = cfg.δ ^ (-((17:ℝ) * cfg.η)) := by
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
        _ = A * (cfg.δ ^ (-((12:ℝ) * cfg.η)) * (cfg.δ ^ (-((3:ℝ) * cfg.η))
              * cfg.δ ^ (-((2:ℝ) * cfg.η))))
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

/-! ### The two hierarchies of one family, compared -/

/-- **Any two exact uniform hierarchies of the same family have comparable node counts**, at the
loss `C³` of the *first* one's Definition 2.1 constant, with no threshold on `δ` and no
hypothesis relating the two.

This is `Kakeya.VeryNotSticky.card_indexSet_parent_le` read with the parent taken to be the
family itself (`sPar := s`, retention `c := 1`), and it is the compiled form of the source's
"admissible hierarchies agree up to `⪅1`" (`gwz.txt` l.194-196), whose comparison constant would need separate control. It is *not* what the count
theorem below uses — that one pays nothing at all for the choice — but it is the general fact
behind D2's mildness, and it is stated here because it is the fact a reader will look for. -/
theorem card_indexSet_le_of_uniform_of_uniform {δ : NNReal} {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ E3} {N : ℕ} {C C' : NNReal}
    (𝒰 : Tube.UniformTubeSet s (fun i ↦ (T i).toTube) N C)
    (𝒱 : Tube.UniformTubeSet s (fun i ↦ (T i).toTube) N C')
    (hne : s.Nonempty) {k : ℕ} (hk : k ≤ N) :
    ((𝒰.cover.indexSet k).card : NNReal) ≤ C ^ 3 * ((𝒱.cover.indexSet k).card : NNReal) := by
  have h := card_indexSet_parent_le 𝒰 𝒱 (Finset.Subset.refl s) hne hk (c := 1) (by simp)
  simpa using h

/-! ### The `∀ᶠ δ` form, with the hierarchy quantified inside -/

/-- **One `δ`-threshold, every hierarchy.** The `∀ᶠ δ` form of
`Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData_hier`, with the hierarchy binder
*inside* the eventually: the single threshold on `δ` — the absorption of the `δ`-free
`Kakeya.VeryNotSticky.fibreCountConstant C₀bd` into one `η`, exactly as in
`Kakeya.VeryNotSticky.eventually_exists_fibreScaleCount` — is uniform in the choice of `𝒰` and
in its constant `C`. -/
theorem eventually_exists_fibreScaleCount_forall_hier (exscal η : ℝ) (C₀bd : NNReal)
    (hC₀bd : 1 ≤ C₀bd) (hexscal : exscal ≤ 1 / 2) (hη : 0 < η) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.b = cfg.δ → bd.C₀ = C₀bd →
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
  refine exists_fibreScaleCount_of_rhoParentData_hier cfg bd 𝒰 (by rw [hC₀]; exact hC₀bd)
    (by rw [hex]; exact hexscal) hb ?_ hk hge hle
  rw [hC₀, hδ, hη']
  exact hδthr

/-- **The clause does not distinguish two hierarchies.** Under the shared hypotheses both sides
are theorems (`Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData_hier` at `𝒰` and at
`𝒱`), so the `Iff` holds with no comparison lemma between the two hierarchies and, in
particular, with **no** loss of the kind
`Kakeya.VeryNotSticky.card_indexSet_le_of_uniform_of_uniform` would charge. That is the precise
sense in which the choice of hierarchy  does not touch conjunct 5. -/
theorem exists_fibreScaleCount_iff_of_hier (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {C C' : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) C)
    (𝒱 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) C')
    (hC₀bd : 1 ≤ bd.C₀) (hexscal : cfg.exscal ≤ 1 / 2) (hb : cfg.b = cfg.δ)
    (hthr : (fibreCountConstant bd.C₀ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η))
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hle : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k
      ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀) :
    (∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
        (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) * ((𝒰.cover.indexSet k).card : ℝ)) ↔
      (∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
        (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) * ((𝒱.cover.indexSet k).card : ℝ)) :=
  ⟨fun _ ↦ exists_fibreScaleCount_of_rhoParentData_hier cfg bd 𝒱 hC₀bd hexscal hb hthr hk hge hle,
    fun _ ↦ exists_fibreScaleCount_of_rhoParentData_hier cfg bd 𝒰 hC₀bd hexscal hb hthr hk hge hle⟩

/-! ### Conjunct 5 of `SideDataObligations`, closed -/

/-- **Conjunct 5 of `Kakeya.VeryNotSticky.SideDataObligations`, closed outright.**

Its conclusion is that conjunct verbatim (see the tripwire below), and its two side conditions
are the ones the residue already has: `exscal ≤ 1/2` is
`Kakeya.VeryNotSticky.CaseParams.scale` and `0 < η` is the positivity every conjunct of this
`Prop` is stated under, exactly as for
`Kakeya.VeryNotSticky.sideDataObligations_conjunct2`. No new `Prop` carrying a hypothesis is
introduced: the whole chain is the configuration's own
`cfg.rho_count : Kakeya.VeryNotSticky.RhoParentData` ,
spent through `Kakeya.VeryNotSticky.eventually_exists_fibreScaleCount_forall_hier`.

The `Classical.choice`-selected hierarchy `cfg.splitHierarchy` is only an *instance* here: the
statement proved above holds at every exact uniform hierarchy of `cfg.s`, at every constant, so
conjunct 5 is not a claim about one uncontrolled pick. -/
theorem sideDataObligations_conjunct5 {β ζ exscal ϱ η τ τ' : ℝ} (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    {C₀bd : NNReal} (hC₀bd : 1 ≤ C₀bd) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
          (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
            ((cfg.splitHierarchy.cover.indexSet k).card : ℝ) := by
  filter_upwards [eventually_exists_fibreScaleCount_forall_hier.{u} exscal η C₀bd hC₀bd
    params.scale.le hη] with δ h
  intro cfg bd hδ hη' hex _hϱ hb hC₀ k hk hge hle
  exact h cfg bd hδ hη' hex hb hC₀ cfg.C₀ cfg.splitHierarchy k hk hge hle

/-- The fifth component of `SideDataObligations`, stated explicitly.
Reconstructing the conjunction checks both its order and the precise
hierarchy-count hypothesis. Fibre counts and angular estimates used in
a single `PBSplitInputs` must refer to the same hierarchy.

The loose analogue, `sideDataObligations_conjunct5_of_looseRhoParent`,
uses `LooseRhoParentData` and retains the exponent `18η`. Its
`ρ_k/4` directional bound is additional information: exact containment
alone provides only a bound of order `6ρ_k`. -/
example {β exscal ϱ η τ τ' : ℝ}
    {C₀bd Cbias CF Cdil c₁ Cg : NNReal} {D : ℕ}
    (h : SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D)
    (h5 : ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      ∀ C : NNReal, 1 ≤ C → (C : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) →
      ∀ 𝒰s : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) C,
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
          (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
            ((𝒰s.cover.indexSet k).card : ℝ)) :
    SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h5⟩

/-- **Tripwire, the other direction: conjunct 5's type is exactly this theorem's type.**

The projection `h.2.2.2.2.1` out of `Kakeya.VeryNotSticky.SideDataObligations` is ascribed the
conclusion of `Kakeya.VeryNotSticky.sideDataObligations_conjunct5`, written out. This elaborates
only if the two are definitionally equal, i.e. it is the `rfl` behind the reconstruction above,
made explicit and independent of the conjunct *order* argument: together the two `example`s pin
both the text and the position of conjunct 5. -/
example {β exscal ϱ η τ τ' : ℝ} {C₀bd Cbias CF Cdil c₁ Cg : NNReal} {D : ℕ}
    (h : SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D) :
    (∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      ∀ C : NNReal, 1 ≤ C → (C : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) →
      ∀ 𝒰s : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) C,
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
          (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
            ((𝒰s.cover.indexSet k).card : ℝ)) :=
  h.2.2.2.2

end Kakeya.VeryNotSticky

end
