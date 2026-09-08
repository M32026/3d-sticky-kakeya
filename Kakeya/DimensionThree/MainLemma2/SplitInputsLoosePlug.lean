/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.LooseUniformAnchorNet
public import Kakeya.DimensionThree.MainLemma2.SplitInputsLoose

/-!
# The step-8 plug: `PBSplitInputs` from conjunct 6's loose datum

`MainLemma2/SplitInputsLoose.lean` carries the
retyped chain (`Kakeya.VeryNotSticky.PBSplitInputs` and
`Kakeya.VeryNotSticky.nonslabSplitBoundPB`); this file carries the uniformity constant, its absorption estimate, the split-input construction, and the application that step 8 of
`Kakeya.VeryNotSticky.sideDataResidue_of_sideDataObligations` consumes.

The split into two modules is forced by the DAG, exactly as the relocation in
`MainLemma2/PartitionBrackets.lean` is: `Kakeya.LooseUniform.anchorOverlapConst` lives in
`MainLemma2/LooseUniformAnchorNet.lean`, which is **downstream** of
`Kakeya.VeryNotSticky.TangentialInputs`, while `PBSplitInputs` must be **upstream** of it.
`Kakeya.VeryNotSticky.SideDataObligations` is downstream of both, which is why conjunct 6 can be
stated at `edCoverConstant cfg.C₀` even though `TangentialInputs.split` cannot mention it.
-/

@[expose] public section

open Filter Topology MeasureTheory

namespace Kakeya.VeryNotSticky

universe u

/-! ### The uniformity constant of the loose cover

`Kakeya.VeryNotSticky.edCoverConstant` is defined **here** rather than beside
`Kakeya.VeryNotSticky.edCoverDilateConstant` in `MainLemma2/LooseUniform.lean` for a mechanical
reason, measured: `Kakeya.LooseUniform.anchorOverlapConst` lives in
`MainLemma2/LooseUniformAnchorNet.lean`, which imports `Conjunct6EssDistinct` →
`AngularMuHierarchy` → `AngularMuBridge` → `LooseUniform`. Putting the `def` in `LooseUniform.lean`
would be an import cycle. It keeps `edCoverDilateConstant`'s namespace,
`Kakeya.VeryNotSticky`. -/

/-- **The uniformity constant of the loose cover**. GWZ's Definition 2.1
constant is `∼1` (`gwz.txt` l.152-153's `⪅`); the tree renders it explicitly, and the anchor
construction of the D-c producer charges its own absolute overlap bound
`Kakeya.LooseUniform.anchorOverlapConst = 2·21249⁶` on top of the configuration's `cfg.C₀`. Those
are two independent uses of the `⪅`, so they are accounted for by a separate constant; the second contribution is an absolute, `δ`-free, `cfg`-free numeral.

`cfg.C₀` alone is **not producible**: `VeryNotSticky` bounds it only from below by `1`
(`VeryNotSticky.hC₀`), a configuration with `cfg.C₀ = 1` is admissible, and the D-c producer's
one-scale net lands at `max C anchorOverlapConst` . It costs no
exponent, because conjunct 6 is an `∀ᶠ δ` and the extra branch of the `max` is a `δ`-free numeral
— that is E-C4, compiled below in
`Kakeya.VeryNotSticky.coe_edCoverConstant_pow_five_le_rpow_neg_eta`. -/
noncomputable def edCoverConstant (C₀ : NNReal) : NNReal :=
  max C₀ (LooseUniform.anchorOverlapConst : NNReal)

/-- `1 ≤ edCoverConstant C₀` whenever `1 ≤ C₀` — the hypothesis `hC` of
`Kakeya.VeryNotSticky.angularFibre_card_le_of_looseUniform`. -/
theorem one_le_edCoverConstant {C₀ : NNReal} (h : 1 ≤ C₀) : 1 ≤ edCoverConstant C₀ :=
  le_trans h (le_max_left _ _)

/-- `C₀ ≤ edCoverConstant C₀`. -/
theorem le_edCoverConstant (C₀ : NNReal) : C₀ ≤ edCoverConstant C₀ := le_max_left _ _

/-- The absolute branch is below the constant too. -/
theorem anchorOverlapConst_le_edCoverConstant (C₀ : NNReal) :
    (LooseUniform.anchorOverlapConst : NNReal) ≤ edCoverConstant C₀ := le_max_right _ _

/-- **E-C4, first half — the `Cang ≤ δ^{-η}` clause at `edCoverConstant cfg.C₀`, on BOTH
branches of the `max`.** The `cfg.C₀` branch is the existing
`Kakeya.VeryNotSticky.coe_C₀_pow_eight_le_rpow_neg_eta` with three powers to spare; the absolute
branch is a `δ`-free numeral and needs a threshold on `δ`, which conjunct 6's `∀ᶠ` supplies. -/
theorem coe_edCoverConstant_pow_five_le_rpow_neg_eta (cfg : VeryNotSticky.{u})
    (hA : ((LooseUniform.anchorOverlapConst : NNReal) : ENNReal) ^ 5 ≤
      (cfg.δ : ENNReal) ^ (-cfg.η)) :
    ((edCoverConstant cfg.C₀ : ENNReal)) ^ 5 ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
  rcases max_cases cfg.C₀ (LooseUniform.anchorOverlapConst : NNReal) with ⟨he, _⟩ | ⟨he, _⟩
  · have hC : edCoverConstant cfg.C₀ = cfg.C₀ := he
    rw [hC]
    have h1 : (1 : ENNReal) ≤ (cfg.C₀ : ENNReal) := by exact_mod_cast cfg.hC₀
    exact le_trans (pow_le_pow_right₀ h1 (by norm_num : (5 : ℕ) ≤ 8))
      cfg.coe_C₀_pow_eight_le_rpow_neg_eta
  · have hC : edCoverConstant cfg.C₀ = (LooseUniform.anchorOverlapConst : NNReal) := he
    rw [hC]
    exact hA

/-- **E-C4, second half — the `fibreConstant` threshold at `edCoverConstant cfg.C₀`, on BOTH
branches.** The `cfg.C₀` branch is the existing
`Kakeya.VeryNotSticky.fibreConstant_of_threshold`; the absolute branch splits `δ^{-η}` as
`δ^{-η/4} · δ^{-3η/4}` exactly as the existing one does. -/
theorem fibreConstant_of_threshold_edCover (cfg : VeryNotSticky.{u}) {C₀ : NNReal}
    (hthr : ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ENNReal) ^ 2 ≤
      (cfg.δ : ENNReal) ^ (-(3 * cfg.η / 4)))
    (hA : ((LooseUniform.anchorOverlapConst : NNReal) : ENNReal) ^ 2 ≤
      (cfg.δ : ENNReal) ^ (-(cfg.η / 4))) :
    ((edCoverConstant cfg.C₀ : ENNReal) ^ 2) *
        ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ENNReal) ^ 2 ≤
      (cfg.δ : ENNReal) ^ (-cfg.η) := by
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := by exact_mod_cast cfg.hδ.ne'
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  rcases max_cases cfg.C₀ (LooseUniform.anchorOverlapConst : NNReal) with ⟨he, _⟩ | ⟨he, _⟩
  · have hC : edCoverConstant cfg.C₀ = cfg.C₀ := he
    rw [hC]
    exact fibreConstant_of_threshold cfg hthr
  · have hC : edCoverConstant cfg.C₀ = (LooseUniform.anchorOverlapConst : NNReal) := he
    rw [hC]
    calc ((LooseUniform.anchorOverlapConst : NNReal) : ENNReal) ^ 2 *
          ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ENNReal) ^ 2
        ≤ (cfg.δ : ENNReal) ^ (-(cfg.η / 4)) * (cfg.δ : ENNReal) ^ (-(3 * cfg.η / 4)) :=
          mul_le_mul' hA hthr
      _ = (cfg.δ : ENNReal) ^ (-cfg.η) := by
          rw [← ENNReal.rpow_add _ _ hδ0 hδtop]; congr 1; ring

/-- **Conjunct 6's clause is a theorem of the loose datum at `edCoverConstant cfg.C₀`.** The
existing `Kakeya.VeryNotSticky.exists_Cang_angularFibre_le_of_looseUniform` with `cfg.C₀` replaced
by `edCoverConstant cfg.C₀`. Its inner step is the existing
`Kakeya.VeryNotSticky.angularFibre_card_le_of_looseUniform`, which is **already** stated at a
general `{C : NNReal}` with `hC : 1 ≤ C` — so the move off `cfg.C₀` costs the tree nothing but
the `∀ᶠ` threshold `hA`, and *that* is what
`Kakeya.VeryNotSticky.coe_edCoverConstant_pow_five_le_rpow_neg_eta` discharges. -/
theorem exists_Cang_angularFibre_le_of_looseUniform_edCover (cfg : VeryNotSticky.{u})
    (bd : BallData cfg)
    (hA : ((LooseUniform.anchorOverlapConst : NNReal) : ENNReal) ^ 5 ≤
      (cfg.δ : ENNReal) ^ (-cfg.η))
    (𝒱 : LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ)
      edCoverDilateConstant (edCoverConstant cfg.C₀))
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k) :
    ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
      ∀ j ∈ cfg.pbActiveTubeNodes 𝒱.tubeUniform.toPartitionBrackets k,
        ∀ x v : EuclideanSpace ℝ (Fin 3),
          (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
            (Cang : ENNReal) *
              ShadedBody.multiplicity (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
                (fun i ↦ (cfg.T i).toShadedBody) := by
  refine ⟨edCoverConstant cfg.C₀ ^ 5, ?_, ?_⟩
  · calc ((edCoverConstant cfg.C₀ ^ 5 : NNReal) : ENNReal)
        = (edCoverConstant cfg.C₀ : ENNReal) ^ 5 := by push_cast; ring
      _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := cfg.coe_edCoverConstant_pow_five_le_rpow_neg_eta hA
  · intro j hj x v
    have h := cfg.angularFibre_card_le_of_looseUniform bd.hC₀ 𝒱 edCoverDilateConstant_pos
      (one_le_edCoverConstant cfg.hC₀) hk hge hj x v
    calc (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal)
        ≤ (edCoverConstant cfg.C₀ : ENNReal) ^ 5 *
            ShadedBody.multiplicity (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
              (fun i ↦ (cfg.T i).toShadedBody) := h
      _ = ((edCoverConstant cfg.C₀ ^ 5 : NNReal) : ENNReal) *
            ShadedBody.multiplicity (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
              (fun i ↦ (cfg.T i).toShadedBody) := by push_cast; ring

/-- **The `∀ᶠ δ` form of the previous theorem — E-C4 discharged from `𝓝[>] 0`.** The `∀ 𝒱`
shape: this is *not* conjunct 6 (with `∀ 𝒱` the clause is a theorem of the tree), it is the certificate that the only
content of conjunct 6 is *producing the datum*. -/
theorem eventually_conjunct6_of_looseUniform_edCover {exscal ϱ η : ℝ} (hη : 0 < η)
    (C₀bd : NNReal) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = d → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      ∀ 𝒱 : LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ)
          edCoverDilateConstant (edCoverConstant cfg.C₀),
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
          ∀ j ∈ cfg.pbActiveTubeNodes 𝒱.tubeUniform.toPartitionBrackets k,
            ∀ x v : EuclideanSpace ℝ (Fin 3),
              (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                (Cang : ENNReal) *
                  ShadedBody.multiplicity
                    (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
                    (fun i ↦ (cfg.T i).toShadedBody) := by
  filter_upwards [eventually_ennreal_le_rpow_neg
    (K := ((LooseUniform.anchorOverlapConst : NNReal) : ENNReal) ^ 5)
    (ENNReal.pow_ne_top ENNReal.coe_ne_top) hη] with d hA
  intro cfg bd hδ hη' _ _ _ _ 𝒱 k hk hge _
  exact cfg.exists_Cang_angularFibre_le_of_looseUniform_edCover bd
    (by rw [hδ, hη']; exact hA) 𝒱 hk hge

/-! ### The T8 producer twin, with the loose datum as a binder -/

/-- **`PBSplitInputs` in the degenerate regime, from a loose Definition 2.2 datum**, up to the
two clauses the existing producer also leaves open. The twin of
`Kakeya.VeryNotSticky.eventually_exists_splitInputs_degenerate`, binder for binder, with two
changes and no others:

* the hierarchy is an explicit `∀ 𝒱` binder, in place of the
  `Classical.choice` pick `cfg.splitHierarchy`;
* the angular and count clauses are read off `𝒱.tubeUniform.toPartitionBrackets` rather than
  off `cfg.splitHierarchy`.

Everything else is discharged here from `cfg`, `bd` and thresholds on `δ` by the *same three
existing lemmas* — `Kakeya.VeryNotSticky.exists_splitLevel`,
`Kakeya.VeryNotSticky.ktScaleData_of_ckt`, `Kakeya.VeryNotSticky.fibreConstant_of_threshold`
(through `fibreConstant_of_threshold_edCover`) — plus
`Kakeya.VeryNotSticky.pbCard_indexSet_mul_card_tubeFibre_le` for `fibreCount`. The only new
threshold is the one E-C4 forces, on the `δ`-free numeral
`Kakeya.LooseUniform.anchorOverlapConst`.

Note that the level `k` does not depend on `𝒱`: `exists_splitLevel` reads only `ρ₂*` and the
grid, so the binder may be introduced before or after it. It is placed before, because the
angular clause conjunct 6 supplies is quantified over `𝒱` first. -/
theorem eventually_exists_splitInputs_loose (C₀ : NNReal) (hC₀ : 1 ≤ C₀)
    {exscal ϱ η : ℝ} (hη : 0 < η) (hexscal0 : 0 < exscal) (hexscal : exscal ≤ 1 / 2)
    (hϱ1 : ϱ ≤ 1) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
        cfg.δ = d → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → bd.C₀ = C₀ →
        cfg.b = cfg.δ →
        ∀ 𝒱 : LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ)
            edCoverDilateConstant (edCoverConstant cfg.C₀),
        ∃ k ≤ Tube.ssfGridLen cfg.δ,
          cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ∧
          Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ ∧
          ∀ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) →
            (∀ j ∈ cfg.pbActiveTubeNodes 𝒱.tubeUniform.toPartitionBrackets k,
              ∀ x v : EuclideanSpace ℝ (Fin 3),
                (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                  (Cang : ENNReal) *
                    ShadedBody.multiplicity
                      (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
                      (fun i ↦ (cfg.T i).toShadedBody)) →
            ∀ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) →
              (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
                (Ccnt : ℝ) * ((𝒱.tubeUniform.cover.indexSet k).card : ℝ) →
              Nonempty (PBSplitInputs cfg bd) := by
  have hpos : (0 : NNReal) < (2 * NonSlab.bodyAngleConstant C₀)⁻¹ := by
    have h1 : (1 : NNReal) ≤ 2 * NonSlab.bodyAngleConstant C₀ :=
      one_le_mul_of_one_le_of_one_le (by norm_num) (NonSlab.one_le_bodyAngleConstant hC₀)
    exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one h1)
  have hKtop : ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ENNReal) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.coe_ne_top
  filter_upwards [eventually_nnreal_mul_rpow_le_const 1 _ hpos hexscal0,
    eventually_ennreal_le_rpow_neg hKtop (by positivity : (0 : ℝ) < 3 * η / 4),
    eventually_ennreal_le_rpow_neg
      (K := ((LooseUniform.anchorOverlapConst : NNReal) : ENNReal) ^ 2)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by positivity : (0 : ℝ) < η / 4)]
    with d hscale hthr hAthr
  intro cfg bd hδ hη' hexs hϱ' hC₀' hb 𝒱
  subst hδ hη' hexs hϱ' hC₀'
  rw [one_mul] at hscale
  obtain ⟨k, hk, hge, hle⟩ := exists_splitLevel cfg hC₀ hexscal hscale hb
  refine ⟨k, hk, hge, hle, fun Cang hCang hang Ccnt hCcnt hfsc ↦ ?_⟩
  exact ⟨PBSplitInputs.ofLevel cfg bd 𝒱.tubeUniform.toPartitionBrackets hk hge hle
    (ktScaleData_of_ckt cfg hexscal hϱ1)
    (fibreConstant_of_threshold_edCover cfg hthr hAthr)
    Cang hCang hang Ccnt hCcnt hfsc⟩

/-! ### The step-8 plug -/

open scoped Classical in
/-- **The step-8 plug, at a fixed `δ`.** From

* conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations` at its specified uniformity constant — the `∃ 𝒱`
  shape, whose body is
  `Kakeya.VeryNotSticky.exists_Cang_angularFibre_le_of_looseUniform_edCover` verbatim — and
* conjunct 5 retyped in lockstep with E-L3, i.e. at the
  *same* loose hierarchy rather than at `cfg.splitHierarchy`,

a `Kakeya.VeryNotSticky.PBSplitInputs cfg bd`. **The `𝒱` the exact chain took by
`Classical.choice` from `cfg.splitHierarchy` is here taken from the conjunct's own `∃`, and it is why conjunct 5 must move with conjunct 6: a
`PBSplitInputs` carries one hierarchy, so its `fibreScaleCount` and its
`angularFibre_le_fibreMult` must speak about the same one.**

The three remaining hypotheses are thresholds on `δ`: `hscale`/`hthr` are the *existing* T8
producer's own, and `hAthr` is E-C4's;
`Kakeya.VeryNotSticky.eventually_exists_pbSplitInputs_of_conjunct6` supplies all three from
`𝓝[>] 0`. -/
theorem exists_pbSplitInputs_of_conjunct6 (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (hexscal : cfg.exscal ≤ 1 / 2) (hϱ1 : cfg.ϱ ≤ 1) (hb : cfg.b = cfg.δ)
    (hscale : cfg.δ ^ cfg.exscal ≤ (2 * NonSlab.bodyAngleConstant bd.C₀)⁻¹)
    (hthr : ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) ^ 2 ≤
      (cfg.δ : ENNReal) ^ (-(3 * cfg.η / 4)))
    (hAthr : ((LooseUniform.anchorOverlapConst : NNReal) : ENNReal) ^ 2 ≤
      (cfg.δ : ENNReal) ^ (-(cfg.η / 4)))
    (hconj6 : ∃ 𝒱 : LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ)
        edCoverDilateConstant (edCoverConstant cfg.C₀),
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
          ∀ j ∈ cfg.pbActiveTubeNodes 𝒱.tubeUniform.toPartitionBrackets k,
            ∀ x v : EuclideanSpace ℝ (Fin 3),
              (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                (Cang : ENNReal) *
                  ShadedBody.multiplicity
                    (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
                    (fun i ↦ (cfg.T i).toShadedBody))
    (hconj5 : ∀ 𝒰s : LooseUniform.LooseUniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
        (Tube.ssfGridLen cfg.δ) edCoverDilateConstant (edCoverConstant cfg.C₀),
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
          (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
            (Ccnt : ℝ) * ((𝒰s.cover.indexSet k).card : ℝ)) :
    Nonempty (PBSplitInputs cfg bd) := by
  obtain ⟨𝒱, hang⟩ := hconj6
  obtain ⟨k, hk, hge, hle⟩ := exists_splitLevel cfg bd.hC₀ hexscal hscale hb
  obtain ⟨Cang, hCang, hangk⟩ := hang k hk hge hle
  obtain ⟨Ccnt, hCcnt, hfsc⟩ := hconj5 𝒱.tubeUniform k hk hge hle
  exact ⟨PBSplitInputs.ofLevel cfg bd 𝒱.tubeUniform.toPartitionBrackets hk hge hle
    (ktScaleData_of_ckt cfg hexscal hϱ1)
    (fibreConstant_of_threshold_edCover cfg hthr hAthr)
    Cang hCang hangk Ccnt hCcnt hfsc⟩

open scoped Classical in
/-- **The step-8 plug, in the `∀ᶠ δ` shape step 8 consumes.** This is the declaration that
replaces `hbuild`'s source in step 8 of
`Kakeya.VeryNotSticky.sideDataResidue_of_sideDataObligations`: after E-L2/E-L3 the four lines

```
obtain ⟨k, hk, hge, hle, hbuild⟩ := hsplit cfg' bd hδ' hη'' hex' hϱ' hbdC₀ hb'
obtain ⟨Ccnt, hCcnt, hfsc⟩ := hR17δ cfg' bd hδ' hη'' hex' hϱ' hb' hbdC₀ k hk hge hle
obtain ⟨Cang, hCang, hang⟩ := hR18δ cfg' bd hδ' hη'' hex' hϱ' hb' hbdC₀ k hk hge hle
obtain ⟨split⟩ := hbuild Cang hCang hang Ccnt hCcnt hfsc
```

become the single line

```
obtain ⟨split⟩ := hsplit cfg' bd hδ' hη'' hex' hϱ' hbdC₀ hb'
  (hR18δ cfg' bd hδ' hη'' hex' hϱ' hb' hbdC₀) (hR17δ cfg' bd hδ' hη'' hex' hϱ' hb' hbdC₀)
```

with `hsplit` this theorem, `hR18δ` conjunct 6 in E-L2's after-text and `hR17δ` conjunct 5
retyped in lockstep. -/
theorem eventually_exists_pbSplitInputs_of_conjunct6 (C₀ : NNReal) (hC₀ : 1 ≤ C₀)
    {exscal ϱ η : ℝ} (hη : 0 < η) (hexscal0 : 0 < exscal) (hexscal : exscal ≤ 1 / 2)
    (hϱ1 : ϱ ≤ 1) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
        cfg.δ = d → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → bd.C₀ = C₀ →
        cfg.b = cfg.δ →
        (∃ 𝒱 : LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ)
            edCoverDilateConstant (edCoverConstant cfg.C₀),
          ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
            cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
            Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
                cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
            ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
              ∀ j ∈ cfg.pbActiveTubeNodes 𝒱.tubeUniform.toPartitionBrackets k,
                ∀ x v : EuclideanSpace ℝ (Fin 3),
                  (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                    (Cang : ENNReal) *
                      ShadedBody.multiplicity
                        (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
                        (fun i ↦ (cfg.T i).toShadedBody)) →
        (∀ 𝒰s : LooseUniform.LooseUniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
            (Tube.ssfGridLen cfg.δ) edCoverDilateConstant (edCoverConstant cfg.C₀),
          ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
            cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
            Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
                cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
            ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
              (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
                (Ccnt : ℝ) * ((𝒰s.cover.indexSet k).card : ℝ)) →
        Nonempty (PBSplitInputs cfg bd) := by
  have hpos : (0 : NNReal) < (2 * NonSlab.bodyAngleConstant C₀)⁻¹ := by
    have h1 : (1 : NNReal) ≤ 2 * NonSlab.bodyAngleConstant C₀ :=
      one_le_mul_of_one_le_of_one_le (by norm_num) (NonSlab.one_le_bodyAngleConstant hC₀)
    exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one h1)
  have hKtop : ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ENNReal) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.coe_ne_top
  filter_upwards [eventually_nnreal_mul_rpow_le_const 1 _ hpos hexscal0,
    eventually_ennreal_le_rpow_neg hKtop (by positivity : (0 : ℝ) < 3 * η / 4),
    eventually_ennreal_le_rpow_neg
      (K := ((LooseUniform.anchorOverlapConst : NNReal) : ENNReal) ^ 2)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by positivity : (0 : ℝ) < η / 4)]
    with d hscale hthr hAthr
  intro cfg bd hδ hη' hexs hϱ' hC₀' hb hconj6 hconj5
  subst hδ hη' hexs hϱ' hC₀'
  rw [one_mul] at hscale
  exact exists_pbSplitInputs_of_conjunct6 cfg bd hexscal hϱ1 hb hscale hthr hAthr hconj6 hconj5

/-! ### Conjunct 6 reduced to the config producer's one remaining step -/

open scoped Classical in
/-- **Conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations`, in its post-E-L2 text, from a
bare loose datum on `cfg.s`.** Everything inside the `∃ 𝒱` is
`Kakeya.VeryNotSticky.exists_Cang_angularFibre_le_of_looseUniform_edCover`, so the *entire*
content of the conjunct is the hypothesis of this theorem: **produce
`LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) edCoverDilateConstant
(edCoverConstant cfg.C₀)` for the configurations the tree builds.**

That is the boundary this steps leaves. c compiles
`Kakeya.LooseUniform.exists_looseShaded_subfamily_of_config`, which gives the datum on a
**subfamily** `s' ⊆ cfg.s` with a shrunk shading; §7 records that bridging `s'` to `cfg.s` is not
a uniformiser step but the configuration producer's — `exists_config_of_slackCut_at` already
performs the analogous naming for the exact datum. This theorem is the exact statement of what
that twin has to hand over, and nothing more. -/
theorem eventually_conjunct6_of_looseDatum {exscal ϱ η : ℝ} (hη : 0 < η) (C₀bd : NNReal) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = d → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      Nonempty (LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ)
          edCoverDilateConstant (edCoverConstant cfg.C₀)) →
      ∃ 𝒱 : LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ)
          edCoverDilateConstant (edCoverConstant cfg.C₀),
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
          ∀ j ∈ cfg.pbActiveTubeNodes 𝒱.tubeUniform.toPartitionBrackets k,
            ∀ x v : EuclideanSpace ℝ (Fin 3),
              (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                (Cang : ENNReal) *
                  ShadedBody.multiplicity
                    (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
                    (fun i ↦ (cfg.T i).toShadedBody) := by
  filter_upwards [eventually_conjunct6_of_looseUniform_edCover.{u} (exscal := exscal) (ϱ := ϱ)
    hη C₀bd] with d h
  intro cfg bd hδ hη' hex hϱ hb hC₀ ⟨𝒱⟩
  exact ⟨𝒱, h cfg bd hδ hη' hex hϱ hb hC₀ 𝒱⟩

/-- **The `Kakeya.LooseUniform.LooseShadedUniformTubeSet.mono` bridge, at the two constants that
matter here.**  produces the datum at
`max cfg.C₀ (anchorOverlapConst : NNReal)`, and that term **is**
`Kakeya.VeryNotSticky.edCoverConstant cfg.C₀` — recorded as a `rfl` so that the producer's output
type and the conjunct's binder type are the same term and no `mono` step is needed for the
constant. -/
theorem edCoverConstant_eq_max (C₀ : NNReal) :
    edCoverConstant C₀ = max C₀ (LooseUniform.anchorOverlapConst : NNReal) := rfl

/-- …and the dilate factor the producer lands at, `4`, **is**
`Kakeya.VeryNotSticky.edCoverDilateConstant`, so no rescaling is needed there either. -/
theorem edCoverDilateConstant_eq_four : edCoverDilateConstant = (4 : ℝ) := rfl

end Kakeya.VeryNotSticky
