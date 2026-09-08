/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.Numerics
public import Kakeya.DimensionThree.MainLemma1.Repair
public import Kakeya.DimensionThree.HybridParentPacking
public import Kakeya.DimensionThree.MainLemma1.Rescaling.BallRadius
public import Kakeya.DimensionThree.MainLemma1.Rescaling.MassShare
public import Kakeya.DimensionThree.MainLemma1.OneSidedUniform
public import Kakeya.DimensionThree.MainLemma1.Rescaling.LowerWindow

/-!
# Main Lemma 1, Case (ii): The coarse bound and the middle factor

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

universe u

namespace ml1Boot



/-! ### The coarse bound and the middle factor -/

section KatzTao

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### One-sided uniformity, as Section 6 reads it -/

/-- **`Kakeya.ml1Boot.IsOneSidedUniformTubeSet` is `Kakeya.IsFlatPrismUniformTubeSet`.**

The two predicates are field-for-field identical: both are `Tube.UniformTubeSet` with
`le_card_class` deleted.  They exist separately because
`Kakeya/Factoring/FlatPrisms.lean` may not depend on Section 8, so neither file can define the
other's; this is the transport, and it keeps `cover` unchanged so that the `assign`-mentioning
clauses match on the nose. -/
def IsOneSidedUniformTubeSet.toFlatPrism {δ : NNReal} {ι : Type*} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : IsOneSidedUniformTubeSet s T N C) :
    IsFlatPrismUniformTubeSet s T N C where
  cover := 𝒰.cover
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap := 𝒰.boundedOverlap
  card_class_le := 𝒰.card_class_le

/-- **`Kakeya.ml1Boot.IsOneSidedUniform` is `Kakeya.IsFlatPrismUniform`.**

The shaded counterpart of `Kakeya.ml1Boot.IsOneSidedUniformTubeSet.toFlatPrism`.  This is the
transport that lets the Section 8 factoring bundles carry the restriction-friendly predicate while
Section 6's Proposition 6.6(A) is stated against its own copy. -/
def IsOneSidedUniform.toFlatPrism {δ : NNReal} {ι : Type*} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal} (𝒱 : IsOneSidedUniform s V N C) :
    IsFlatPrismUniform s V N C where
  tubeUniform := 𝒱.tubeUniform.toFlatPrism
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := 𝒱.card_shadeClass_le
  le_branchingN := 𝒱.le_branchingN


/-- **The raw Katz–Tao bound at the `b`-tube scale** (blueprint `lem:ml1bootKatzTaoRaw`).

Suppose `K_KT(β)` holds in `ℝ³` and write `β' = β'(γ)`.  Then there is a fullness threshold
`ηs > 0` — the one supplied by `Kakeya.KatzTaoEstimate.multiplicity_bound` at loss exponent
`ε` and exponent `β'` — such that for all sufficiently small `δ̃ > 0`, every
`b ∈ [δ̃, δ̃ ^ (1 - 5 ε)]` and every nonempty shaded family of `b`-tubes in `B₁` with
`λ ≥ δ̃ ^ ((1 - 5 ε) ηs)`,

`μ(𝕋̃_b, Y) ≤ δ̃ ^ (-ε) Δ_max(𝕋̃_b) ^ (1 - β') |𝕋̃_b| ^ β'`.

This is `Kakeya.KatzTaoEstimate.multiplicity_bound` verbatim at the exponent `β'`, with the
loss `b ^ (-ε)` weakened to `δ̃ ^ (-ε)` using `b ≥ δ̃`; separating it from
`Kakeya.ml1Boot.multiplicity_coarse_le` isolates the single use of the Katz–Tao hypothesis
from the bracket bookkeeping that converts its right-hand side into `multTildeTb`.

The family is **not** asked to be pairwise essentially distinct, and nothing replaces the
hypothesis.  `Kakeya.KatzTaoEstimate.multiplicity_bound` carries no such hypothesis: what
excludes degenerate repetition there is the fullness bound, and the conclusion is invariant
under duplicating each index, since `μ`, `Δ_max` and `|𝕋̃_b|` all scale by the multiplicity of
the duplication while `λ` is unchanged and the right-hand side scales by
`m ^ (1 - β') m ^ β' = m`.  Earlier revisions asked for distinctness here and never used it.
See blueprint `note:ml1bootCoarseEDInert`.

The `b`-window is `[δ̃, δ̃ ^ (1 - 5 ε)]` and not `[δ̃, δ̃ ^ (1 - ε)]` because
`Kakeya.ml1Boot.plankWidth_le`, which produces the honest `b`-tube scale, now speaks on the
`5 ε`-window; see blueprint `note:ml1bootWindowConsumers`(3).

`5 ε < 1` is required, not merely `ε ≤ 1`.  The Katz–Tao input is available only below a
threshold at the *tube* scale `b`, and what pushes `b` below it is `b ≤ δ̃ ^ (1 - 5 ε)`
together with `δ̃ → 0`; at `5 ε = 1` the upper end of the range is `δ̃ ^ 0 = 1`, so `b` need
not be small and no choice of `δ̃` makes the input applicable.  The `δ̃ ^ (-ε)` slack does not
repair this, being a factor on the conclusion rather than on the range of `b`.  This costs
nothing: the consumers read `ε` off `Kakeya.ml1Boot.Params`, where
`96 ε ≤ gap β γ₀ ≤ 1/2` forces `ε ≤ 1/192` (`Kakeya.ml1Boot.params_spec`). -/
theorem multiplicity_coarse_raw (hdim : Module.finrank ℝ E = 3)
    {β γ : ℝ} (hβ0 : 0 ≤ β) (hKKT : KatzTaoEstimate.{u} E β)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : 5 * ε < 1) :
    ∃ ηs > (0 : ℝ),
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ b : NNReal, δt ≤ b → b ≤ δt ^ (1 - 5 * ε) →
      ∀ {κ : Type u} {t : Finset κ} (Tb : κ → ShadedTube b E),
        t.Nonempty →
        (∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall 0 1) →
        (δt : ENNReal) ^ ((1 - 5 * ε) * ηs)
          ≤ ShadedBody.fullness t (fun l => (Tb l).toShadedBody) →
        ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ENNReal) ^ (-ε)
            * maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ)
            * (t.card : ENNReal) ^ betaPrime β γ := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by
    rw [hdim]; norm_num : 0 < Module.finrank ℝ E)
  have hKTB : KatzTaoEstimate.{u} E (betaPrime β γ) := by
    refine KatzTaoEstimate.mono ?_ hKKT
    dsimp [betaPrime]
    exact le_max_left β (γ / 2)
  have hβ'0 : 0 ≤ betaPrime β γ := by
    dsimp [betaPrime]
    exact le_trans hβ0 (le_max_left β (γ / 2))
  obtain ⟨η, hη_pos, hP⟩ :=
    KatzTaoEstimate.multiplicity_bound (E := E) (β := betaPrime β γ) hβ'0 hKTB ε hε0
  refine ⟨η, hη_pos, ?_⟩
  · -- Case `5 ε < 1`: the transfer of `K_KT` from small scales to `b ∈ [δ̃, δ̃^(1-5ε)]`.
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hP
    rcases hP with ⟨δ₁, hδ₁_pos, hP_near⟩
    have hδt_rpow_lt : ∀ᶠ (δt : NNReal) in 𝓝[>] (0 : NNReal),
        (δt : NNReal) ^ (1 - 5 * ε) < δ₁ := by
      have h1m : 0 < 1 - 5 * ε := by linarith
      have hcoet : Tendsto (fun δt : NNReal => (δt : ℝ))
          (𝓝[>] (0 : NNReal)) (𝓝 (0 : ℝ)) := by
        simpa using ((NNReal.continuous_coe.tendsto (0 : NNReal)).mono_left nhdsWithin_le_nhds)
      have htendR : Tendsto (fun δt : NNReal => (δt : ℝ) ^ (1 - 5 * ε))
          (𝓝[>] (0 : NNReal)) (𝓝 (0 : ℝ)) :=
        hcoet.rpow_const_nhds_zero h1m
      have h_ev : ∀ᶠ (δt : NNReal) in 𝓝[>] (0 : NNReal),
          (δt : ℝ) ^ (1 - 5 * ε) < (δ₁ : ℝ) :=
        htendR.eventually (eventually_lt_nhds (by exact_mod_cast hδ₁_pos))
      filter_upwards [h_ev] with δt hδt
      simpa [NNReal.coe_rpow] using hδt
    have hδt_pos_ev : ∀ᶠ (δt : NNReal) in 𝓝[>] (0 : NNReal), (0 : NNReal) < δt :=
      self_mem_nhdsWithin
    filter_upwards [hδt_rpow_lt, hδt_pos_ev] with δt hδt_rpow hδt_pos
    intro b hδt_le_b hb_le
    have hb0 : 0 < b := lt_of_lt_of_le hδt_pos hδt_le_b
    have hb_lt_δ₁ : b < δ₁ := lt_of_le_of_lt hb_le hδt_rpow
    intro κ t Tb ht_nonempty hballs hfull
    rcases ht_nonempty with ⟨l₀, hl₀⟩
    let T_ext : κ → ShadedTube b E := fun i => if i ∈ t then Tb i else Tb l₀
    have hext_eq : ∀ i ∈ t, T_ext i = Tb i := by
      intro i hi
      simp [T_ext, hi]
    have hball_total : ∀ i, (T_ext i).carrier ⊆ Metric.closedBall 0 1 := by
      intro i
      by_cases hi : i ∈ t
      · rw [hext_eq i hi]
        exact hballs i hi
      · rw [show T_ext i = Tb l₀ by simp [T_ext, hi]]
        exact hballs l₀ hl₀
    have hfull_real : (b : ℝ) ^ η ≤ (ShadedBody.fullness t (fun l => (Tb l).toShadedBody) : ℝ) := by
      have hbridge : (δt : ℝ) ^ ((1 - 5 * ε) * η) ≤
          (ShadedBody.fullness t (fun l => (Tb l).toShadedBody) : ℝ) := by
        have htoReal : ENNReal.toReal ((δt : ENNReal) ^ ((1 - 5 * ε) * η)) ≤
            ENNReal.toReal (ShadedBody.fullness t (fun l => (Tb l).toShadedBody) : ENNReal) := by
          have hne' : (ShadedBody.fullness t (fun l => (Tb l).toShadedBody) : ENNReal) ≠ ⊤ :=
            ENNReal.coe_ne_top
          exact ENNReal.toReal_mono hne' hfull
        simpa [ennreal_coe_nnreal_rpow_toReal hδt_pos ((1 - 5 * ε) * η), ENNReal.coe_toReal]
          using htoReal
      have hmono : (b : ℝ) ^ η ≤ (δt : ℝ) ^ ((1 - 5 * ε) * η) := by
        have hb_le_real : (b : ℝ) ≤ (δt : ℝ) ^ (1 - 5 * ε) := by exact_mod_cast hb_le
        have h1 : (b : ℝ) ^ η ≤ ((δt : ℝ) ^ (1 - 5 * ε)) ^ η :=
          Real.rpow_le_rpow (by positivity : 0 ≤ (b : ℝ)) hb_le_real (le_of_lt hη_pos)
        rwa [← Real.rpow_mul (by positivity : 0 ≤ (δt : ℝ)) (1 - 5 * ε) η] at h1
      exact le_trans hmono hbridge
    have hfull_eqENN : (ShadedBody.fullness t (fun i => (T_ext i).toShadedBody) : ENNReal) =
        (ShadedBody.fullness t (fun l => (Tb l).toShadedBody) : ENNReal) := by
      rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness]
      unfold ShadedBody.fullness'
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        simp [hext_eq i hi]
      · apply Finset.sum_congr rfl
        intro i hi
        simp [hext_eq i hi]
    have hfull_eq : ShadedBody.fullness t (fun i => (T_ext i).toShadedBody) =
        ShadedBody.fullness t (fun l => (Tb l).toShadedBody) := by
      exact_mod_cast hfull_eqENN
    have hfull_ext :
        (ShadedBody.fullness t (fun i => (T_ext i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ η := by
      rw [hfull_eq]
      exact hfull_real
    have hb_dist : dist b 0 < δ₁ := by
      simpa [NNReal.dist_eq, abs_of_nonneg (by exact_mod_cast hb0.le : (0 : ℝ) ≤ (b : ℝ))]
        using hb_lt_δ₁
    have hb_ball : b ∈ Metric.ball (0 : NNReal) δ₁ := by
      rw [Metric.mem_ball]
      exact hb_dist
    have hbP := hP_near b hb_ball hb0 (ι := κ)
    have hbP_res : ShadedBody.multiplicity t (fun i => (T_ext i).toShadedBody) ≤
        (b : ENNReal) ^ (-ε) *
          maxDensity t (fun i => (T_ext i).toConvexSpaceBody) ^ (1 - betaPrime β γ) *
          (t.card : ENNReal) ^ betaPrime β γ :=
      hbP t T_ext hball_total hfull_ext
    have hmu_eq : ShadedBody.multiplicity t (fun i => (T_ext i).toShadedBody) =
        ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody) := by
      refine multiplicity_eq_of_eqOn (E := E) t ?_
      intro i hi
      rw [hext_eq i hi]
    have hext_convex : ∀ i ∈ t, (T_ext i).toConvexSpaceBody = (Tb i).toConvexSpaceBody := by
      intro i hi
      rw [hext_eq i hi]
    have hΔ_eq : maxDensity t (fun i => (T_ext i).toConvexSpaceBody) =
        maxDensity t (fun l => (Tb l).toConvexSpaceBody) := by
      apply le_antisymm
      · rw [maxDensity_le_iff]
        intro K
        rw [densityIn_eq_of_eqOn (E := E) t hext_convex K]
        exact le_maxDensity t (fun l => (Tb l).toConvexSpaceBody) K
      · rw [maxDensity_le_iff]
        intro K
        rw [← densityIn_eq_of_eqOn (E := E) t hext_convex K]
        exact le_maxDensity t (fun i => (T_ext i).toConvexSpaceBody) K
    have hloss : (b : ENNReal) ^ (-ε) ≤ (δt : ENNReal) ^ (-ε) := by
      have hδtle : (δt : ENNReal) ≤ (b : ENNReal) := by exact_mod_cast hδt_le_b
      have hεle : (δt : ENNReal) ^ ε ≤ (b : ENNReal) ^ ε :=
        ENNReal.rpow_le_rpow hδtle hε0.le
      rw [show (b : ENNReal) ^ (-ε) = ((b : ENNReal) ^ ε)⁻¹ from by
            rw [← ENNReal.rpow_neg (b : ENNReal) ε],
          show (δt : ENNReal) ^ (-ε) = ((δt : ENNReal) ^ ε)⁻¹ from by
            rw [← ENNReal.rpow_neg (δt : ENNReal) ε]]
      exact ENNReal.inv_le_inv.mpr hεle
    calc
      ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          = ShadedBody.multiplicity t (fun i => (T_ext i).toShadedBody) := hmu_eq.symm
      _ ≤ (b : ENNReal) ^ (-ε) *
            maxDensity t (fun i => (T_ext i).toConvexSpaceBody) ^ (1 - betaPrime β γ) *
            (t.card : ENNReal) ^ betaPrime β γ := hbP_res
      _ ≤ (δt : ENNReal) ^ (-ε) *
            maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ) *
            (t.card : ENNReal) ^ betaPrime β γ := by
            rw [hΔ_eq]
            gcongr

/-- **The Katz-Tao coarse multiplicity bound at an ambient radius `R ≥ 1`**.

`Kakeya.ml1Boot.multiplicity_coarse_raw` with the unit ball replaced by `closedBall 0 R` for an
arbitrary scale-independent `R ≥ 1`, at the cost of one extra hypothesis `(b : ℝ) ≤ 1 / 4` and of
nothing at all in the conclusion.

This is what the `b`-scale plank tubes of the coarse endgame need, and the reason they need it is
that they do **not** lie in the unit ball and cannot be made to: a `Kakeya.Tube` has core length
exactly `1`, so a tube attached to a plank hugging `∂B₁` pokes out, and
`Kakeya.ml1Boot.plankTube_carrier_subset_closedBall` gives only
`closedBall 0 (3/2 + √3 + C b)`, with `3/2 + √3 > 1` and no slack.  Under the plank-width side
condition `C b ≤ 1` that radius is at most `9 / 2`
(`Kakeya.ml1Boot.plankTube_carrier_subset_closedBall_of_le`), which is the `R` to use here.

The proof is `Kakeya.ml1Boot.multiplicity_le_of_ball_of_unitBall` applied to the radius-`1`
statement at the *same* accuracy `ε`, with the loss given away in the conclusion instead: the
reduction's two losses — the factor `2` of the low-shading discard and the cell count `M` of the
ball assignment — are fixed before the scale, so `Kakeya.ml1Boot.eventually_mul_rpow_le_rpow`
absorbs `2 M δ̃ ^ (-ε)` into `δ̃ ^ (-ε₂)` for any `ε₂ > ε`.

**This is a real charge on the coarse budget, and the ledger of
`Kakeya.ml1Boot.multTildeT_of_planksClose` does not record it.**  The reduction cannot be had at
the same loss exponent: absorbing a constant requires widening an exponent, and the only exponent
free to widen is the loss, the range of `b` being pinned by the caller.  So item (6) of that
ledger — the unit-ball containment of the `b`-tubes — is *repairable but not free*: whoever routes
`Kakeya.ml1Boot.multiplicity_coarse_le_of_const` through this statement has to find the gap
`ε₂ - ε` somewhere in the `-72 ε` budget of its `hnum`, and ultimately in
`Kakeya.ml1Boot.Params.Spec`.  The exponent is left as a parameter precisely so that the consumer
may choose how small a charge to pay.

*Why the loss cannot instead be bought by shrinking `ε`.*  In
`Kakeya.ml1Boot.multiplicity_coarse_raw` the accuracy and the admissible range of `b` are tied to
the same `ε`: the loss is `δ̃ ^ (-ε)` and the range is `b ≤ δ̃ ^ (1 - 5 ε)`.  Running it at `ε / 2`
would halve the loss but also shrink the range to `b ≤ δ̃ ^ (1 - 5 ε / 2) ≤ δ̃ ^ (1 - 5 ε)`, which
the caller's hypothesis does not supply.  Widening the conclusion is the exit that costs the
caller nothing, every consumer reading `ε` off `Kakeya.ml1Boot.Params` where it is free to halve.
The
fullness threshold is handed out at `ηs / 2` rather than `ηs` for the same reason: the discard
delivers a subfamily fullness of only half the family's, and halving is absorbed by moving the
exponent. -/
theorem multiplicity_coarse_raw_ball (hdim : Module.finrank ℝ E = 3)
    {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ'1 : betaPrime β γ ≤ 1) (hKKT : KatzTaoEstimate.{u} E β)
    {ε ε₂ : ℝ} (hε0 : 0 < ε) (hε1 : 5 * ε < 1) (hεε₂ : ε < ε₂) (R : ℝ) (hR : 1 ≤ R) :
    ∃ ηs > (0 : ℝ),
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ b : NNReal, 0 < b → δt ≤ b → b ≤ δt ^ (1 - 5 * ε) →
      (b : ℝ) ≤ 1 / 4 →
      ∀ {κ : Type u} (t : Finset κ) (Tb : κ → ShadedTube b E),
        t.Nonempty →
        (∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall 0 R) →
        (δt : ENNReal) ^ ((1 - 5 * ε) * ηs)
          ≤ ShadedBody.fullness t (fun l => (Tb l).toShadedBody) →
        ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ENNReal) ^ (-ε₂)
            * maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ)
            * (t.card : ENNReal) ^ betaPrime β γ := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by
    rw [hdim]; norm_num : 0 < Module.finrank ℝ E)
  obtain ⟨M, hM0, hred⟩ := multiplicity_le_of_ball_of_unitBall (E := E) R hR
  obtain ⟨ηs', hηs'0, hraw⟩ :=
    multiplicity_coarse_raw (E := E) (γ := γ) hdim hβ0 hKKT (ε := ε) hε0 hε1
  have h15 : (0 : ℝ) < 1 - 5 * ε := by linarith
  have hβ'0 : 0 ≤ betaPrime β γ := le_trans hβ0 (le_max_left β (γ / 2))
  refine ⟨ηs' / 2, by positivity, ?_⟩
  filter_upwards [hraw,
    eventually_mul_rpow_le_rpow (K := (2 : ENNReal) * (M : ENNReal))
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top M))
      (p := -ε) (q := -ε₂) (by linarith),
    eventually_mul_rpow_le_rpow (K := (2 : ENNReal)) (by simp)
      (p := (1 - 5 * ε) * ηs') (q := (1 - 5 * ε) * (ηs' / 2)) (by nlinarith)]
    with δt hrawδ habs hslack
  intro b hb0 hδtb hbub hb4 κ t Tb ht hball hfull
  set lam : NNReal := δt ^ ((1 - 5 * ε) * (ηs' / 2)) with hlam
  have hexp : (0 : ℝ) ≤ (1 - 5 * ε) * (ηs' / 2) := by positivity
  have hlamcoe : (lam : ENNReal) = (δt : ENNReal) ^ ((1 - 5 * ε) * (ηs' / 2)) := by
    rw [hlam, ENNReal.coe_rpow_of_nonneg _ hexp]
  have hexp1 : (0 : ℝ) ≤ 1 - betaPrime β γ := by linarith
  set Bound : ENNReal := (δt : ENNReal) ^ (-ε)
      * maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ)
      * (t.card : ENNReal) ^ betaPrime β γ with hBound
  -- The radius-`1` statement, read on a translated subfamily.
  have hunit : ∀ (t' : Finset κ) (v : E), t' ⊆ t → t'.Nonempty →
      (∀ l ∈ t', ((Tb l).translate v).carrier ⊆ Metric.closedBall 0 1) →
      ((lam / 2 : NNReal) : ENNReal)
        ≤ (ShadedBody.fullness t' (fun l => ((Tb l).translate v).toShadedBody) : ENNReal) →
      ShadedBody.multiplicity t' (fun l => ((Tb l).translate v).toShadedBody) ≤ Bound := by
    intro t' v hsub hne hballu hfullu
    have hcast : ((lam / 2 : NNReal) : ENNReal) = (lam : ENNReal) / 2 := by
      rw [ENNReal.coe_div (by norm_num)]
      norm_num
    have hfull' : (δt : ENNReal) ^ ((1 - 5 * ε) * ηs')
        ≤ ShadedBody.fullness t' (fun l => ((Tb l).translate v).toShadedBody) := by
      refine le_trans ?_ hfullu
      rw [hcast, ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      calc (δt : ENNReal) ^ ((1 - 5 * ε) * ηs') * 2
          = 2 * (δt : ENNReal) ^ ((1 - 5 * ε) * ηs') := by ring
        _ ≤ (δt : ENNReal) ^ ((1 - 5 * ε) * (ηs' / 2)) := hslack
        _ = (lam : ENNReal) := hlamcoe.symm
    have hkey := hrawδ b hδtb hbub (t := t') (fun l => (Tb l).translate v) hne hballu hfull'
    have hmd : maxDensity t' (fun l => ((Tb l).translate v).toConvexSpaceBody)
        = maxDensity t' (fun l => (Tb l).toConvexSpaceBody) := by
      have hpt : ∀ l, ((Tb l).translate v).toConvexSpaceBody
          = (((Tb l).toTube).translate v).toConvexSpaceBody := by
        intro l
        rw [StickyKakeya.shadedTube_translate_toTube]
      simp only [hpt]
      exact StickyKakeya.maxDensity_tube_translate t' (fun l => (Tb l).toTube) v
    rw [hmd] at hkey
    have hmdle : maxDensity t' (fun l => (Tb l).toConvexSpaceBody)
        ≤ maxDensity t (fun l => (Tb l).toConvexSpaceBody) :=
      maxDensity_mono (fun l => (Tb l).toConvexSpaceBody) hsub
    have hcard : (t'.card : ENNReal) ≤ (t.card : ENNReal) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    refine hkey.trans ?_
    rw [hBound]
    gcongr
  -- The reduction, then the absorption of its two losses.
  have hfullLam : (lam : ENNReal)
      ≤ (ShadedBody.fullness t (fun l => (Tb l).toShadedBody) : ENNReal) := by
    rw [hlamcoe]; exact hfull
  refine (hred hb0 hb4 t Tb hball hfullLam hunit).trans ?_
  rw [hBound]
  calc 2 * (M : ENNReal) * ((δt : ENNReal) ^ (-ε)
        * maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ)
        * (t.card : ENNReal) ^ betaPrime β γ)
      = (2 * (M : ENNReal) * (δt : ENNReal) ^ (-ε))
        * (maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ)
          * (t.card : ENNReal) ^ betaPrime β γ) := by ring
    _ ≤ (δt : ENNReal) ^ (-ε₂)
        * (maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ)
          * (t.card : ENNReal) ^ betaPrime β γ) := by gcongr
    _ = (δt : ENNReal) ^ (-ε₂)
        * maxDensity t (fun l => (Tb l).toConvexSpaceBody) ^ (1 - betaPrime β γ)
        * (t.card : ENNReal) ^ betaPrime β γ := by ring

/-- **`1 ≤ C_Δ`.**

`Kakeya.ml1Boot.coarsePlank.C` is `C_{dilateTestBody} · 2 · C_{plankInTube} · C_{cardBound}`
and each factor is at least `1`.  Extracted from the body of
`Kakeya.ml1Boot.multiplicity_coarse_le`, which now takes its constant as a parameter and
needs this only to instantiate it. -/
theorem coarsePlank.one_le_C : (1 : NNReal) ≤ coarsePlank.C := by
  have one_le_volC : ∀ n : ℕ, (1 : NNReal) ≤ Metric.volume_comparison.C n := by
    intro n
    have hCval : Metric.volume_comparison.C n = ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) : ℝ) := by
      dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      push_cast
      field_simp
    have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hfac : (1 : ℝ) ≤ (Nat.factorial n : ℝ) :=
      mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
    have : (1 : ℝ) ≤ (Metric.volume_comparison.C n : ℝ) := by
      rw [hCval]
      nlinarith
    exact_mod_cast this
  have hdilate : (1 : NNReal) ≤ dilateTestBody.C := by
    dsimp [dilateTestBody.C]
    exact one_le_mul (by norm_num : (1 : NNReal) ≤ 3 ^ 3) (one_le_volC 3)
  have hplink : (1 : NNReal) ≤ plankInTube.C := by
    dsimp [plankInTube.C]
    have hCw : (1 : NNReal) ≤ plankPigeonhole.C := by
      dsimp [plankPigeonhole.C]
      exact one_le_mul (by norm_num : (1 : NNReal) ≤ 16) (one_le_volC 3)
    exact one_le_mul (one_le_mul (by norm_num : (1 : NNReal) ≤ 256) (one_le_pow₀ hCw))
      (one_le_volC 3)
  dsimp [coarsePlank.C]
  exact one_le_mul (one_le_mul (one_le_mul hdilate (by norm_num : (1 : NNReal) ≤ 2)) hplink)
    cardBound.one_le_C

/-- **(GWZ Lemma 8.1) The Katz–Tao bound for the `b`-tubes** (blueprint
`lem:ml1bootTbKatzTao`).

Suppose `K_KT(β)` holds in `ℝ³`, write `β' = β'(γ)`, `g = γ - β'` and let `ap' = η'_{j-1}(γ)`
satisfy the two conclusions of `Kakeya.ml1Boot.numerics_strong`.  Then there is a fullness
threshold `ηs > 0` — the one supplied by `Kakeya.KatzTaoEstimate.multiplicity_bound` at loss
exponent `ε` and exponent `β'` — such that for all sufficiently small `δ̃ > 0`, every
`b ∈ [δ̃, δ̃ ^ (1 - 5 ε)]` and every nonempty family of `b`-tubes
in `B₁` with a shading satisfying

* (a) `λ ≥ δ̃ ^ ((1 - 5 ε) ηs)`,
* (b) `Δ_max(𝕋̃_b) ≤ C_Δ δ̃ ^ (-30 ε - ap')`,
* (c) `C_F(𝕋̃_b, B₁) ≤ C_Δ δ̃ ^ (-ap')`,

the coarse bound `multTildeTb` holds.  Here `C_Δ` is the caller-supplied `CDelta`, subject
only to `1 ≤ CDelta`.

**Why the constant is a parameter.**  This lemma used to pin (b) and (c) at the literal
`Kakeya.ml1Boot.coarsePlank.C`, that is at
`C_{dilateTestBody} · 2 · C_{plankInTube} · C_{cardBound}` with `C_{cardBound} = 2 ^ 60`.  The
density producer on the count route,
`Kakeya.ml1Boot.maxDensity_coarse_le_rpow_of_cardPow`, delivers instead
`C_{dilateTestBody} · 2 · C_{plankInTube} · Ccard` where `Ccard` is the *caller's* count
constant — on the route through `Kakeya.ml1Boot.exists_parentFamilyDilate_atSixEps_card` that
is `Kakeya.hybridPackingConst` and not `C_{cardBound}`.  There is no exponent room in (b) to
absorb the discrepancy: the exponent the producer delivers and the exponent (b) demands are
literally equal (`-30 ε - ap'` at `e = 5`), so no power of `δ̃` can swallow a constant ratio.
Freeing the constant is therefore the only repair, and it is contained: the conclusion carries
no constant at all, and the constant enters the proof only through the local abbreviations
`cNN`, `ce`, `cI` and through the single hypothesis `1 ≤ C_Δ`, which is now `hCDelta`.
`Kakeya.ml1Boot.multiplicity_coarse_le` below is this statement at
`CDelta := Kakeya.ml1Boot.coarsePlank.C`.

Hypothesis (b) carries the exponent `-30 ε - ap'`, which is exactly what
`Kakeya.ml1Boot.maxDensity_coarse_le_rpow` supplies at the parent scale `ρ = δ̃ ^ (6 ε)` and
exactly the value `h = 30 ε + ap'` that `Kakeya.ml1Boot.exponent_budget` uses; the `b`-window
and the fullness threshold carry `1 - 5 ε` because
`Kakeya.ml1Boot.exists_normalizedMiddleData`(iv) speaks on the `5 ε`-window.  See blueprint
`note:ml1bootWindowConsumers`(3).

`Kakeya.ml1Boot.bracket_mem_Icc` and `Kakeya.ml1Boot.bracket_rpow_le` are what handle the
factor `Q ^ (γ/2 + β' - 1)` whose exponent has indeterminate sign.

The family is **not** asked to be pairwise essentially distinct.  That hypothesis was inert:
it was used only to build the corresponding hypothesis of `Kakeya.ml1Boot.bracket_mem_Icc`,
which never referenced it, and neither did `Kakeya.ml1Boot.multiplicity_coarse_raw`, while
`Kakeya.KatzTaoEstimate.multiplicity_bound` has no such hypothesis at all.  Nothing replaces
it — in particular not bounded overlap, which the `b`-tubes cannot supply: they are not the
nodes of a hierarchy, `Tube.HasBoundedOverlap` counts *undilated* containments in a
test tube whereas a `b`-tube contains the fine tubes of its own block only after a `2`-dilate,
and the uniqueness of the parent map says nothing about a count over containments.  Dropping
the hypothesis is what lets `Kakeya.ml1Boot.exists_plankTube_parentFamily` deliver its parent
family at the plank's own ratio `2`.  See blueprint `note:ml1bootCoarseEDInert`. -/
theorem multiplicity_coarse_le_of_const (hdim : Module.finrank ℝ E = 3)
    {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hKKT : KatzTaoEstimate.{u} E β)
    {ε ap' : ℝ} (hε0 : 0 < ε) (hε1 : 5 * ε < 1) (hap' : 0 < ap')
    (hnum : γ - betaPrime β γ
      ≤ -72 * ε - 2 * ap' + 2 * (γ - betaPrime β γ))
    (hnum' : 10 * ap' ≤ (γ - betaPrime β γ) / 2)
    {CDelta : NNReal} (hCDelta : 1 ≤ CDelta) :
    ∃ ηs > (0 : ℝ),
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ b : NNReal, δt ≤ b → b ≤ δt ^ (1 - 5 * ε) →
      ∀ {κ : Type u} {t : Finset κ} (Tb : κ → ShadedTube b E),
        t.Nonempty →
        (∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall 0 1) →
        (δt : ENNReal) ^ ((1 - 5 * ε) * ηs)
          ≤ ShadedBody.fullness t (fun l => (Tb l).toShadedBody) →
        maxDensity t (fun l => (Tb l).toConvexSpaceBody)
          ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-30 * ε - ap') →
        frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall
          ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-ap') →
        ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ)
            * ((t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  classical
  have hεlt1 : ε < 1 := by linarith
  obtain ⟨ηs, hηs, hraw⟩ :=
    multiplicity_coarse_raw (E := E) (γ := γ) hdim hβ0 hKKT hε0 hε1
  obtain ⟨c₃, hc₃, hbr0⟩ := bracket_mem_Icc (E := E) hdim
  let β' : ℝ := betaPrime β γ
  let g : ℝ := γ - β'
  let h : ℝ := 30 * ε + ap'
  let cNN : NNReal := c₃ * CDelta
  let ce : ENNReal := (c₃ : ENNReal) * (CDelta : ENNReal)
  let cI : ENNReal := (CDelta : ENNReal) * ce
  -- β' facts
  have hg2lt : γ / 2 < 1 := by nlinarith [hγ1]
  have hβ'0 : 0 < β' := by
    dsimp [β']
    exact lt_of_lt_of_le (div_pos hγ0 (by norm_num)) (le_max_right β (γ / 2))
  have hβ'1 : β' < 1 := by
    dsimp [β']
    exact max_lt hβ1 hg2lt
  have he0 : -1 ≤ γ / 2 + β' - 1 := by nlinarith [hγ0, hβ'0]
  have he1 : γ / 2 + β' - 1 ≤ 1 := by nlinarith [hg2lt, hβ'1]
  have hgap0 : 0 < γ - β' := by
    have h10 : 0 < 10 * ap' := by positivity
    have hle : 10 * ap' ≤ (γ - β') / 2 := by simpa [β'] using hnum'
    have hpos : 0 < (γ - β') / 2 := lt_of_lt_of_le h10 hle
    nlinarith
  have hgap1 : γ - β' ≤ 1 := by nlinarith [hγ1, hβ'0]
  have hg : 0 < g := by simpa [g] using hgap0
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have h1m : 0 < 1 - 5 * ε := by linarith
  -- 1 ≤ CDelta
  have hCp : (1 : NNReal) ≤ CDelta := hCDelta
  have hcNN1 : (1 : NNReal) ≤ cNN := by
    dsimp [cNN]
    exact one_le_mul hc₃ hCp
  have hce_ne0 : ce ≠ 0 := by
    dsimp [ce]
    have hc₃₀ : (c₃ : ENNReal) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hc₃))
    have hCΔ₀ : (CDelta : ENNReal) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hCp))
    exact mul_ne_zero hc₃₀ hCΔ₀
  have hce_ne_top : ce ≠ ⊤ := by
    dsimp [ce]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hcI_ne_top : cI ≠ ⊤ := by
    dsimp [cI]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hce_ne_top
  have hcI_ne0 : cI ≠ 0 := by
    dsimp [cI]
    have hCΔ₀ : (CDelta : ENNReal) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hCp))
    exact mul_ne_zero hCΔ₀ hce_ne0
  have hcI_inv_pos : 0 < cI ⁻¹ := by
    rw [ENNReal.inv_pos]
    exact hcI_ne_top
  have hsmall0 : ∀ᶠ (δt : NNReal) in 𝓝[>] (0 : NNReal), (δt : ENNReal) ^ (g / 2) ≤ cI ⁻¹ :=
    ENNReal.eventually_coe_rpow_le_of_pos (div_pos hg (by norm_num)) hcI_inv_pos
  have hsmall : ∀ᶠ (δt : NNReal) in 𝓝[>] (0 : NNReal), cI * (δt : ENNReal) ^ (g / 2) ≤ 1 := by
    filter_upwards [hsmall0] with δt hδ
    calc
      cI * (δt : ENNReal) ^ (g / 2) ≤ cI * cI⁻¹ := mul_le_mul_of_nonneg_left hδ (by positivity)
      _ = 1 := ENNReal.mul_inv_cancel hcI_ne0 hcI_ne_top
  refine ⟨ηs, hηs, ?_⟩
  filter_upwards [hraw, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : NNReal) < (1 : NNReal))), hsmall]
    with δt hrawδ (hδ0 : 0 < δt) (hδ1 : δt < 1) hcIsmall
  intro b hδt_le_b hb_le
  -- basic local facts
  have hδt1 : δt ≤ 1 := hδ1.le
  have hδtE : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδtEt : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδt1E : (δt : ENNReal) ≤ 1 := by exact_mod_cast hδt1
  have hb0 : 0 < b := lt_of_lt_of_le hδ0 hδt_le_b
  have hbE : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb0.ne'
  have hbEt : (b : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hdtpow : (1 : ENNReal) ≤ (δt : ENNReal) ^ (-h) := by
    calc (1 : ENNReal) = (δt : ENNReal) ^ (0 : ℝ) := by simp
      _ ≤ (δt : ENNReal) ^ (-h) := ENNReal.rpow_le_rpow_of_exponent_ge hδt1E (by linarith : -h ≤ 0)
  have hb1 : b ≤ 1 := by
    have hδ1mNN : (δt : NNReal) ^ (1 - 5 * ε) ≤ 1 := by
      calc
        (δt : NNReal) ^ (1 - 5 * ε) ≤ (1 : NNReal) ^ (1 - 5 * ε) :=
          NNReal.rpow_le_rpow hδt1 h1m.le
        _ = 1 := by simp
    exact le_trans hb_le hδ1mNN
  intro κ t Tb ht_nonempty hball hfull hmaxdens hfrost
  -- connect to the tube family (bracket_mem_Icc speaks about `Tube`)
  let Tbm : κ → Tube b E := fun l => (Tb l).toTube
  have hconn : ∀ l, (Tbm l).toConvexSpaceBody = (Tb l).toConvexSpaceBody := by
    intro l
    rfl
  have hdens_eq : maxDensity t (fun l => (Tbm l).toConvexSpaceBody) =
      maxDensity t (fun l => (Tb l).toConvexSpaceBody) := by
    apply congr_arg (fun f : κ → ConvexSpaceBody E => maxDensity t f)
    funext l
    exact hconn l
  have hfrost_eq : frostmanConstIn t (fun l => (Tbm l).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall =
      frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall := by
    apply congr_arg (fun f : κ → ConvexSpaceBody E =>
      frostmanConstIn t f ConvexSpaceBody.closedUnitBall)
    funext l
    exact hconn l
  have hball_m : ∀ l ∈ t, (Tbm l).carrier ⊆ Metric.closedBall 0 1 := by
    intro l hl
    simpa [Tbm] using hball l hl
  let CFb : ENNReal := (CDelta : ENNReal) * (δt : ENNReal) ^ (-h)
  have hCFb : (1 : ENNReal) ≤ CFb := by
    change (1 : ENNReal) ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-h)
    exact one_le_mul (by exact_mod_cast hCp) hdtpow
  have hmaxdens_m : maxDensity t (fun l => (Tbm l).toConvexSpaceBody)
      ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-h) := by
    rw [hdens_eq]
    calc
      maxDensity t (fun l => (Tb l).toConvexSpaceBody)
          ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-30 * ε - ap') := by
            simpa using hmaxdens
      _ = (CDelta : ENNReal) * (δt : ENNReal) ^ (-h) := by
            congr 1
            congr 1
            dsimp [h]
            ring
  have hfrost_m : frostmanConstIn t (fun l => (Tbm l).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall ≤ CFb := by
    rw [hfrost_eq]
    dsimp [CFb]
    calc
      frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
          ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-ap') := by simpa using hfrost
      _ ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-h) := by
            have hpow : (δt : ENNReal) ^ (-ap') ≤ (δt : ENNReal) ^ (-h) :=
              ENNReal.rpow_le_rpow_of_exponent_ge hδt1E (by dsimp [h]; linarith [hε0] : -h ≤ -ap')
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hbr := hbr0 hδ0 hδt_le_b hb1 (CFb := CFb) hCFb (CΔ := CDelta) hCp (h := h) hh
      (κ := κ) (t := t) (Tb := Tbm) ht_nonempty hball_m hfrost_m hmaxdens_m
  -- the bracket Q
  let Q : ENNReal := (b : ENNReal) ^ (2 : ℕ) * (t.card : ENNReal)
  have hcard0 : 0 < t.card := (Finset.card_pos).mpr ht_nonempty
  have hcardE0 : (t.card : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hcard0)
  have hcardEtop : (t.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcI_form : (c₃ : ENNReal) * CFb = ce * (δt : ENNReal) ^ (-h) := by
    dsimp [CFb, ce]
    ac_rfl
  have hbr1 : ((c₃ : ENNReal) * CFb)⁻¹ ≤ (t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ) := hbr.1
  have hbr2 : (t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ)
      ≤ (c₃ : ENNReal) * (CDelta : ENNReal) * (δt : ENNReal) ^ (-h) := hbr.2
  have hidt : (δt : ENNReal) ^ h = ((δt : ENNReal) ^ (-h))⁻¹ := by
    rw [← ENNReal.rpow_neg (x := (δt : ENNReal)) (-h)]
    congr 1
    ring
  have hlb : (ce)⁻¹ * (δt : ENNReal) ^ h ≤ (b : ENNReal) ^ (2 : ℕ) * (t.card : ENNReal) := by
    calc
      (ce)⁻¹ * (δt : ENNReal) ^ h = (ce)⁻¹ * ((δt : ENNReal) ^ (-h))⁻¹ := by rw [hidt]
      _ = (ce * (δt : ENNReal) ^ (-h))⁻¹ := by
            rw [← ENNReal.mul_inv (Or.inl hce_ne0) (Or.inl hce_ne_top)]
      _ ≤ (b : ENNReal) ^ (2 : ℕ) * (t.card : ENNReal) := by
            rw [← hcI_form]
            simpa [mul_comm] using hbr1
  have hub : (b : ENNReal) ^ (2 : ℕ) * (t.card : ENNReal)
      ≤ ce * (δt : ENNReal) ^ (-h) := by
    calc
      (b : ENNReal) ^ (2 : ℕ) * (t.card : ENNReal)
          = (t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ) := by
            rw [mul_comm]
      _ ≤ (c₃ : ENNReal) * (CDelta : ENNReal) * (δt : ENNReal) ^ (-h) := hbr2
      _ = ce * (δt : ENNReal) ^ (-h) := by rfl
  have hcardβ : (t.card : ENNReal) ^ β'
      ≤ ce * (δt : ENNReal) ^ (-h) * (b : ENNReal) ^ (-2 * β') * Q ^ (1 - γ / 2) := by
    have hlbr := card_rpow_le_bracket (b := b) (δt := δt) hb0 hδt1
      (β' := β') (γ := γ) he0 he1
      (P := (t.card : ENNReal)) hcardE0 hcardEtop (C := cNN) hcNN1 (h := h) hh hlb hub
    simpa [cNN, ce, Q, ENNReal.coe_mul] using hlbr
  -- exponent budget
  have hbudget : (δt : ENNReal) ^ (-ε - 2 * (30 * ε + ap')) * (b : ENNReal) ^ (-2 * β')
      ≤ (δt : ENNReal) ^ (γ - β') * (b : ENNReal) ^ (-2 * γ) :=
    exponent_budget (ε := ε) (β' := betaPrime β γ) (γ := γ) (ap' := ap')
      hε0 hεlt1.le hap'.le hgap0 hgap1 hnum hδ0 hδt1 hδt_le_b hb_le
  -- assemble
  let M : ENNReal := maxDensity t (fun l => (Tb l).toConvexSpaceBody)
  have h1 : ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
      ≤ (δt : ENNReal) ^ (-ε) * M ^ (1 - β') * (t.card : ENNReal) ^ β' := by
    simpa [M] using hrawδ b hδt_le_b hb_le (Tb := Tb) ht_nonempty hball hfull
  have hconvpow : M ^ (1 - β') ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-h) := by
    calc
      M ^ (1 - β') ≤ ((CDelta : ENNReal) * (δt : ENNReal) ^ (-h)) ^ (1 - β') :=
        ENNReal.rpow_le_rpow (by simpa [M] using hmaxdens_m) (by linarith)
      _ ≤ ((CDelta : ENNReal) * (δt : ENNReal) ^ (-h)) ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (one_le_mul (by exact_mod_cast hCp) hdtpow)
          (by linarith)
      _ = (CDelta : ENNReal) * (δt : ENNReal) ^ (-h) := by simp
  have hpows : (δt : ENNReal) ^ (-ε) * (δt : ENNReal) ^ (-h) * (δt : ENNReal) ^ (-h)
      = (δt : ENNReal) ^ (-ε - 2 * h) := by
    rw [← ENNReal.rpow_add (x := (δt : ENNReal)) (-ε) (-h) hδtE hδtEt]
    rw [← ENNReal.rpow_add (x := (δt : ENNReal)) (-ε + -h) (-h) hδtE hδtEt]
    congr 1
    ring
  have hμ0 : ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
      ≤ (δt : ENNReal) ^ (-ε) * ((CDelta : ENNReal) * (δt : ENNReal) ^ (-h))
          * (ce * (δt : ENNReal) ^ (-h) * (b : ENNReal) ^ (-2 * β') * Q ^ (1 - γ / 2)) := by
    let B : ENNReal := ce * (δt : ENNReal) ^ (-h) * (b : ENNReal) ^ (-2 * β') * Q ^ (1 - γ / 2)
    have hA : (δt : ENNReal) ^ (-ε) * M ^ (1 - β') * (t.card : ENNReal) ^ β'
        ≤ (δt : ENNReal) ^ (-ε) * M ^ (1 - β') * B := by
      exact mul_le_mul_of_nonneg_left (a := (δt : ENNReal) ^ (-ε) * M ^ (1 - β')) hcardβ bot_le
    have hB : (δt : ENNReal) ^ (-ε) * M ^ (1 - β') * B
        ≤ (δt : ENNReal) ^ (-ε) * ((CDelta : ENNReal) * (δt : ENNReal) ^ (-h)) * B := by
      have hM : (δt : ENNReal) ^ (-ε) * M ^ (1 - β')
          ≤ (δt : ENNReal) ^ (-ε) * ((CDelta : ENNReal) * (δt : ENNReal) ^ (-h)) :=
        mul_le_mul_of_nonneg_left (a := (δt : ENNReal) ^ (-ε)) hconvpow bot_le
      exact mul_le_mul_of_nonneg_right (a := B) hM bot_le
    calc
      ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ENNReal) ^ (-ε) * M ^ (1 - β') * (t.card : ENNReal) ^ β' := h1
      _ ≤ (δt : ENNReal) ^ (-ε) * M ^ (1 - β') * B := hA
      _ ≤ (δt : ENNReal) ^ (-ε) * ((CDelta : ENNReal) * (δt : ENNReal) ^ (-h)) * B := hB
  have hμ1 : ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
      ≤ cI * (δt : ENNReal) ^ (-ε - 2 * h) * (b : ENNReal) ^ (-2 * β') * Q ^ (1 - γ / 2) := by
    calc
      ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ENNReal) ^ (-ε) * ((CDelta : ENNReal) * (δt : ENNReal) ^ (-h))
              * (ce * (δt : ENNReal) ^ (-h) * (b : ENNReal) ^ (-2 * β') * Q ^ (1 - γ / 2)) := hμ0
      _ = cI * (δt : ENNReal) ^ (-ε - 2 * h) * (b : ENNReal) ^ (-2 * β') * Q ^ (1 - γ / 2) := by
            dsimp [cI]
            rw [← hpows]
            ac_rfl
  have hμ2 : ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
      ≤ cI * (δt : ENNReal) ^ (γ - β') * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
    have hbdex : (δt : ENNReal) ^ (-ε - 2 * h) * (b : ENNReal) ^ (-2 * β')
        ≤ (δt : ENNReal) ^ (γ - β') * (b : ENNReal) ^ (-2 * γ) := by
      simpa [h] using hbudget
    calc
      ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ cI * (δt : ENNReal) ^ (-ε - 2 * h) * (b : ENNReal) ^ (-2 * β') * Q ^ (1 - γ / 2) := hμ1
      _ = cI * Q ^ (1 - γ / 2) * ((δt : ENNReal) ^ (-ε - 2 * h) * (b : ENNReal) ^ (-2 * β')) := by
            ac_rfl
      _ ≤ cI * Q ^ (1 - γ / 2) * ((δt : ENNReal) ^ (γ - β') * (b : ENNReal) ^ (-2 * γ)) := by
            exact mul_le_mul_of_nonneg_left (a := cI * Q ^ (1 - γ / 2)) hbdex bot_le
      _ = cI * (δt : ENNReal) ^ (γ - β') * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
            ac_rfl
  have hg_half : (δt : ENNReal) ^ g = (δt : ENNReal) ^ (g / 2) * (δt : ENNReal) ^ (g / 2) := by
    rw [← ENNReal.rpow_add (x := (δt : ENNReal)) (g / 2) (g / 2) hδtE hδtEt]
    congr 1
    ring
  have htail0 : cI * (δt : ENNReal) ^ g * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2)
      = (cI * (δt : ENNReal) ^ (g / 2)) * (δt : ENNReal) ^ (g / 2)
          * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
    rw [hg_half]
    ac_rfl
  have hnum'g : 10 * ap' ≤ g / 2 := by simpa [g] using hnum'
  have htail : (cI * (δt : ENNReal) ^ (g / 2)) * (δt : ENNReal) ^ (g / 2)
        * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2)
      ≤ (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
    have hpowg : (δt : ENNReal) ^ (g / 2) ≤ (δt : ENNReal) ^ (10 * ap') :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδt1E hnum'g
    calc
      (cI * (δt : ENNReal) ^ (g / 2)) * (δt : ENNReal) ^ (g / 2)
            * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2)
          ≤ 1 * (δt : ENNReal) ^ (g / 2) * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
            gcongr
      _ = (δt : ENNReal) ^ (g / 2) * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by simp
      _ ≤ (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
            exact mul_le_mul_of_nonneg_right (a := Q ^ (1 - γ / 2))
              (mul_le_mul_of_nonneg_right (a := (b : ENNReal) ^ (-2 * γ)) hpowg bot_le) bot_le
  -- final
  calc
    ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
        ≤ cI * (δt : ENNReal) ^ g * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
          simpa [g] using hμ2
    _ = (cI * (δt : ENNReal) ^ (g / 2)) * (δt : ENNReal) ^ (g / 2)
          * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := htail0
    _ ≤ (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := htail
    _ = (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ)
          * ((t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          rw [show Q ^ (1 - γ / 2) =
              ((t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) from by
            dsimp [Q]
            apply congrArg (fun x : ENNReal => x ^ (1 - γ / 2))
            exact mul_comm ((b : ENNReal) ^ (2 : ℕ)) (t.card : ENNReal)]

/-- **(GWZ Lemma 8.1) The Katz–Tao bound for the `b`-tubes, at an ambient radius `R ≥ 1`.**

`Kakeya.ml1Boot.multiplicity_coarse_le_of_const` with `Metric.closedBall 0 1` replaced by
`Metric.closedBall 0 R` in the containment hypothesis and by
`ConvexSpaceBody.closedBall 0 R` in the ambient body of hypothesis (c).  The conclusion is
 to the unit-ball form: no exponent moves.

Two hypotheses are added and one is widened:

* `(b : ℝ) ≤ 1 / 4`, the plank-width side condition of
  `Kakeya.ml1Boot.multiplicity_coarse_raw_ball` — bought from the eventually filter on the
  Section 8 route by `Kakeya.ml1Boot.eventually_mul_two_rpow_le`, and identical to the `hbq1`
  the `b`-tube producers already ask for;
* the loss exponent `ε₂` with `ε < ε₂ ≤ 2 ε`, which is what
  `Kakeya.ml1Boot.multiplicity_coarse_raw_ball` charges for the ball reduction.

**The `ε₂` charge is already funded and costs `Kakeya.ml1Boot.Params.Spec` nothing.**  The
budget hypothesis `hnum` is unchanged at `-72 ε`, and
`Kakeya.ml1Boot.exponent_budget_loss` shows `71 ε` is all that is needed; `ε₂ = 3 ε / 2` is
therefore admissible with `ε / 2` still to spare.  This contradicts the warning carried by
`Kakeya.ml1Boot.multiplicity_coarse_raw_ball`'s own docstring, that the caller "has to find the
gap `ε₂ - ε` … ultimately in `Kakeya.ml1Boot.Params.Spec`": the gap is inside `hnum` already.

The ambient radius enters the proof in exactly two places, and both are volume bookkeeping:
`Kakeya.ml1Boot.multiplicity_coarse_raw_ball` (already on the tree, previously with no
consumer) and `Kakeya.ml1Boot.bracket_mem_Icc_ball`, whose only change is the constant
`c₃ = max 3 r ↦ max (3 R³) r`.  That constant is absorbed by the `∀ᶠ` filter through
`cI * δ̃ ^ (g/2) ≤ 1`, so it is free. -/
theorem multiplicity_coarse_le_of_const_ball (hdim : Module.finrank ℝ E = 3)
    {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hKKT : KatzTaoEstimate.{u} E β)
    {ε ε₂ ap' : ℝ} (hε0 : 0 < ε) (hε1 : 5 * ε < 1) (hap' : 0 < ap')
    (hεε₂ : ε < ε₂) (hε₂2 : ε₂ ≤ 2 * ε)
    (hnum : γ - betaPrime β γ
      ≤ -72 * ε - 2 * ap' + 2 * (γ - betaPrime β γ))
    (hnum' : 10 * ap' ≤ (γ - betaPrime β γ) / 2)
    {CDelta : NNReal} (hCDelta : 1 ≤ CDelta) (R : NNReal) (hR : 1 ≤ R) :
    ∃ ηs > (0 : ℝ),
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ b : NNReal, δt ≤ b → b ≤ δt ^ (1 - 5 * ε) →
      (b : ℝ) ≤ 1 / 4 →
      ∀ {κ : Type u} (t : Finset κ) (Tb : κ → ShadedTube b E),
        t.Nonempty →
        (∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall 0 (R : ℝ)) →
        (δt : ENNReal) ^ ((1 - 5 * ε) * ηs)
          ≤ ShadedBody.fullness t (fun l => (Tb l).toShadedBody) →
        maxDensity t (fun l => (Tb l).toConvexSpaceBody)
          ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-30 * ε - ap') →
        frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody)
            (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg)
          ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-ap') →
        ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ)
            * ((t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  classical
  have hεlt1 : ε < 1 := by linarith
  have hg2lt : γ / 2 < 1 := by nlinarith [hγ1]
  have hβ'1 : betaPrime β γ ≤ 1 := by
    dsimp [betaPrime]
    exact max_le hβ1.le hg2lt.le
  obtain ⟨ηs, hηs, hraw⟩ :=
    multiplicity_coarse_raw_ball (E := E) (γ := γ) hdim hβ0 hβ'1 hKKT hε0 hε1 hεε₂
      (R : ℝ) (by exact_mod_cast hR)
  obtain ⟨c₃, hc₃, hbr0⟩ := bracket_mem_Icc_ball (E := E) hdim R hR
  let β' : ℝ := betaPrime β γ
  let g : ℝ := γ - β'
  let h : ℝ := 30 * ε + ap'
  let cNN : NNReal := c₃ * CDelta
  let ce : ENNReal := (c₃ : ENNReal) * (CDelta : ENNReal)
  let cI : ENNReal := (CDelta : ENNReal) * ce
  have hβ'0 : 0 < β' := by
    dsimp [β', betaPrime]
    exact lt_of_lt_of_le (div_pos hγ0 (by norm_num)) (le_max_right β (γ / 2))
  have he0 : -1 ≤ γ / 2 + β' - 1 := by nlinarith [hγ0, hβ'0]
  have he1 : γ / 2 + β' - 1 ≤ 1 := by nlinarith [hg2lt, hβ'1]
  have hgap0 : 0 < γ - β' := by
    have h10 : 0 < 10 * ap' := by positivity
    have hle : 10 * ap' ≤ (γ - β') / 2 := by simpa [β'] using hnum'
    have hpos : 0 < (γ - β') / 2 := lt_of_lt_of_le h10 hle
    nlinarith
  have hgap1 : γ - β' ≤ 1 := by nlinarith [hγ1, hβ'0]
  have hg : 0 < g := by simpa [g] using hgap0
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have h1m : 0 < 1 - 5 * ε := by linarith
  have hCp : (1 : NNReal) ≤ CDelta := hCDelta
  have hcNN1 : (1 : NNReal) ≤ cNN := one_le_mul hc₃ hCp
  have hce_ne0 : ce ≠ 0 := by
    dsimp [ce]
    exact mul_ne_zero (ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hc₃)))
      (ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hCp)))
  have hce_ne_top : ce ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hcI_ne_top : cI ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hce_ne_top
  have hcI_ne0 : cI ≠ 0 := by
    dsimp [cI]
    exact mul_ne_zero (ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hCp)))
      hce_ne0
  have hcI_inv_pos : 0 < cI ⁻¹ := by rw [ENNReal.inv_pos]; exact hcI_ne_top
  have hsmall0 : ∀ᶠ (δt : NNReal) in 𝓝[>] (0 : NNReal), (δt : ENNReal) ^ (g / 2) ≤ cI ⁻¹ :=
    ENNReal.eventually_coe_rpow_le_of_pos (div_pos hg (by norm_num)) hcI_inv_pos
  have hsmall : ∀ᶠ (δt : NNReal) in 𝓝[>] (0 : NNReal), cI * (δt : ENNReal) ^ (g / 2) ≤ 1 := by
    filter_upwards [hsmall0] with δt hδ
    calc
      cI * (δt : ENNReal) ^ (g / 2) ≤ cI * cI⁻¹ := mul_le_mul_of_nonneg_left hδ (by positivity)
      _ = 1 := ENNReal.mul_inv_cancel hcI_ne0 hcI_ne_top
  refine ⟨ηs, hηs, ?_⟩
  filter_upwards [hraw, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : NNReal) < (1 : NNReal))), hsmall]
    with δt hrawδ (hδ0 : 0 < δt) (hδ1 : δt < 1) hcIsmall
  intro b hδt_le_b hb_le hb4
  have hδt1 : δt ≤ 1 := hδ1.le
  have hδtE : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδtEt : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδt1E : (δt : ENNReal) ≤ 1 := by exact_mod_cast hδt1
  have hb0 : 0 < b := lt_of_lt_of_le hδ0 hδt_le_b
  have hdtpow : (1 : ENNReal) ≤ (δt : ENNReal) ^ (-h) := by
    calc (1 : ENNReal) = (δt : ENNReal) ^ (0 : ℝ) := by simp
      _ ≤ (δt : ENNReal) ^ (-h) := ENNReal.rpow_le_rpow_of_exponent_ge hδt1E (by linarith : -h ≤ 0)
  have hb1 : b ≤ 1 := by
    have hδ1mNN : (δt : NNReal) ^ (1 - 5 * ε) ≤ 1 := by
      calc
        (δt : NNReal) ^ (1 - 5 * ε) ≤ (1 : NNReal) ^ (1 - 5 * ε) :=
          NNReal.rpow_le_rpow hδt1 h1m.le
        _ = 1 := by simp
    exact le_trans hb_le hδ1mNN
  intro κ t Tb ht_nonempty hball hfull hmaxdens hfrost
  let Tbm : κ → Tube b E := fun l => (Tb l).toTube
  have hconn : ∀ l, (Tbm l).toConvexSpaceBody = (Tb l).toConvexSpaceBody := fun l => rfl
  have hdens_eq : maxDensity t (fun l => (Tbm l).toConvexSpaceBody) =
      maxDensity t (fun l => (Tb l).toConvexSpaceBody) := by
    apply congr_arg (fun f : κ → ConvexSpaceBody E => maxDensity t f)
    funext l
    exact hconn l
  have hfrost_eq : frostmanConstIn t (fun l => (Tbm l).toConvexSpaceBody)
        (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg) =
      frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody)
        (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg) := by
    apply congr_arg (fun f : κ → ConvexSpaceBody E =>
      frostmanConstIn t f (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg))
    funext l
    exact hconn l
  have hball_m : ∀ l ∈ t, (Tbm l).carrier ⊆ Metric.closedBall 0 (R : ℝ) := by
    intro l hl
    simpa [Tbm] using hball l hl
  let CFb : ENNReal := (CDelta : ENNReal) * (δt : ENNReal) ^ (-h)
  have hCFb : (1 : ENNReal) ≤ CFb :=
    one_le_mul (by exact_mod_cast hCp) hdtpow
  have hmaxdens_m : maxDensity t (fun l => (Tbm l).toConvexSpaceBody)
      ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-h) := by
    rw [hdens_eq]
    calc
      maxDensity t (fun l => (Tb l).toConvexSpaceBody)
          ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-30 * ε - ap') := by simpa using hmaxdens
      _ = (CDelta : ENNReal) * (δt : ENNReal) ^ (-h) := by
            congr 2
            dsimp [h]
            ring
  have hfrost_m : frostmanConstIn t (fun l => (Tbm l).toConvexSpaceBody)
        (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg) ≤ CFb := by
    rw [hfrost_eq]
    dsimp [CFb]
    calc
      frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody)
            (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg)
          ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-ap') := by simpa using hfrost
      _ ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-h) := by
            have hpow : (δt : ENNReal) ^ (-ap') ≤ (δt : ENNReal) ^ (-h) :=
              ENNReal.rpow_le_rpow_of_exponent_ge hδt1E (by dsimp [h]; linarith [hε0] : -h ≤ -ap')
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hbr := hbr0 hδ0 hδt_le_b hb1 (CFb := CFb) hCFb (CΔ := CDelta) hCp (h := h) hh
      (κ := κ) (t := t) (Tb := Tbm) ht_nonempty hball_m hfrost_m hmaxdens_m
  let Q : ENNReal := (b : ENNReal) ^ (2 : ℕ) * (t.card : ENNReal)
  have hcard0 : 0 < t.card := (Finset.card_pos).mpr ht_nonempty
  have hcardE0 : (t.card : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hcard0)
  have hcardEtop : (t.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcI_form : (c₃ : ENNReal) * CFb = ce * (δt : ENNReal) ^ (-h) := by
    dsimp [CFb, ce]
    ac_rfl
  have hbr1 : ((c₃ : ENNReal) * CFb)⁻¹ ≤ (t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ) := hbr.1
  have hbr2 : (t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ)
      ≤ (c₃ : ENNReal) * (CDelta : ENNReal) * (δt : ENNReal) ^ (-h) := hbr.2
  have hidt : (δt : ENNReal) ^ h = ((δt : ENNReal) ^ (-h))⁻¹ := by
    rw [← ENNReal.rpow_neg (x := (δt : ENNReal)) (-h)]
    congr 1
    ring
  have hlb : (ce)⁻¹ * (δt : ENNReal) ^ h ≤ (b : ENNReal) ^ (2 : ℕ) * (t.card : ENNReal) := by
    calc
      (ce)⁻¹ * (δt : ENNReal) ^ h = (ce)⁻¹ * ((δt : ENNReal) ^ (-h))⁻¹ := by rw [hidt]
      _ = (ce * (δt : ENNReal) ^ (-h))⁻¹ := by
            rw [← ENNReal.mul_inv (Or.inl hce_ne0) (Or.inl hce_ne_top)]
      _ ≤ (b : ENNReal) ^ (2 : ℕ) * (t.card : ENNReal) := by
            rw [← hcI_form]
            simpa [mul_comm] using hbr1
  have hub : (b : ENNReal) ^ (2 : ℕ) * (t.card : ENNReal)
      ≤ ce * (δt : ENNReal) ^ (-h) := by
    calc
      (b : ENNReal) ^ (2 : ℕ) * (t.card : ENNReal)
          = (t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ) := by rw [mul_comm]
      _ ≤ (c₃ : ENNReal) * (CDelta : ENNReal) * (δt : ENNReal) ^ (-h) := hbr2
      _ = ce * (δt : ENNReal) ^ (-h) := by rfl
  have hcardβ : (t.card : ENNReal) ^ β'
      ≤ ce * (δt : ENNReal) ^ (-h) * (b : ENNReal) ^ (-2 * β') * Q ^ (1 - γ / 2) := by
    have hlbr := card_rpow_le_bracket (b := b) (δt := δt) hb0 hδt1
      (β' := β') (γ := γ) he0 he1
      (P := (t.card : ENNReal)) hcardE0 hcardEtop (C := cNN) hcNN1 (h := h) hh hlb hub
    simpa [cNN, ce, Q, ENNReal.coe_mul] using hlbr
  have hbudget : (δt : ENNReal) ^ (-ε₂ - 2 * (30 * ε + ap')) * (b : ENNReal) ^ (-2 * β')
      ≤ (δt : ENNReal) ^ (γ - β') * (b : ENNReal) ^ (-2 * γ) :=
    exponent_budget_loss (ε := ε) (ε₂ := ε₂) (β' := betaPrime β γ) (γ := γ) (ap' := ap')
      hε0 hεlt1.le hap'.le hε₂2 hgap0 hgap1 hnum hδ0 hδt1 hδt_le_b hb_le
  let M : ENNReal := maxDensity t (fun l => (Tb l).toConvexSpaceBody)
  have h1 : ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
      ≤ (δt : ENNReal) ^ (-ε₂) * M ^ (1 - β') * (t.card : ENNReal) ^ β' := by
    simpa [M, β'] using hrawδ b hb0 hδt_le_b hb_le hb4 t Tb ht_nonempty hball hfull
  have hconvpow : M ^ (1 - β') ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-h) := by
    calc
      M ^ (1 - β') ≤ ((CDelta : ENNReal) * (δt : ENNReal) ^ (-h)) ^ (1 - β') :=
        ENNReal.rpow_le_rpow (by simpa [M] using (hdens_eq ▸ hmaxdens_m)) (by linarith)
      _ ≤ ((CDelta : ENNReal) * (δt : ENNReal) ^ (-h)) ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (one_le_mul (by exact_mod_cast hCp) hdtpow)
          (by linarith)
      _ = (CDelta : ENNReal) * (δt : ENNReal) ^ (-h) := by simp
  have hpows : (δt : ENNReal) ^ (-ε₂) * (δt : ENNReal) ^ (-h) * (δt : ENNReal) ^ (-h)
      = (δt : ENNReal) ^ (-ε₂ - 2 * h) := by
    rw [← ENNReal.rpow_add (x := (δt : ENNReal)) (-ε₂) (-h) hδtE hδtEt]
    rw [← ENNReal.rpow_add (x := (δt : ENNReal)) (-ε₂ + -h) (-h) hδtE hδtEt]
    congr 1
    ring
  have hμ0 : ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
      ≤ (δt : ENNReal) ^ (-ε₂) * ((CDelta : ENNReal) * (δt : ENNReal) ^ (-h))
          * (ce * (δt : ENNReal) ^ (-h) * (b : ENNReal) ^ (-2 * β') * Q ^ (1 - γ / 2)) := by
    let B : ENNReal := ce * (δt : ENNReal) ^ (-h) * (b : ENNReal) ^ (-2 * β') * Q ^ (1 - γ / 2)
    have hA : (δt : ENNReal) ^ (-ε₂) * M ^ (1 - β') * (t.card : ENNReal) ^ β'
        ≤ (δt : ENNReal) ^ (-ε₂) * M ^ (1 - β') * B :=
      mul_le_mul_of_nonneg_left (a := (δt : ENNReal) ^ (-ε₂) * M ^ (1 - β')) hcardβ bot_le
    have hB : (δt : ENNReal) ^ (-ε₂) * M ^ (1 - β') * B
        ≤ (δt : ENNReal) ^ (-ε₂) * ((CDelta : ENNReal) * (δt : ENNReal) ^ (-h)) * B := by
      have hM : (δt : ENNReal) ^ (-ε₂) * M ^ (1 - β')
          ≤ (δt : ENNReal) ^ (-ε₂) * ((CDelta : ENNReal) * (δt : ENNReal) ^ (-h)) :=
        mul_le_mul_of_nonneg_left (a := (δt : ENNReal) ^ (-ε₂)) hconvpow bot_le
      exact mul_le_mul_of_nonneg_right (a := B) hM bot_le
    calc
      ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ENNReal) ^ (-ε₂) * M ^ (1 - β') * (t.card : ENNReal) ^ β' := h1
      _ ≤ (δt : ENNReal) ^ (-ε₂) * M ^ (1 - β') * B := hA
      _ ≤ (δt : ENNReal) ^ (-ε₂) * ((CDelta : ENNReal) * (δt : ENNReal) ^ (-h)) * B := hB
  have hμ1 : ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
      ≤ cI * (δt : ENNReal) ^ (-ε₂ - 2 * h) * (b : ENNReal) ^ (-2 * β') * Q ^ (1 - γ / 2) := by
    calc
      ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ENNReal) ^ (-ε₂) * ((CDelta : ENNReal) * (δt : ENNReal) ^ (-h))
              * (ce * (δt : ENNReal) ^ (-h) * (b : ENNReal) ^ (-2 * β') * Q ^ (1 - γ / 2)) := hμ0
      _ = cI * (δt : ENNReal) ^ (-ε₂ - 2 * h) * (b : ENNReal) ^ (-2 * β') * Q ^ (1 - γ / 2) := by
            dsimp [cI]
            rw [← hpows]
            ac_rfl
  have hμ2 : ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
      ≤ cI * (δt : ENNReal) ^ (γ - β') * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
    have hbdex : (δt : ENNReal) ^ (-ε₂ - 2 * h) * (b : ENNReal) ^ (-2 * β')
        ≤ (δt : ENNReal) ^ (γ - β') * (b : ENNReal) ^ (-2 * γ) := by
      simpa [h] using hbudget
    calc
      ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ cI * (δt : ENNReal) ^ (-ε₂ - 2 * h) * (b : ENNReal) ^ (-2 * β') * Q ^ (1 - γ / 2) := hμ1
      _ = cI * Q ^ (1 - γ / 2) * ((δt : ENNReal) ^ (-ε₂ - 2 * h) * (b : ENNReal) ^ (-2 * β')) := by
            ac_rfl
      _ ≤ cI * Q ^ (1 - γ / 2) * ((δt : ENNReal) ^ (γ - β') * (b : ENNReal) ^ (-2 * γ)) :=
            mul_le_mul_of_nonneg_left (a := cI * Q ^ (1 - γ / 2)) hbdex bot_le
      _ = cI * (δt : ENNReal) ^ (γ - β') * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
            ac_rfl
  have hg_half : (δt : ENNReal) ^ g = (δt : ENNReal) ^ (g / 2) * (δt : ENNReal) ^ (g / 2) := by
    rw [← ENNReal.rpow_add (x := (δt : ENNReal)) (g / 2) (g / 2) hδtE hδtEt]
    congr 1
    ring
  have htail0 : cI * (δt : ENNReal) ^ g * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2)
      = (cI * (δt : ENNReal) ^ (g / 2)) * (δt : ENNReal) ^ (g / 2)
          * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
    rw [hg_half]
    ac_rfl
  have hnum'g : 10 * ap' ≤ g / 2 := by simpa [g, β'] using hnum'
  have htail : (cI * (δt : ENNReal) ^ (g / 2)) * (δt : ENNReal) ^ (g / 2)
        * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2)
      ≤ (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
    have hpowg : (δt : ENNReal) ^ (g / 2) ≤ (δt : ENNReal) ^ (10 * ap') :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδt1E hnum'g
    calc
      (cI * (δt : ENNReal) ^ (g / 2)) * (δt : ENNReal) ^ (g / 2)
            * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2)
          ≤ 1 * (δt : ENNReal) ^ (g / 2) * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
            gcongr
      _ = (δt : ENNReal) ^ (g / 2) * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by simp
      _ ≤ (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) :=
            mul_le_mul_of_nonneg_right (a := Q ^ (1 - γ / 2))
              (mul_le_mul_of_nonneg_right (a := (b : ENNReal) ^ (-2 * γ)) hpowg bot_le) bot_le
  calc
    ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
        ≤ cI * (δt : ENNReal) ^ g * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := by
          simpa [g, β'] using hμ2
    _ = (cI * (δt : ENNReal) ^ (g / 2)) * (δt : ENNReal) ^ (g / 2)
          * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := htail0
    _ ≤ (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ) * Q ^ (1 - γ / 2) := htail
    _ = (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ)
          * ((t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          rw [show Q ^ (1 - γ / 2) =
              ((t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) from by
            dsimp [Q]
            apply congrArg (fun x : ENNReal => x ^ (1 - γ / 2))
            exact mul_comm ((b : ENNReal) ^ (2 : ℕ)) (t.card : ENNReal)]




/-! ### Acceptance records for repair route (i)

Two checks: the exponent charge is free, and the supply already on the tree meets the demand. -/

/-- **the `ε₂ - ε` charge is free.**

`Kakeya.ml1Boot.multiplicity_coarse_le_of_const_ball` instantiates at `ε₂ = 3 ε / 2` with the
budget hypothesis `hnum` **unchanged** and no other numeric side condition.  So routing the
coarse route through the ambient radius costs `Kakeya.ml1Boot.Params.Spec` nothing, contrary to
the warning on `Kakeya.ml1Boot.multiplicity_coarse_raw_ball`. -/
example (hdim : Module.finrank ℝ E = 3)
    {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hKKT : KatzTaoEstimate.{u} E β)
    {ε ap' : ℝ} (hε0 : 0 < ε) (hε1 : 5 * ε < 1) (hap' : 0 < ap')
    (hnum : γ - betaPrime β γ
      ≤ -72 * ε - 2 * ap' + 2 * (γ - betaPrime β γ))
    (hnum' : 10 * ap' ≤ (γ - betaPrime β γ) / 2)
    {CDelta : NNReal} (hCDelta : 1 ≤ CDelta) :
    ∃ ηs > (0 : ℝ),
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ b : NNReal, δt ≤ b → b ≤ δt ^ (1 - 5 * ε) →
      (b : ℝ) ≤ 1 / 4 →
      ∀ {κ : Type u} (t : Finset κ) (Tb : κ → ShadedTube b E),
        t.Nonempty →
        (∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall 0 (((11 : NNReal) / 2 : NNReal) : ℝ)) →
        (δt : ENNReal) ^ ((1 - 5 * ε) * ηs)
          ≤ ShadedBody.fullness t (fun l => (Tb l).toShadedBody) →
        maxDensity t (fun l => (Tb l).toConvexSpaceBody)
          ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-30 * ε - ap') →
        frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody)
            (ConvexSpaceBody.closedBall (0 : E) (((11 : NNReal) / 2 : NNReal) : ℝ)
              ((11 : NNReal) / 2 : NNReal).coe_nonneg)
          ≤ (CDelta : ENNReal) * (δt : ENNReal) ^ (-ap') →
        ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ)
            * ((t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) :=
  multiplicity_coarse_le_of_const_ball (ε₂ := 3 * ε / 2) hdim hβ0 hβ1 hγ0 hγ1 hKKT hε0 hε1 hap'
    (by linarith) (by linarith) hnum hnum' hCDelta ((11 : NNReal) / 2)
    (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)

/-- **the supply already on the tree meets that demand.**

All four `b`-tube producers of `Rescaling/CoarseDensity.lean` export the location clause
`(Tb j).carrier ⊆ closedBall 0 (5/2 + 3 C_𝕎 bp)`
(`Kakeya.ml1Boot.exists_plankTube_parentFamily` and its three siblings, the source construction, i.e. **after** the ledger of `Kakeya.ml1Boot.multTildeT_of_planksClose` recorded
that "nothing in this repository produces `b`-tubes inside the unit ball" and that the dilate
clause is "the *only* location clause").  Under the plank-width side condition
`hbq1 : C_𝕎 bp ≤ 1` — closed by `Kakeya.ml1Boot.eventually_plankPigeonhole_C_mul_le_one`, and
the same condition the producers already carry — that radius is at most `11/2`, which is exactly
the `R` reads. -/
example {bp : NNReal} (hbq1 : plankPigeonhole.C * bp ≤ 1)
    {b : NNReal} {κ : Type*} {t : Finset κ} (Tb : κ → ShadedTube b E)
    (hloc : ∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall (0 : E)
      (5 / 2 + 3 * ((plankPigeonhole.C * bp : NNReal) : ℝ))) :
    ∀ l ∈ t, (Tb l).carrier
      ⊆ Metric.closedBall (0 : E) (((11 : NNReal) / 2 : NNReal) : ℝ) := by
  intro l hl
  refine (hloc l hl).trans (Metric.closedBall_subset_closedBall ?_)
  have hb : ((plankPigeonhole.C * bp : NNReal) : ℝ) ≤ 1 := by exact_mod_cast hbq1
  push_cast
  linarith



/-- **(GWZ Lemma 8.1) The Katz–Tao bound for the `b`-tubes, at `C_Δ = C_{coarsePlank}`**
(blueprint `lem:ml1bootTbKatzTao`).

`Kakeya.ml1Boot.multiplicity_coarse_le_of_const` at `CDelta := Kakeya.ml1Boot.coarsePlank.C`,
preserving the original statement for the docstring references that name it; **it has no Lean
consumer — every occurrence of the name is prose.**  See that lemma for the mathematics. -/
theorem multiplicity_coarse_le (hdim : Module.finrank ℝ E = 3)
    {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hKKT : KatzTaoEstimate.{u} E β)
    {ε ap' : ℝ} (hε0 : 0 < ε) (hε1 : 5 * ε < 1) (hap' : 0 < ap')
    (hnum : γ - betaPrime β γ
      ≤ -72 * ε - 2 * ap' + 2 * (γ - betaPrime β γ))
    (hnum' : 10 * ap' ≤ (γ - betaPrime β γ) / 2) :
    ∃ ηs > (0 : ℝ),
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ b : NNReal, δt ≤ b → b ≤ δt ^ (1 - 5 * ε) →
      ∀ {κ : Type u} {t : Finset κ} (Tb : κ → ShadedTube b E),
        t.Nonempty →
        (∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall 0 1) →
        (δt : ENNReal) ^ ((1 - 5 * ε) * ηs)
          ≤ ShadedBody.fullness t (fun l => (Tb l).toShadedBody) →
        maxDensity t (fun l => (Tb l).toConvexSpaceBody)
          ≤ (coarsePlank.C : ENNReal) * (δt : ENNReal) ^ (-30 * ε - ap') →
        frostmanConstIn t (fun l => (Tb l).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall
          ≤ (coarsePlank.C : ENNReal) * (δt : ENNReal) ^ (-ap') →
        ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
          ≤ (δt : ENNReal) ^ (10 * ap') * (b : ENNReal) ^ (-2 * γ)
            * ((t.card : ENNReal) * (b : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  exact multiplicity_coarse_le_of_const hdim hβ0 hβ1 hγ0 hγ1 hKKT hε0 hε1 hap' hnum hnum'
    coarsePlank.one_le_C

/-! ### The parameter instantiation of the middle factor

The assembly of `Kakeya.ml1Boot.multiplicity_le_middle` runs the rescaled chain at three
exponents derived from the package, and they are *not* the naive ones.  Writing
`β₀ = β'(γ₀)`, `a = η_{j-1}` and `g₀ = γ₀ - β₀`:

* the **fullness** exponent is `aλ = a γ₀ / β₀`, strictly above `a`;
* the **Frostman** exponent is `aF = 5 aλ / ε`, strictly above `a + η₀ / ε`;
* the **eccentricity** exponent is `ap' = 10 aλ / (ε γ)`, still below `η'_{j-1}`.

The inflation of `a` to `aλ` is forced twice over and is the content of
`Kakeya.ml1Boot.middleFactor_numerics`.  First, the conclusion of the rescaled chain is
`δ̃ ^ (10 aλ / ε)`, and `δ̃ ≤ δ ^ ε` turns that into `δ ^ (10 aλ)`; the target asks for
`δ ^ (10 a)`, so `aλ > a` is exactly the room in which the fixed constant `C₂ Λ²` of
`Kakeya.ml1Boot.exists_normalizedMiddleData`(i) is absorbed into the smallness of `δ`.
Secondly, item (iii) of that lemma bounds the rescaled Frostman constant only by
`C₂ δ ^ (-η₀) δ̃ ^ (-a)`, and `δ ^ (-η₀) ≤ δ̃ ^ (-η₀ / ε)` is all that `δ̃ ≤ δ ^ ε` gives, so
the exponent the rescaled family honestly satisfies is `a + η₀ / ε` and not `a`.

That second point is why the fullness and the Frostman exponents have to be *decoupled*, and
it is the reason the retired coupled dichotomy — which forced them into a single `a` — could
not be applied at the value `a = η_{j-1}` the ladder supplies; the live form is
`Kakeya.ml1Boot.flatPrism_dichotomy_decoupled`.  Unwinding
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'`, the dichotomy at fullness exponent
`aλ`, Frostman exponent `aF` and eccentricity exponent `ap' = 10 aλ / (ε γ)` needs only
`aF (1 - γ/2) + (loss) ≤ 5 aλ / ε`, and `aF = 5 aλ / ε` is exactly that budget.  The coupled
form is the special case `aF = aλ`, which the rescaled family does not satisfy. -/

/-- **The exponents at which the rescaled chain is run** (the parameter instantiation of
blueprint `lem:ml1bootMiddleFactor`).

For an admissible package `p`, every `γ ∈ [γ₀, 1]` and every `1 ≤ j ≤ N`, with
`β₀ = β'(γ₀)`, `a = η_{j-1}` and `aλ = a γ₀ / β₀`:

* (i) `aλ > 0`;
* (ii) `a < aλ` — the room that absorbs the constant `C₂ Λ²` of
  `Kakeya.ml1Boot.exists_normalizedMiddleData`(i);
* (iii) `η(γ) / ε < aλ` — the room that turns the fullness hypothesis `δ ^ η(γ) ≤ λ` into
  `δ̃ ^ aλ ≤ λ̃`;
* (iv) `a + η₀ / ε < 5 aλ / ε` — the room that turns item (iii) of that lemma into
  `C_F(𝕋̃, B₁) ≤ δ̃ ^ (-aF)` at `aF = 5 aλ / ε`;
* (v) `0 < ap'` and (vi) `ap' ≤ η'_{j-1}` at `ap' = 10 aλ / (ε γ)` — so the whole numeric
  bookkeeping of `Kakeya.ml1Boot.numerics_strong` and
  `Kakeya.ml1Boot.Params.Spec.etaPrimeLossLe`, which is stated at `η'_{j-1}`, is available at
  `ap'` a fortiori.

Every clause is elementary: (ii) and (vi) are `β₀ < γ₀ ≤ γ`, which is the positivity and the
monotonicity of the gap; (iii) is `η(γ) ≤ ε η₀ / 2` together with `η₀ ≤ η_{j-1}`; and (iv) is
`η₀ ≤ η_{j-1}` together with `ε ≤ 1`, the inequality reducing to `ε + 1 < 5`. -/
theorem middleFactor_numerics {β γ₀ : ℝ} (hβ0 : 0 ≤ β) (hγ₀ : γ₀ ∈ Set.Ioc β 1)
    {ηKF ηKKT : ℝ → ℝ} {p : Params} (hp : p.Spec β γ₀) (hpη : p.EtaGammaSpec β γ₀ ηKF ηKKT)
    {γ : ℝ} (hγ : γ ∈ Set.Icc γ₀ 1) {j : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ p.N) :
    0 < p.η (j - 1) * γ₀ / betaPrime β γ₀ ∧
      p.η (j - 1) < p.η (j - 1) * γ₀ / betaPrime β γ₀ ∧
      p.ηGamma γ / p.ε < p.η (j - 1) * γ₀ / betaPrime β γ₀ ∧
      p.η (j - 1) + p.η 0 / p.ε < 5 * (p.η (j - 1) * γ₀ / betaPrime β γ₀) / p.ε ∧
      0 < 10 * (p.η (j - 1) * γ₀ / betaPrime β γ₀) / (p.ε * γ) ∧
      10 * (p.η (j - 1) * γ₀ / betaPrime β γ₀) / (p.ε * γ)
        ≤ p.etaPrime β γ₀ (j - 1) := by
  let b0 : ℝ := betaPrime β γ₀
  let a : ℝ := p.η (j - 1)
  let e : ℝ := p.ε
  change 0 < a * γ₀ / b0 ∧ a < a * γ₀ / b0 ∧ p.ηGamma γ / e < a * γ₀ / b0 ∧
      a + p.η 0 / e < 5 * (a * γ₀ / b0) / e ∧
      0 < 10 * (a * γ₀ / b0) / (e * γ) ∧
      10 * (a * γ₀ / b0) / (e * γ) ≤ p.etaPrime β γ₀ (j - 1)
  -- basic facts
  have hβγ : β < γ₀ := hγ₀.1
  have hγ0pos : 0 < γ₀ := lt_of_le_of_lt hβ0 hβγ
  have hb0spec := betaPrime_spec hβ0 γ₀ hγ₀
  have hb0pos : 0 < b0 := by simpa [b0] using hb0spec.1
  have hb0ltγ : b0 < γ₀ := by simpa [b0] using hb0spec.2
  have hepos : 0 < e := by simpa [e] using hp.epsPos
  have hele1 : e ≤ 1 := by simpa [e] using hp.epsLeOne
  have hη0pos : 0 < p.η 0 := hp.etaZeroPos
  have hγle : γ₀ ≤ γ := hγ.1
  have hγpos : 0 < γ := lt_of_lt_of_le hγ0pos hγle
  -- a = p.η (j - 1)
  have hsub : j - 1 ≤ p.N := le_trans (Nat.sub_le j 1) hjN
  have hmonoE : p.η 0 ≤ a := by
    dsimp [a]
    exact hp.etaMono (Set.mem_Iic.mpr (Nat.zero_le _)) (Set.mem_Iic.mpr hsub) (Nat.zero_le _)
  have ha_pos : 0 < a := lt_of_lt_of_le hη0pos hmonoE
  have heγpos : 0 < e * γ := mul_pos hepos hγpos
  have heb0pos : 0 < e * b0 := mul_pos hepos hb0pos
  have hgamLeRescale : p.ηGamma γ ≤ e * p.η 0 / 2 := by
    simpa [e] using hpη.etaGammaLeRescale γ hγ
  -- goal 1
  have h1 : 0 < a * γ₀ / b0 := div_pos (mul_pos ha_pos hγ0pos) hb0pos
  -- goal 2
  have h2 : a < a * γ₀ / b0 := by
    rw [lt_div_iff₀ hb0pos]
    exact mul_lt_mul_of_pos_left hb0ltγ ha_pos
  -- goal 3
  have hgamDiv : p.ηGamma γ / e ≤ p.η 0 / 2 := by
    rw [div_le_div_iff₀ hepos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hgamLeRescale]
  have hη0div : p.η 0 / 2 ≤ a / 2 := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_right hmonoE (by norm_num : (0 : ℝ) ≤ 2)
  have hahalf : a / 2 < a := by nlinarith [ha_pos]
  have h3mid : a / 2 < a * γ₀ / b0 := lt_trans hahalf h2
  have h3 : p.ηGamma γ / e < a * γ₀ / b0 :=
    lt_of_le_of_lt (le_trans hgamDiv hη0div) h3mid
  -- goal 4
  have h4a : a + p.η 0 / e ≤ a + a / e := by
    have hd : p.η 0 / e ≤ a / e := div_le_div_of_nonneg_right hmonoE hepos.le
    exact add_le_add_right hd a
  have h4b : a + a / e < 5 * a / e := by
    rw [lt_div_iff₀ hepos]
    field_simp [ne_of_gt hepos]
    nlinarith [mul_le_mul_of_nonneg_left hele1 ha_pos.le, ha_pos]
  have h4b' : 5 * a / e < 5 * (a * γ₀ / b0) / e := by
    rw [div_lt_div_iff₀ hepos hepos]
    field_simp [ne_of_gt hepos, ne_of_gt hb0pos]
    nlinarith [hb0ltγ, ha_pos, hepos]
  have h4 : a + p.η 0 / e < 5 * (a * γ₀ / b0) / e :=
    lt_of_le_of_lt h4a (lt_trans h4b h4b')
  -- goal 5
  have h5 : 0 < 10 * (a * γ₀ / b0) / (e * γ) :=
    div_pos (mul_pos (by norm_num : (0 : ℝ) < 10) h1) heγpos
  -- goal 6
  have hetaPrime : p.etaPrime β γ₀ (j - 1) = 10 * a / (e * b0) := by
    rfl
  have h6 : 10 * (a * γ₀ / b0) / (e * γ) ≤ p.etaPrime β γ₀ (j - 1) := by
    rw [hetaPrime]
    rw [div_le_div_iff₀ heγpos heb0pos]
    field_simp [ne_of_gt hepos, ne_of_gt hb0pos, ne_of_gt hγpos]
    nlinarith [hγle, ha_pos, hepos]
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-! #### The scale transfer `δ̃ ≤ δ ^ ε`

The four lemmas below are the whole arithmetic content of the passage between the outer scale
`δ` and the middle scale `δ̃ = τ/θ` in `Kakeya.ml1Boot.multiplicity_le_middle`.  They are
stated abstractly, in `ENNReal`, because nothing geometric is involved: the multiplicities,
fullnesses and Frostman constants enter only as opaque values. -/

/-- **A power of `δ̃` is a power of `δ`, upwards** (the scale separation `δ̃ ≤ δ ^ ε`).

If `δ̃ ≤ δ ^ ε` and `x ≥ 0` then `δ̃ ^ x ≤ δ ^ (ε x)`.  This is the direction that converts a
*conclusion* stated at the middle scale into one stated at the outer scale. -/
theorem coe_rpow_le_rpow_mul_of_sep {ε : ℝ} {δ δt : NNReal} (hδ0 : 0 < δ)
    (hsep : δt ≤ δ ^ ε) {x : ℝ} (hx : 0 ≤ x) :
    (δt : ENNReal) ^ x ≤ (δ : ENNReal) ^ (ε * x) := by
  have hsepE : (δt : ENNReal) ≤ (δ : ENNReal) ^ ε := by
    calc
      (δt : ENNReal) ≤ (δ ^ ε : NNReal) := ENNReal.coe_le_coe.mpr hsep
      _ = (δ : ENNReal) ^ ε := by
        rw [ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ0)]
  calc
    (δt : ENNReal) ^ x ≤ ((δ : ENNReal) ^ ε) ^ x := ENNReal.rpow_le_rpow hsepE hx
    _ = (δ : ENNReal) ^ (ε * x) := by rw [← ENNReal.rpow_mul]

/-- **A power of `δ̃` is a power of `δ`, downwards** (the scale separation `δ̃ ≤ δ ^ ε`).

If `δ̃ ≤ δ ^ ε` with `ε > 0`, `δ > 0` and `x ≥ 0`, then `δ̃ ^ (x / ε) ≤ δ ^ x`.  This is the
direction that converts a *hypothesis* carrying a loss `δ ^ x` at the outer scale into the
loss `δ̃ ^ (x / ε)` at the middle scale, and it is where the exponent `η₀ / ε` of blueprint
`lem:ml1bootSmallB` comes from. -/
theorem coe_rpow_div_le_rpow_of_sep {ε : ℝ} (hε0 : 0 < ε) {δ δt : NNReal} (hδ0 : 0 < δ)
    (hsep : δt ≤ δ ^ ε) {x : ℝ} (hx : 0 ≤ x) :
    (δt : ENNReal) ^ (x / ε) ≤ (δ : ENNReal) ^ x := by
  have hsepE : (δt : ENNReal) ≤ (δ : ENNReal) ^ ε := by
    calc
      (δt : ENNReal) ≤ (δ ^ ε : NNReal) := ENNReal.coe_le_coe.mpr hsep
      _ = (δ : ENNReal) ^ ε := by
        rw [ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ0)]
  have hxε : 0 ≤ x / ε := div_nonneg hx (le_of_lt hε0)
  have hpow : (δt : ENNReal) ^ (x / ε) ≤ ((δ : ENNReal) ^ ε) ^ (x / ε) :=
    ENNReal.rpow_le_rpow hsepE hxε
  have hEq : ε * (x / ε) = x := by
    field_simp [ne_of_gt hε0]
  calc
    (δt : ENNReal) ^ (x / ε) ≤ ((δ : ENNReal) ^ ε) ^ (x / ε) := hpow
    _ = (δ : ENNReal) ^ (ε * (x / ε)) := by rw [← ENNReal.rpow_mul]
    _ = (δ : ENNReal) ^ x := by rw [hEq]

/-- **The fullness hypothesis survives the rescaling.**

If `δ ^ ηΓ ≤ F`, if `F ≤ C₂ Λ² F'` — item (ii) of
`Kakeya.ml1Boot.exists_normalizedMiddleData` — and if the fixed constant is absorbed,
`C₂ Λ² δ ^ (ε aλ - ηΓ) ≤ 1`, then `δ̃ ^ aλ ≤ F'`.

In the application `F = λ(𝕌, Z)`, `F' = λ(𝕋̃, Ỹ)` and `ηΓ = η(γ)`; the absorption hypothesis
is available for small `δ` because `η(γ) / ε < aλ`
(`Kakeya.ml1Boot.middleFactor_numerics`(iii)). -/
theorem rescaled_fullness_le {ε aL ηΓ : ℝ} {Λ δ δt : NNReal} (hδ0 : 0 < δ)
    (hsep : δt ≤ δ ^ ε) (haL0 : 0 ≤ aL)
    (habs : (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2
      * (δ : ENNReal) ^ (ε * aL - ηΓ) ≤ 1)
    {F F' : ENNReal} (hF : (δ : ENNReal) ^ ηΓ ≤ F)
    (hFF : F ≤ (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2 * F') :
    (δt : ENNReal) ^ aL ≤ F' := by
  let K : ENNReal := (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2
  have hC_pos : 0 < fineFactor.C := by
    unfold fineFactor.C
    positivity
  have hK0 : K ≠ 0 := by
    dsimp [K]
    by_cases hΛ0 : (Λ : ENNReal) = 0
    · exfalso
      have hFle : F ≤ 0 := by
        calc
          F ≤ (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2 * F' := hFF
          _ = 0 := by rw [hΛ0]; simp
      have hδg : (δ : ENNReal) ^ ηΓ = 0 :=
        le_antisymm (le_trans hF hFle) bot_le
      have hpos : 0 < (δ : ENNReal) ^ ηΓ :=
        ENNReal.rpow_pos (by exact_mod_cast hδ0) ENNReal.coe_ne_top
      exact (ne_of_gt hpos) hδg
    · exact mul_ne_zero (ENNReal.coe_ne_zero.mpr (ne_of_gt hC_pos)) (pow_ne_zero 2 hΛ0)
  have hKtop : K ≠ ⊤ := by
    dsimp [K]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hKmul : K * (δt : ENNReal) ^ aL ≤ K * F' := by
    calc
      K * (δt : ENNReal) ^ aL ≤ K * (δ : ENNReal) ^ (ε * aL) := by
        have h1 : (δt : ENNReal) ^ aL ≤ (δ : ENNReal) ^ (ε * aL) :=
          coe_rpow_le_rpow_mul_of_sep hδ0 hsep haL0
        exact mul_le_mul_of_nonneg_left h1 bot_le
      _ = K * ((δ : ENNReal) ^ (ε * aL - ηΓ) * (δ : ENNReal) ^ ηΓ) := by
        congr 1
        rw [← ENNReal.rpow_add (x := (δ : ENNReal)) (ε * aL - ηΓ) ηΓ
          (ENNReal.coe_ne_zero.mpr (ne_of_gt hδ0)) ENNReal.coe_ne_top]
        congr 1
        ring
      _ = (K * (δ : ENNReal) ^ (ε * aL - ηΓ)) * (δ : ENNReal) ^ ηΓ := by
        ac_rfl
      _ ≤ 1 * (δ : ENNReal) ^ ηΓ := by
        have h_abs : K * (δ : ENNReal) ^ (ε * aL - ηΓ) ≤ 1 := by
          simpa [K] using habs
        exact mul_le_mul_of_nonneg_right (a := (δ : ENNReal) ^ ηΓ) h_abs bot_le
      _ = (δ : ENNReal) ^ ηΓ := by simp
      _ ≤ F := hF
      _ ≤ K * F' := by simpa [K] using hFF
  exact (ENNReal.mul_le_mul_iff_left hK0 hKtop).mp (by
    rw [mul_comm ((δt : ENNReal) ^ aL) K, mul_comm F' K]
    exact hKmul)

/-- **The Frostman hypothesis survives the rescaling, at the inflated exponent `aF`.**

If `X ≤ C₂ δ ^ (-e₀) δ̃ ^ (-a)` — item (iii) of
`Kakeya.ml1Boot.exists_normalizedMiddleData` — if `a + e₀ / ε ≤ aF`, and if the fixed constant
is absorbed, `C₂ δ ^ (ε aF - ε a - e₀) ≤ 1`, then `X ≤ δ̃ ^ (-aF)`.

Only `δ ^ (-e₀) ≤ δ̃ ^ (-e₀ / ε)` is used, which is
`Kakeya.ml1Boot.coe_rpow_div_le_rpow_of_sep` inverted.  It is exactly this step that forces
the Frostman exponent of the rescaled family up from `a = η_{j-1}` to `a + η₀ / ε`, and hence
forces the fullness and Frostman exponents apart; see the discussion above
`Kakeya.ml1Boot.middleFactor_numerics`. -/
theorem rescaled_frostman_le {ε a aF e₀ : ℝ} (hε0 : 0 < ε) {δ δt : NNReal} (hδ0 : 0 < δ)
    (hδt0 : 0 < δt) (hsep : δt ≤ δ ^ ε) (he₀ : 0 ≤ e₀) (ha0 : 0 ≤ a)
    (haF : a + e₀ / ε ≤ aF)
    (habs : (fineFactor.C : ENNReal) * (δ : ENNReal) ^ (ε * aF - ε * a - e₀) ≤ 1)
    {X : ENNReal}
    (hX : X ≤ (fineFactor.C : ENNReal) * (δ : ENNReal) ^ (-e₀) * (δt : ENNReal) ^ (-a)) :
    X ≤ (δt : ENNReal) ^ (-aF) := by
  let Cf : ENNReal := (fineFactor.C : ENNReal)
  let D : ENNReal := (δ : ENNReal)
  let T : ENNReal := (δt : ENNReal)
  have hT0 : T ≠ 0 := by
    dsimp [T]
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt hδt0)
  have hTtop : T ≠ ⊤ := by
    dsimp [T]
    exact ENNReal.coe_ne_top
  have ha0' : 0 ≤ a := ha0
  have hnnonneg : 0 ≤ aF - a - e₀ / ε := by
    linarith
  have h_exp : ε * (aF - a - e₀ / ε) = ε * aF - ε * a - e₀ := by
    field_simp [ne_of_gt hε0]
  have hDleT : D ^ (-e₀) ≤ T ^ (-(e₀ / ε)) := by
    have hpow : T ^ (e₀ / ε) ≤ D ^ e₀ := by
      simpa [T, D] using (coe_rpow_div_le_rpow_of_sep hε0 hδ0 hsep (x := e₀) he₀)
    rw [ENNReal.rpow_neg D e₀, ENNReal.rpow_neg T (e₀ / ε)]
    exact ENNReal.inv_le_inv.mpr hpow
  have hmid : T ^ (-(e₀ / ε)) * T ^ (-a) = T ^ (aF - a - e₀ / ε) * T ^ (-aF) := by
    rw [← ENNReal.rpow_add (x := T) (-(e₀ / ε)) (-a) hT0 hTtop,
        ← ENNReal.rpow_add (x := T) (aF - a - e₀ / ε) (-aF) hT0 hTtop]
    congr 1
    ring
  have hCe : Cf * T ^ (aF - a - e₀ / ε) ≤ (1 : ENNReal) := by
    calc
      Cf * T ^ (aF - a - e₀ / ε) ≤ Cf * D ^ (ε * (aF - a - e₀ / ε)) := by
        have hcoef : T ^ (aF - a - e₀ / ε) ≤ D ^ (ε * (aF - a - e₀ / ε)) := by
          simpa [T, D] using
            coe_rpow_le_rpow_mul_of_sep (x := aF - a - e₀ / ε) hδ0 hsep hnnonneg
        exact mul_le_mul_of_nonneg_left hcoef bot_le
      _ = Cf * D ^ (ε * aF - ε * a - e₀) := by rw [h_exp]
      _ ≤ (1 : ENNReal) := by simpa [Cf, D] using habs
  calc
    X ≤ Cf * D ^ (-e₀) * T ^ (-a) := by simpa [Cf, D, T] using hX
    _ ≤ Cf * T ^ (-(e₀ / ε)) * T ^ (-a) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hDleT bot_le) bot_le
    _ = Cf * (T ^ (-(e₀ / ε)) * T ^ (-a)) := by rw [mul_assoc]
    _ = Cf * (T ^ (aF - a - e₀ / ε) * T ^ (-aF)) := by rw [hmid]
    _ = (Cf * T ^ (aF - a - e₀ / ε)) * T ^ (-aF) := by rw [← mul_assoc]
    _ ≤ 1 * T ^ (-aF) := by
      exact mul_le_mul_of_nonneg_right hCe bot_le
    _ = T ^ (-aF) := by simp

/-- **The rescaled bound `multTildeT` implies the middle-scale bound
`multTTauInsideTTheta`.**

If `M ≤ C₂ Λ² M'` — item (i) of `Kakeya.ml1Boot.exists_normalizedMiddleData` — if `M'`
satisfies `multTildeT` at the exponent `10 aλ / ε` over an index count `N' ≤ N`, and if the
fixed constant is absorbed, `C₂ Λ² δ ^ (10 (aλ - a)) ≤ 1`, then `M` satisfies
`multTTauInsideTTheta` at the exponent `10 a`.

Two things happen here.  The bracket is monotone in the cardinality because `1 - γ/2 ≥ 0` for
`γ ≤ 1`, which is what lets the refined index set `u' ⊆ u` of
`Kakeya.ml1Boot.exists_normalizedMiddleData` be replaced by `u`; and `δ̃ ^ (10 aλ / ε)` becomes
`δ ^ (10 aλ)` by the scale separation, of which `δ ^ (10 (aλ - a))` is spent on the constant
and `δ ^ (10 a)` is the conclusion.  This is
`Kakeya.ml1Boot.middle_le_of_normalized` in the form the present chain needs: that lemma is
stated for the image of `Kakeya.ShadedTube.normalizeInto` and at a loss `δ̃ ^ (10 a / ε)` read
at the *same* exponent as the conclusion, whereas here the normalized family is the one
`Kakeya.ml1Boot.exists_normalizedMiddleData` returns, on a subfamily, and the two exponents
differ by the room `aλ - a` that the constant `C₂ Λ²` costs. -/
theorem middle_le_of_rescaled {ε aL a γ : ℝ} {Λ δ δt : NNReal} (hδ0 : 0 < δ)
    (hsep : δt ≤ δ ^ ε) (hγ1 : γ ≤ 1) (haL0 : 0 ≤ aL) (hε0 : 0 < ε)
    (habs : (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2
      * (δ : ENNReal) ^ (10 * (aL - a)) ≤ 1)
    {M M' : ENNReal} {N N' : ℕ} (hNN : N' ≤ N)
    (hM : M ≤ (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2 * M')
    (hM' : M' ≤ (δt : ENNReal) ^ (10 * aL / ε) * (δt : ENNReal) ^ (-2 * γ)
      * ((N' : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) :
    M ≤ (δ : ENNReal) ^ (10 * a) * (δt : ENNReal) ^ (-2 * γ)
      * ((N : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  let K : ENNReal := (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2
  -- Key scalar bound: the fixed constant is absorbed into `δ ^ (10 a)`.
  have hkey : K * (δt : ENNReal) ^ (10 * aL / ε) ≤ (δ : ENNReal) ^ (10 * a) := by
    have hx : (0 : ℝ) ≤ 10 * aL / ε :=
      div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) haL0) (le_of_lt hε0)
    have hsep1 : (δt : ENNReal) ^ (10 * aL / ε) ≤ (δ : ENNReal) ^ (ε * (10 * aL / ε)) :=
      coe_rpow_le_rpow_mul_of_sep hδ0 hsep hx
    have hεx : ε * (10 * aL / ε) = 10 * aL := by
      field_simp [ne_of_gt hε0]
    have hδE : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ0)
    have hδEt : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hsplit : (δ : ENNReal) ^ (10 * aL) =
        (δ : ENNReal) ^ (10 * (aL - a)) * (δ : ENNReal) ^ (10 * a) := by
      rw [← ENNReal.rpow_add (x := (δ : ENNReal)) (10 * (aL - a)) (10 * a) hδE hδEt]
      congr 1
      ring
    have h_abs : K * (δ : ENNReal) ^ (10 * (aL - a)) ≤ 1 := by
      simpa [K] using habs
    calc
      K * (δt : ENNReal) ^ (10 * aL / ε)
          ≤ K * (δ : ENNReal) ^ (ε * (10 * aL / ε)) := by
            exact mul_le_mul_of_nonneg_left hsep1 bot_le
      _ = K * (δ : ENNReal) ^ (10 * aL) := by rw [hεx]
      _ = K * ((δ : ENNReal) ^ (10 * (aL - a)) * (δ : ENNReal) ^ (10 * a)) := by rw [hsplit]
      _ = (K * (δ : ENNReal) ^ (10 * (aL - a))) * (δ : ENNReal) ^ (10 * a) := by ac_rfl
      _ ≤ 1 * (δ : ENNReal) ^ (10 * a) := by
            exact mul_le_mul_of_nonneg_right (a := (δ : ENNReal) ^ (10 * a)) h_abs bot_le
      _ = (δ : ENNReal) ^ (10 * a) := by simp
  -- Bracket monotonicity in the index count `N' ≤ N`.
  have hbr : ((N' : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
      ≤ ((N : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    have hNN' : (N' : ENNReal) ≤ (N : ENNReal) := by exact_mod_cast hNN
    have hbase : (N' : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)
        ≤ (N : ENNReal) * (δt : ENNReal) ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right (a := (δt : ENNReal) ^ (2 : ℕ)) hNN' bot_le
    have hnonneg : (0 : ℝ) ≤ 1 - γ / 2 := by linarith
    exact ENNReal.rpow_le_rpow hbase hnonneg
  -- Assemble.
  calc
    M ≤ K * M' := by simpa [K] using hM
    _ ≤ K * ((δt : ENNReal) ^ (10 * aL / ε) * (δt : ENNReal) ^ (-2 * γ)
        * ((N' : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
          exact mul_le_mul_of_nonneg_left hM' bot_le
    _ = (K * (δt : ENNReal) ^ (10 * aL / ε)) * (δt : ENNReal) ^ (-2 * γ)
        * ((N' : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by ac_rfl
    _ ≤ (δ : ENNReal) ^ (10 * a) * (δt : ENNReal) ^ (-2 * γ)
        * ((N : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          have h1 : (K * (δt : ENNReal) ^ (10 * aL / ε)) * (δt : ENNReal) ^ (-2 * γ)
              ≤ (δ : ENNReal) ^ (10 * a) * (δt : ENNReal) ^ (-2 * γ) := by
            exact mul_le_mul_of_nonneg_right (a := (δt : ENNReal) ^ (-2 * γ)) hkey bot_le
          exact mul_le_mul h1 hbr bot_le bot_le

/-- **The smallness of `δ` that the middle-factor assembly consumes.**

For all sufficiently small `δ > 0`: `δ ^ ε` is below any prescribed threshold `r` and below
`1/4`, and the three fixed constants of the assembly are absorbed by three positive exponents
`c₁, c₂, c₃`.

The threshold `r` is the radius on which the rescaled endgame
`Kakeya.ml1Boot.multTildeT_of_rescaledData` holds, reached through `δ̃ ≤ δ ^ ε`; the bound
`δ ^ ε ≤ 1/4` is the hypothesis `hquarter` of
`Kakeya.ml1Boot.exists_normalizedMiddleData`; and `c₁, c₂, c₃` are instantiated at
`10 (aλ - η_{j-1})`, `ε aλ - η(γ)` and `ε (5 aλ / ε) - ε η_{j-1} - η₀`, all positive by
`Kakeya.ml1Boot.middleFactor_numerics`. -/
theorem middleFactor_eventually {ε c₁ c₂ c₃ : ℝ} (hε0 : 0 < ε)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) {Λ : NNReal} (hΛ : 1 ≤ Λ) {r : NNReal}
    (hr0 : 0 < r) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      0 < δ ∧ δ ^ ε < r ∧ δ ^ ε ≤ 1 / 4 ∧ δ ^ ε ≤ (1 / 4 : NNReal) ^ (1 / (5 * ε)) ∧
        (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ c₁ ≤ 1 ∧
        (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ c₂ ≤ 1 ∧
        (fineFactor.C : ENNReal) * (δ : ENNReal) ^ c₃ ≤ 1 := by
  -- Fact 1: the eventual positivity of δ.
  have f1 : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), (0 : NNReal) < δ :=
    self_mem_nhdsWithin
  -- Facts 2 and 3: `δ ^ ε < r` and `δ ^ ε ≤ 1/4`, via the raw real limit template.
  have hcoet : Tendsto (fun δ : NNReal => (δ : ℝ))
      (𝓝[>] (0 : NNReal)) (𝓝 (0 : ℝ)) := by
    simpa using ((NNReal.continuous_coe.tendsto (0 : NNReal)).mono_left nhdsWithin_le_nhds)
  have htendR : Tendsto (fun δ : NNReal => (δ : ℝ) ^ ε)
      (𝓝[>] (0 : NNReal)) (𝓝 (0 : ℝ)) :=
    hcoet.rpow_const_nhds_zero hε0
  have f2 : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), δ ^ ε < r := by
    have h_ev : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), (δ : ℝ) ^ ε < (r : ℝ) :=
      htendR.eventually (eventually_lt_nhds (by exact_mod_cast hr0))
    filter_upwards [h_ev] with δ hδ
    exact_mod_cast hδ
  have f3 : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), δ ^ ε ≤ 1 / 4 := by
    have h_ev : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), (δ : ℝ) ^ ε < (1 / 4 : ℝ) :=
      htendR.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [h_ev] with δ hδ
    have hδNN : (δ : NNReal) ^ ε < (1 / 4 : NNReal) := by
      exact_mod_cast hδ
    exact le_of_lt hδNN
  -- Fact 3': the same at the sharper threshold `(1/4) ^ (1 / (5 ε))`, which puts the whole
  -- rescaled Frostman window of `Kakeya.ml1Boot.exists_normalizedMiddleData`(iv) below `1/4`.
  have f3' : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
      δ ^ ε ≤ (1 / 4 : NNReal) ^ (1 / (5 * ε)) := by
    have hpos : (0 : ℝ) < ((1 / 4 : NNReal) ^ (1 / (5 * ε)) : NNReal) := by
      have : (0 : NNReal) < (1 / 4 : NNReal) ^ (1 / (5 * ε)) :=
        NNReal.rpow_pos (by rw [← NNReal.coe_lt_coe]; push_cast; norm_num)
      exact_mod_cast this
    have h_ev : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
        (δ : ℝ) ^ ε < ((1 / 4 : NNReal) ^ (1 / (5 * ε)) : NNReal) :=
      htendR.eventually (eventually_lt_nhds hpos)
    filter_upwards [h_ev] with δ hδ
    have hδNN : (δ : NNReal) ^ ε < (1 / 4 : NNReal) ^ (1 / (5 * ε)) := by
      exact_mod_cast hδ
    exact le_of_lt hδNN
  -- Constant absorption: facts 4 and 5 with `C = fineFactor.C * Λ ^ 2`, fact 6 with
  -- `C = fineFactor.C`.
  have hΛpos : (0 : NNReal) < Λ := lt_of_lt_of_le (by norm_num) hΛ
  have hΛE0 : (Λ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hΛpos)
  have hFineCpos : 0 < fineFactor.C := by
    unfold fineFactor.C
    positivity
  have hFineC0 : (fineFactor.C : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hFineCpos)
  have f4 : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
      (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ c₁ ≤ 1 := by
    let C : ENNReal := (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2
    have hC0 : C ≠ 0 := by
      dsimp [C]
      exact mul_ne_zero hFineC0 (pow_ne_zero 2 hΛE0)
    have hCtop : C ≠ ⊤ := by
      dsimp [C]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hinv : 0 < C⁻¹ := by
      rw [ENNReal.inv_pos]
      exact hCtop
    filter_upwards [ENNReal.eventually_coe_rpow_le_of_pos (ρ := c₁) hc₁ hinv] with δ hδ
    calc
      C * (δ : ENNReal) ^ c₁ ≤ C * C⁻¹ := by
        exact mul_le_mul_of_nonneg_left hδ (by positivity)
      _ = 1 := ENNReal.mul_inv_cancel hC0 hCtop
  have f5 : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
      (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ c₂ ≤ 1 := by
    let C : ENNReal := (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2
    have hC0 : C ≠ 0 := by
      dsimp [C]
      exact mul_ne_zero hFineC0 (pow_ne_zero 2 hΛE0)
    have hCtop : C ≠ ⊤ := by
      dsimp [C]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hinv : 0 < C⁻¹ := by
      rw [ENNReal.inv_pos]
      exact hCtop
    filter_upwards [ENNReal.eventually_coe_rpow_le_of_pos (ρ := c₂) hc₂ hinv] with δ hδ
    calc
      C * (δ : ENNReal) ^ c₂ ≤ C * C⁻¹ := by
        exact mul_le_mul_of_nonneg_left hδ (by positivity)
      _ = 1 := ENNReal.mul_inv_cancel hC0 hCtop
  have f6 : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
      (fineFactor.C : ENNReal) * (δ : ENNReal) ^ c₃ ≤ 1 := by
    have hCtop : (fineFactor.C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hinv : 0 < (fineFactor.C : ENNReal) ⁻¹ := by
      rw [ENNReal.inv_pos]
      exact hCtop
    filter_upwards [ENNReal.eventually_coe_rpow_le_of_pos hc₃ hinv] with δ hδ
    calc
      (fineFactor.C : ENNReal) * (δ : ENNReal) ^ c₃
          ≤ (fineFactor.C : ENNReal) * (fineFactor.C : ENNReal)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hδ (by positivity)
      _ = 1 := ENNReal.mul_inv_cancel hFineC0 hCtop
  filter_upwards [f1, f2, f3, f3', f4, f5, f6] with δ h1 h2 h3 h3' h4 h5 h6
  exact ⟨h1, h2, h3, h3', h4, h5, h6⟩

/-! `Kakeya.ml1Boot.normalizedUnif.C` and `Kakeya.ml1Boot.normalizedUnif.one_le_C` have moved
upstream to `Kakeya/DimensionThree/MainLemma1/Rescaling/Normalized.lean`, beside the lemma that
now returns the uniformity.

`Kakeya.ml1Boot.exists_normalizedMiddleData_unif`, which was
`Kakeya.ml1Boot.exists_normalizedMiddleData` with the uniformity hypothesis and conclusion added,
has been **retired**: that hypothesis and that conclusion are now part of
`Kakeya.ml1Boot.exists_normalizedMiddleData` itself, which also gained the ambient family the
blueprint requires (`note:ml1bootRescaledLowerAmbient`).  Use it directly. -/

/-- **The `ρ`-parent family of the rescaled middle data** (obstruction (2) of
`Kakeya.ml1Boot.multTildeT_of_rescaledData`).

Item (iv) of `Kakeya.ml1Boot.exists_normalizedMiddleData` attaches a `ρ`-tube to each `k`
separately, whereas `Kakeya.ml1Boot.exists_plankDimensions` consumes a
`Kakeya.ml1Boot.IsParentFamily` together with `Set.SurjOn`.  This is that conversion.

The parents are indexed by a subset `t_ρ ⊆ u'` of the family itself, so containment in `B₁`
and the Frostman lower bound are read off the input hypothesis *at the representative*, with
no transport: for `m ∈ t_ρ ⊆ u'` the clause wanted is literally `hpt m`.  That is the reason
for taking `κ := ι` here rather than an abstract parent type.

The Frostman lower bound is read at an *ambient* index set `un'`, which is carried opaquely
from hypothesis to conclusion and never has to be related to `u'`.  This is what
`Kakeya.ml1Boot.exists_normalizedMiddleData`(iv) supplies (blueprint
`note:ml1bootRescaledLowerAmbient`) and what
`Kakeya.ml1Boot.multTildeT_of_rescaledData` therefore hypothesises; reading it at `u'`
instead would be strictly stronger and is not available, since `frostmanConstIn` over the
larger index set `un' ⊇ u'` does not bound `frostmanConstIn` over `u'` from below.

The only step doing real work is `Kakeya.ml1Boot.exists_dedupe`.  The `injOn` clause of
`IsParentFamily` is injectivity of `m ↦ (T_{ρ,m}).toConvexSpaceBody` on `t_ρ`, which pointwise
data cannot provide — two different `k` may be handed the same `ρ`-tube — and deduplication is
what supplies it; `le_parent` then follows since the representative's body *equals* the
original's.  Nonemptiness of `u'` enters only to define the parent function off `u'`, where its
value is irrelevant.  No `DecidableEq ι` is assumed: the case split defining that function is
made with `classical` inside the proof.

Essential distinctness of the parents is deliberately *not* produced here.  It is needed by
`Kakeya.ml1Boot.maxDensity_coarse_le` but not by `Kakeya.ml1Boot.exists_plankDimensions`, and
the only selection available, `Tube.exists_essDistinct_dilateCover`, delivers containment in a
dilate of ratio `Tube.tubeOverlapCoreClose.C 3` rather than the undilated containment that
`IsParentFamily` demands.  That tension is items (3) and (6) of the obstruction list on
`Kakeya.ml1Boot.multTildeT_of_rescaledData`, and composing the existing API does not resolve
it. -/
theorem exists_parentFamily_of_pointwiseTubes {δt ρt : NNReal}
    {ι : Type*} {u' un' : Finset ι} (Ttil : ι → ShadedTube δt E)
    (hu' : u'.Nonempty) {c : ENNReal}
    (hpt : ∀ k ∈ u', ∃ Tρ : Tube ρt E, Tρ.carrier ⊆ Metric.closedBall 0 1 ∧
      (Ttil k).toConvexSpaceBody ≤ Tρ.toConvexSpaceBody ∧
      c ≤ frostmanConstIn
            (familyIn un' (fun k' => (Ttil k').toConvexSpaceBody) (Tube.dilate Tρ 2))
            (fun k' => (Ttil k').toConvexSpaceBody) (Tube.dilate Tρ 2)) :
    ∃ tρ ⊆ u', ∃ (Tρ : ι → Tube ρt E) (pρ : ι → ι),
      IsParentFamily u' (fun k => (Ttil k).toTube) tρ Tρ pρ ∧
      Set.SurjOn pρ ↑u' ↑tρ ∧
      (∀ m ∈ tρ, (Tρ m).carrier ⊆ Metric.closedBall 0 1) ∧
      (∀ m ∈ tρ, c ≤ frostmanConstIn
          (familyIn un' (fun k' => (Ttil k').toConvexSpaceBody) (Tube.dilate (Tρ m) 2))
          (fun k' => (Ttil k').toConvexSpaceBody) (Tube.dilate (Tρ m) 2)) := by
  classical
  let Tρ0 : ι → Tube ρt E :=
    fun k => if h : k ∈ u' then (hpt k h).choose else (hpt hu'.choose hu'.choose_spec).choose
  obtain ⟨tρ, htρ_sub, qρ, hq_map, hq_body, hq_inj, hq_surj⟩ :=
    exists_dedupe (s := u') (V := Tρ0)
  refine ⟨tρ, htρ_sub, Tρ0, qρ, ?_⟩
  · refine ⟨?_, hq_surj, ?_, ?_⟩
    · refine ⟨hq_map, hq_inj, ?_⟩
      · intro k hk
        rw [hq_body k hk]
        simp only [Tρ0]
        rw [dif_pos hk]
        exact (hpt k hk).choose_spec.2.1
    · intro m hm
      simp only [Tρ0]
      rw [dif_pos (htρ_sub hm)]
      exact (hpt m (htρ_sub hm)).choose_spec.1
    · intro m hm
      simp only [Tρ0]
      rw [dif_pos (htρ_sub hm)]
      exact (hpt m (htρ_sub hm)).choose_spec.2.2

/-- **The `ρ`-parent family of the rescaled middle data at the parent scale `δ̃ ^ (6 ε)`.**

`Kakeya.ml1Boot.exists_parentFamily_of_pointwiseTubes` specialised to the one scale the
middle-factor assembly uses.  The `5 ε`-window of
`Kakeya.ml1Boot.exists_normalizedMiddleData`(iv) is `[δ̃ ^ (1 - 5 ε), δ̃ ^ (5 ε)]`, and
`δ̃ ^ (6 ε)` lies in it exactly when `5 ε ≤ 6 ε ≤ 1 - 5 ε`, i.e. when `11 ε ≤ 1`; that is
`hε11`, available from `Kakeya.ml1Boot.Params.Spec.epsLeInvSixtyFour`.

The parent scale is `6 ε` and not `2 ε` for the reason recorded on
`Kakeya.ml1Boot.multiplicity_le_middle`: `δ̃ ^ (2 ε)` is outside the window, and `6 ε` is the
least multiple of `ε` inside it that still gives `b♯ ≤ C_𝕎 b ≤ δ̃ ^ (5 ε)`.

The Frostman lower bound `c` is a *function of the scale*, not a constant.  This is forced:
`Kakeya.ml1Boot.exists_normalizedMiddleData`(iv) reads it as
`C⁻¹ δ̃ ^ (η₀ / ε) (ρ / δ̃) ^ η_j`, which is strictly increasing in `ρ`, so no single value of
it holds across the whole `5 ε`-window and the conclusion has to name the scale `δ̃ ^ (6 ε)` at
which the bound is taken. -/
theorem exists_parentFamily_atSixEps {ε : ℝ} (hε0 : 0 < ε) (hε11 : 11 * ε ≤ 1)
    {δt : NNReal} (hδt1 : δt ≤ 1)
    {ι : Type*} {u' un' : Finset ι} (Ttil : ι → ShadedTube δt E) (hu' : u'.Nonempty)
    {c : NNReal → ENNReal}
    (hlow : ∀ ρt : NNReal, δt ^ (1 - 5 * ε) ≤ ρt → ρt ≤ δt ^ (5 * ε) → ∀ k ∈ u',
      ∃ Tρ : Tube ρt E, Tρ.carrier ⊆ Metric.closedBall 0 1 ∧
        (Ttil k).toConvexSpaceBody ≤ Tρ.toConvexSpaceBody ∧
        c ρt ≤ frostmanConstIn
              (familyIn un' (fun k' => (Ttil k').toConvexSpaceBody) (Tube.dilate Tρ 2))
              (fun k' => (Ttil k').toConvexSpaceBody) (Tube.dilate Tρ 2)) :
    ∃ tρ ⊆ u', ∃ (Tρ : ι → Tube (δt ^ (6 * ε)) E) (pρ : ι → ι),
      IsParentFamily u' (fun k => (Ttil k).toTube) tρ Tρ pρ ∧
      Set.SurjOn pρ ↑u' ↑tρ ∧
      (∀ m ∈ tρ, (Tρ m).carrier ⊆ Metric.closedBall 0 1) ∧
      (∀ m ∈ tρ, c (δt ^ (6 * ε)) ≤ frostmanConstIn
          (familyIn un' (fun k' => (Ttil k').toConvexSpaceBody) (Tube.dilate (Tρ m) 2))
          (fun k' => (Ttil k').toConvexSpaceBody) (Tube.dilate (Tρ m) 2)) := by
  classical
  by_cases hz : δt = 0
  · subst δt
    have hpos1 : 1 - 5 * ε ≠ 0 := by nlinarith
    have hpos2 : 6 * ε ≠ 0 := by nlinarith
    have hpos3 : 5 * ε ≠ 0 := by nlinarith
    exact exists_parentFamily_of_pointwiseTubes Ttil hu'
      (hlow (0 ^ (6 * ε))
        (by rw [NNReal.zero_rpow hpos1, NNReal.zero_rpow hpos2])
        (by rw [NNReal.zero_rpow hpos2, NNReal.zero_rpow hpos3]))
  · have hδ0 : 0 < δt := lt_of_le_of_ne (by positivity : (0 : NNReal) ≤ δt) (ne_comm.mp hz)
    exact exists_parentFamily_of_pointwiseTubes Ttil hu'
      (hlow (δt ^ (6 * ε))
        (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδt1 (by nlinarith))
        (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδt1 (by nlinarith)))

/-- **The `ρ`-parent family at `δ̃ ^ (6 ε)`, counted** — a hybrid of
`Kakeya.ml1Boot.exists_parentFamily_atSixEps` and the essential-distinctness-free packing of
`Kakeya/DimensionThree/HybridParentPacking.lean`.

The conclusion is that of `Kakeya.ml1Boot.exists_parentFamily_atSixEps` with two changes:
`Kakeya.ml1Boot.IsParentFamily` weakens to `Kakeya.ml1Boot.IsParentFamilyDilate 2`, and the
parent set acquires the count `|t_ρ| ≤ C ρ ^ (-5)` at `ρ = δ̃ ^ (6 ε)`, `C` being the absolute
constant `Kakeya.hybridPackingConst`.  The count is what the endgame budgets for at this scale;
`Kakeya.ml1Boot.card_merged_rhoParents_le` supplies one too, but only *after* a merge that needs
pairwise essential distinctness of the parents, which is precisely the datum this route does not
have to produce.

## Why the `hlow` tubes stay as the parents

Only the parent *index set* and the parent *map* come from the packing; the parent tubes
themselves are still the ones `hlow` hands out, exactly as in
`Kakeya.ml1Boot.exists_parentFamily_of_pointwiseTubes`.  That is what keeps the last two clauses
— containment of the parent in `B₁` and the per-parent Frostman lower bound — free: the retained
parents form a subset of `u'`, so both are read off `hlow` *at the representative*, with no
transport.  Replacing the tubes wholesale by packing representatives would break the Frostman
clause irreparably, since `Kakeya.frostmanConstIn` over a larger index set does not bound
`Kakeya.frostmanConstIn` over a smaller one from below — the same non-monotonicity recorded on
`Kakeya.ml1Boot.exists_parentFamily_of_pointwiseTubes` for the ambient set `un'`.

## The ratio is `2`

`Kakeya.exists_separatedAssignment_abstract` at separation `ρ / 8` gives, for each `k ∈ u'`, a
selected `σ k` with `tubeParamDist (T_ρ (σ k)) (T_ρ k) ≤ ρ / 8`.  The leaf sits *undilated*
inside its own `ρ`-tube, so `Kakeya.carrier_subset_rescale_of_tubeParamDist_le` moves it into the
`s`-rescale of the selected one as soon as `ρ + 3 (ρ/8) / 2 ≤ s`, i.e. `s = 19 ρ / 16`; and
`Kakeya.Tube.rescale_le_dilate_of_le_mul` puts that rescale inside the `C`-dilate for any
`C ≥ 1` with `s ≤ C ρ`.  Since `19/16 ≤ 2`, `C = 2` suffices — and `2` is also the ratio the rest
of the development already pays (`Kakeya.ml1Boot.IsParentFamilyDilate`), so nothing new is
charged.

## Injectivity is not free

The separation of the selected set is a statement about tube *parameters* — centres and
directions — whereas the `injOn` clause of `Kakeya.ml1Boot.IsParentFamilyDilate` is injectivity
of `m ↦ (T_ρ m).toConvexSpaceBody`, a statement about *bodies*.  The one does not give the other:
a tube and its `Kakeya.Tube.reverse` have the same body at parameter distance `2` in the
direction, so the parameter map is not determined by the body.  Injectivity is therefore supplied
by `Kakeya.ml1Boot.exists_dedupe_dilate`, exactly as
`Kakeya.ml1Boot.exists_parentFamily_of_pointwiseTubes` supplies it with
`Kakeya.ml1Boot.exists_dedupe`.  The *dilate* form of the dedupe is the one wanted here, because
`Kakeya.Tube.dilate` is a homothety about the centre and so must be transported across equal
bodies by `Kakeya.Tube.dilate_congr` rather than read off the body equality directly.

`0 < δ̃` is required, unlike in `Kakeya.ml1Boot.exists_parentFamily_atSixEps`: the packing count
is vacuous at `ρ = 0` and `Kakeya.exists_separatedAssignment_abstract` asks for `0 < ρ`. -/
theorem exists_parentFamilyDilate_atSixEps_card [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {ε : ℝ} (hε0 : 0 < ε) (hε11 : 11 * ε ≤ 1)
    {δt : NNReal} (hδt0 : 0 < δt) (hδt1 : δt ≤ 1)
    {ι : Type*} {u' un' : Finset ι} (Ttil : ι → ShadedTube δt E) (hu' : u'.Nonempty)
    {c : NNReal → ENNReal}
    (hlow : ∀ ρt : NNReal, δt ^ (1 - 5 * ε) ≤ ρt → ρt ≤ δt ^ (5 * ε) → ∀ k ∈ u',
      ∃ Tρ : Tube ρt E, Tρ.carrier ⊆ Metric.closedBall 0 1 ∧
        (Ttil k).toConvexSpaceBody ≤ Tρ.toConvexSpaceBody ∧
        c ρt ≤ frostmanConstIn
              (familyIn un' (fun k' => (Ttil k').toConvexSpaceBody) (Tube.dilate Tρ 2))
              (fun k' => (Ttil k').toConvexSpaceBody) (Tube.dilate Tρ 2)) :
    ∃ tρ ⊆ u', ∃ (Tρ : ι → Tube (δt ^ (6 * ε)) E) (pρ : ι → ι),
      IsParentFamilyDilate 2 u' (fun k => (Ttil k).toTube) tρ Tρ pρ ∧
      Set.SurjOn pρ ↑u' ↑tρ ∧
      (∀ m ∈ tρ, (Tρ m).carrier ⊆ Metric.closedBall 0 1) ∧
      (∀ m ∈ tρ, c (δt ^ (6 * ε)) ≤ frostmanConstIn
          (familyIn un' (fun k' => (Ttil k').toConvexSpaceBody) (Tube.dilate (Tρ m) 2))
          (fun k' => (Ttil k').toConvexSpaceBody) (Tube.dilate (Tρ m) 2)) ∧
      (tρ.card : ENNReal)
        ≤ (hybridPackingConst : ENNReal) * ((δt ^ (6 * ε) : NNReal) : ENNReal) ^ (-5 : ℝ) := by
  classical
  let ρ : NNReal := δt ^ (6 * ε)
  have hρ0 : 0 < ρ := by
    dsimp [ρ]
    exact NNReal.rpow_pos hδt0
  have hρ1 : ρ ≤ 1 := by
    dsimp [ρ]
    exact NNReal.rpow_le_one hδt1 (by positivity : (0 : ℝ) ≤ 6 * ε)
  have hpt : ∀ k ∈ u', ∃ Tρ : Tube ρ E, Tρ.carrier ⊆ Metric.closedBall 0 1 ∧
        (Ttil k).toConvexSpaceBody ≤ Tρ.toConvexSpaceBody ∧
        c ρ ≤ frostmanConstIn
              (familyIn un' (fun k' => (Ttil k').toConvexSpaceBody) (Tube.dilate Tρ 2))
              (fun k' => (Ttil k').toConvexSpaceBody) (Tube.dilate Tρ 2) := by
    intro k hk
    exact hlow ρ
      (by dsimp [ρ]; exact NNReal.rpow_le_rpow_of_exponent_ge hδt0 hδt1 (by nlinarith))
      (by dsimp [ρ]; exact NNReal.rpow_le_rpow_of_exponent_ge hδt0 hδt1 (by nlinarith))
      k hk
  let Tρ0 : ι → Tube ρ E :=
    fun k => if h : k ∈ u' then (hpt k h).choose else (hpt hu'.choose hu'.choose_spec).choose
  obtain ⟨S, assign, hSu', hSsep, hmem, hclose⟩ :=
    exists_separatedAssignment_abstract (δ := ρ) (ρ := ρ) hρ0 u' hu' Tρ0
  obtain ⟨t, htS, r, hinj, hrt, hrsurj, hdil⟩ :=
    exists_dedupe_dilate S Tρ0
  have htu' : t ⊆ u' := htS.trans hSu'
  refine ⟨t, htu', Tρ0, fun k => r (assign k), ?_, ?_, ?_, ?_, ?_⟩
  · -- IsParentFamilyDilate
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num
    · intro k hk
      exact hrt (assign k) (hmem k hk)
    · exact hinj
    · intro k hk
      let s : NNReal := 19 * ρ / 16
      have hs1 : (ρ : ℝ) + 3 * ((ρ : ℝ) / 8) / 2 ≤ (s : ℝ) := by
        dsimp [s]
        nlinarith
      have hs2 : (s : ℝ) ≤ 2 * (ρ : ℝ) := by
        dsimp [s]
        nlinarith [NNReal.coe_nonneg ρ]
      have hclose_k : tubeParamDist (Tρ0 k) (Tρ0 (assign k)) ≤ (ρ : ℝ) / 8 := by
        rw [tubeParamDist_comm]
        exact hclose k hk
      have hsub : (Tρ0 k).carrier ⊆ ((Tρ0 (assign k)).rescale s).carrier := by
        exact carrier_subset_rescale_of_tubeParamDist_le (Tρ0 k) (Tρ0 (assign k))
          (by positivity) hclose_k hs1
      have hb1 : (Ttil k).toConvexSpaceBody ≤ (Tρ0 k).toConvexSpaceBody := by
        simp only [Tρ0]
        rw [dif_pos hk]
        exact (hpt k hk).choose_spec.2.1
      have hsubbody : (Tρ0 k).toConvexSpaceBody
          ≤ ((Tρ0 (assign k)).rescale s).toConvexSpaceBody := by
        change (Tρ0 k).carrier ⊆ ((Tρ0 (assign k)).rescale s).carrier
        exact hsub
      have hb3 : ((Tρ0 (assign k)).rescale s).toConvexSpaceBody ≤ Tube.dilate (Tρ0 (assign k)) 2 :=
        Tube.rescale_le_dilate_of_le_mul (Tρ0 (assign k)) (by norm_num : (1 : ℝ) ≤ 2) hs2
      have hbody : (Ttil k).toConvexSpaceBody ≤ Tube.dilate (Tρ0 (assign k)) 2 :=
        le_trans hb1 (le_trans hsubbody hb3)
      rw [hdil (assign k) (hmem k hk) 2]
      exact hbody
  · -- SurjOn
    intro m hm
    rcases hrsurj hm with ⟨j, hjS, hrj⟩
    refine ⟨j, hSu' hjS, ?_⟩
    calc
      r (assign j) = r j := by rw [assign_eq_self_of_mem_separated hSu' hSsep hmem hclose hjS]
      _ = m := hrj
  · -- ball
    intro m hm
    have hmu : m ∈ u' := htu' hm
    simp only [Tρ0]
    rw [dif_pos hmu]
    exact (hpt m hmu).choose_spec.1
  · -- frostman
    intro m hm
    have hmu : m ∈ u' := htu' hm
    simp only [Tρ0]
    rw [dif_pos hmu]
    exact (hpt m hmu).choose_spec.2.2
  · -- count
    have hsep_t : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → (ρ : ℝ) / 8 < tubeParamDist (Tρ0 i) (Tρ0 j) := by
      intro i hi j hj hij
      exact hSsep i (htS hi) j (htS hj) hij
    have hball_t : ∀ i ∈ t, (Tρ0 i).carrier ⊆ Metric.closedBall (0 : E) 1 := by
      intro i hi
      have hiu : i ∈ u' := htu' hi
      simp only [Tρ0]
      rw [dif_pos hiu]
      exact (hpt i hiu).choose_spec.1
    exact card_le_of_tubeParamDist_separated_of_finrank_three hdim Tρ0 t hρ0 hρ1 hsep_t hball_t

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Restricting the parents of a parent family** (first half of obstruction (6) of
`Kakeya.ml1Boot.multTildeT_of_rescaledData`).

`Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le` delivers its coarse Frostman bound only after
passing to a subset `t' ⊆ t_b` of the parents, which the obstruction list records as *breaking
the parent family*.  It does not: discarding the leaves whose parent did not survive leaves an
honest `Kakeya.ml1Boot.IsParentFamily` over `t'`, still surjective, and — this is the point —
every *retained* fibre is unchanged, `s[m] = (s ∩ p⁻¹ t')[m]` for `m ∈ t'`.  So a clause
quantified over fibres, such as a fibrewise Frostman bound, transports across the restriction
for free rather than having to be re-derived.

Nothing here is new mathematics: it is `Kakeya.ml1Boot.IsParentFamily.mono` for the structure
and `Kakeya.ml1Boot.fibre_filter_mem` for the fibres.  It is packaged as one statement because
the three clauses are always wanted together, and because reading the fibre clause off is what
makes the restriction free.

What this does *not* address is the other half of obstruction (6): the dyadic-pigeonhole factor
`L(|u'|, δ̃)` that the same lemma carries is not a constant, so it is not absorbed by the `C_Δ`
of `Kakeya.ml1Boot.multiplicity_coarse_le`(c).  That half is a genuine mismatch and is left
recorded there. -/
theorem isParentFamily_restrictParents {σ ρ : NNReal} {ι κ : Type*} [DecidableEq κ]
    {s : Finset ι} {t t' : Finset κ} {V : ι → Tube σ E} {Vρ : κ → Tube ρ E} {p : ι → κ}
    (h : IsParentFamily s V t Vρ p) (hsurj : Set.SurjOn p ↑s ↑t) (ht' : t' ⊆ t) :
    IsParentFamily (s.filter fun i => p i ∈ t') V t' Vρ p ∧
      Set.SurjOn p ↑(s.filter fun i => p i ∈ t') ↑t' ∧
      ∀ m ∈ t', fibre (s.filter fun i => p i ∈ t') p m = fibre s p m := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact IsParentFamily.mono h (Finset.filter_subset _ _) ht'
      (fun i hi => (Finset.mem_filter.mp hi).2)
  · intro m hm
    rcases hsurj (Finset.mem_coe.mpr (ht' (Finset.mem_coe.mp hm))) with ⟨i, his, hpi⟩
    refine ⟨i, Finset.mem_coe.mpr ?_, hpi⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_coe.mp his, by rw [hpi]; exact Finset.mem_coe.mp hm⟩
  · intro m hm
    exact fibre_filter_mem s p t' hm

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Restricting the leaves of a parent family, and trimming the parents to the image.**

The companion of `Kakeya.ml1Boot.isParentFamily_restrictParents`, on the other side.
`Kakeya.ml1Boot.exists_plankDimensions` passes to a subfamily `u'' ⊆ u'` of the *leaves*, and
`Kakeya.ml1Boot.IsParentFamily.mono` restricts along it, but the surjectivity of the parent map
is lost: a parent of `u'` may have no leaf left in `u''`.  Trimming the parent set to
`p_ρ '' u''` restores it, and the trimmed set is still inside the original one, so every clause
quantified over parents — containment in `B₁`, the Frostman lower bound, the plank
factorizations — restricts for free.

Surjectivity is what `Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le` consumes, so it has to
survive the passage to `u''`; the flat-prism dichotomy itself does not need it. -/
theorem isParentFamily_restrictLeaves {σ ρ : NNReal} {ι κ : Type*} [DecidableEq κ]
    {u'' u' : Finset ι} {tρ : Finset κ} {V : ι → Tube σ E} {Vρ : κ → Tube ρ E} {pρ : ι → κ}
    (h : IsParentFamily u' V tρ Vρ pρ) (hsub : u'' ⊆ u') :
    IsParentFamily u'' V (u''.image pρ) Vρ pρ ∧
      Set.SurjOn pρ ↑u'' ↑(u''.image pρ) ∧ u''.image pρ ⊆ tρ := by
  classical
  have himg : u''.image pρ ⊆ tρ := by
    intro m hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    exact h.mapsTo i (hsub hi)
  refine ⟨?_, ?_, himg⟩
  · exact IsParentFamily.mono h hsub himg (fun i hi => Finset.mem_image_of_mem pρ hi)
  · rw [Finset.coe_image]
    exact Set.surjOn_image pρ (u'' : Set ι)

/-- **Every parent family is a `c`-dilate parent family, for every `c ≥ 1`.**

`Kakeya.ml1Boot.IsParentFamilyDilate c` weakens `Kakeya.ml1Boot.IsParentFamily` in exactly one
clause, `le_parent` to `le_parent_dilate`, and `Kakeya.Tube.subset_dilate` bridges it: a tube
lies in its own `c`-dilate as soon as `1 ≤ c`.  The other two clauses are copied.

The docstring of `Kakeya.ml1Boot.IsParentFamilyDilate` asserted this implication, but until now
nothing in the repository proved it, so the direction of the weakening was an unchecked claim.
It is checked here, and it is what makes the comparison on
`Kakeya.ml1Boot.multTildeT_of_planksClose` — where the parent hypothesis was moved from
`IsParentFamily` to `IsParentFamilyDilate 2` — a verifiable statement rather than an
assertion. -/
theorem isParentFamilyDilate_of_isParentFamily [Nontrivial E] {σ ρ : NNReal} {c : ℝ}
    {ι κ : Type*} {s : Finset ι} {t : Finset κ}
    {V : ι → Tube σ E} {Vρ : κ → Tube ρ E} {p : ι → κ}
    (h : IsParentFamily s V t Vρ p) (hc : 1 ≤ c) :
    IsParentFamilyDilate c s V t Vρ p := by
  refine ⟨hc, h.mapsTo, h.injOn, ?_⟩
  intro i hi
  calc
    (V i).toConvexSpaceBody ≤ (Vρ (p i)).toConvexSpaceBody := h.le_parent i hi
    _ ≤ Tube.dilate (Vρ (p i)) c := by
      apply SetLike.coe_subset_coe.mp
      exact Tube.subset_dilate (Vρ (p i)) hc

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Restricting the leaves of a `c`-dilate parent family, and trimming the parents to the
image.**

`Kakeya.ml1Boot.isParentFamily_restrictLeaves` with the containment clause weakened from
`Kakeya.ml1Boot.IsParentFamily` to `Kakeya.ml1Boot.IsParentFamilyDilate c`.  Nothing in that
proof reads the containment: the trimmed parent set is the image of the retained leaves, so the
parent map is total on it and surjective onto it, and the containment clause — whichever of the
two it is — restricts along `u'' ⊆ u'` unchanged. -/
theorem isParentFamilyDilate_restrictLeaves [Nontrivial E] {σ ρ : NNReal} {c : ℝ}
    {ι κ : Type*} [DecidableEq κ]
    {u'' u' : Finset ι} {tρ : Finset κ} {V : ι → Tube σ E} {Vρ : κ → Tube ρ E} {pρ : ι → κ}
    (h : IsParentFamilyDilate c u' V tρ Vρ pρ) (hsub : u'' ⊆ u') :
    IsParentFamilyDilate c u'' V (u''.image pρ) Vρ pρ ∧
      Set.SurjOn pρ ↑u'' ↑(u''.image pρ) ∧ u''.image pρ ⊆ tρ := by
  classical
  have himg : u''.image pρ ⊆ tρ := by
    intro m hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    exact h.mapsTo i (hsub hi)
  refine ⟨?_, ?_, himg⟩
  · refine ⟨h.one_le, ?_, ?_, ?_⟩
    · intro i hi
      exact Finset.mem_image_of_mem pρ hi
    · exact h.injOn.mono (Finset.coe_subset.mpr himg)
    · intro i hi
      exact h.le_parent_dilate i (hsub hi)
  · rw [Finset.coe_image]
    exact Set.surjOn_image pρ (u'' : Set ι)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A unit-radius tube containing the closed unit ball.**

A `Kakeya.Tube` of radius `1` is the closed `1`-neighbourhood of a unit segment
(`Kakeya.Tube.carrier_eq`), so the one centred at the origin contains `closedBall 0 1`: the
origin is the midpoint of its core segment, and the ball around that single point is already
one of the balls in the union.

This is what lets the flat-prism branch of the endgame be run *without* a parent family of its
own.  `Kakeya.ml1Boot.multiplicity_le_of_factorsThroughFlatPrisms'` reads the parent data only
through `p i ∈ t` and `V i ⊆ V_ρ (p i)` at some scale `ρ ≤ 1`, so a family whose members all
lie in `B₁` may be given the *constant* unit tube as its parent and the containment is free.
See `Kakeya.ml1Boot.flatPrism_dichotomy_ambient`. -/
theorem exists_tube_one_superset_unitBall [Nontrivial E] :
    ∃ T : Tube 1 E, Metric.closedBall (0 : E) 1 ⊆ T.carrier := by
  rcases exists_ne (0 : E) with ⟨v, hv⟩
  let u : E := ‖v‖⁻¹ • v
  have hvne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    exact inv_mul_cancel₀ hvne
  refine ⟨Tube.ofMidpointDirection 1 (0 : E) u hu, ?_⟩
  refine Tube.closedBall_subset_carrier_of_mem_segment (δ := 1)
    (Tube.ofMidpointDirection 1 (0 : E) u hu) ?_
  have hmid : midpoint ℝ (Tube.ofMidpointDirection 1 (0 : E) u hu).x
      (Tube.ofMidpointDirection 1 (0 : E) u hu).y = (0 : E) := by
    rw [Tube.ofMidpointDirection_x, Tube.ofMidpointDirection_y]
    simp [midpoint_eq_smul_add]
  simpa [hmid] using (midpoint_mem_segment (𝕜 := ℝ)
    (Tube.ofMidpointDirection 1 (0 : E) u hu).x
    (Tube.ofMidpointDirection 1 (0 : E) u hu).y)



/-- **Paying for the plank-pigeonhole refinement out of the exponent.**

`Kakeya.ml1Boot.exists_plankDimensions` passes from the family `u'` to a subfamily `u''` and
records the passage as a `Kakeya.ShadedBody.IsCRefinement` at the constant `δ̃ ^ ε''`, where
`ε'' > 0` is a free parameter of that lemma.  The flat-prism dichotomy is then applied to
`u''`, so its conclusion is a `multTildeT`-shaped bound for `u''`, whereas the middle-factor
assembly needs one for `u'`.  This is the transfer.

`Kakeya.ShadedBody.IsCRefinement.mul_multiplicity_le` gives `δ̃ ^ ε'' · μ(u') ≤ μ(u'')`, so the
whole cost of the passage is the single factor `δ̃ ^ (-ε'')`, and it is absorbed by running the
dichotomy at the *raised* exponent `A + ε''` rather than at `A`.  Since `ε''` is free and the
conclusion exponent `A = 10 aλ / ε` is fixed by the statement being proved, that raise is free
as well: `Kakeya.ml1Boot.flatPrism_dichotomy_decoupled` is monotone in its `aLam`, a larger
`aLam` giving a smaller right-hand side.  The bracket is handled separately by
`u''.card ≤ u'.card` and `1 - γ / 2 ≥ 0`.

Stated for bare `Kakeya.ShadedBody`s rather than for shaded tubes, since neither the tube
structure nor the scale plays any role. -/
theorem multiplicity_le_of_cRefinement_rpow {δt : NNReal} (hδt0 : 0 < δt)
    {A γ e : ℝ} (hγ2 : 0 ≤ 1 - γ / 2) {ι : Type*} {u'' u' : Finset ι}
    (T : ι → ShadedBody E) (hsub : u'' ⊆ u')
    (href : ShadedBody.IsCRefinement u'' T u' T ⟨(δt : ℝ) ^ e, by positivity⟩)
    (hmul : ShadedBody.multiplicity u'' T
      ≤ (δt : ENNReal) ^ (A + e) * (δt : ENNReal) ^ (-2 * γ)
        * ((u''.card : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) :
    ShadedBody.multiplicity u' T
      ≤ (δt : ENNReal) ^ A * (δt : ENNReal) ^ (-2 * γ)
        * ((u'.card : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  -- `c` as an ENNReal equals `δt ^ e`.
  have hd0 : δt ≠ 0 := ne_of_gt hδt0
  have hδt_ne_zero : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd0
  have hδt_ne_top : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδt_pos : 0 < (δt : ENNReal) := ENNReal.coe_pos.mpr hδt0
  let c0 : NNReal := ⟨(δt : ℝ) ^ e, by positivity⟩
  have hrc : c0 = δt ^ e := NNReal.coe_injective rfl
  have hrE : (c0 : ENNReal) = (δt : ENNReal) ^ e := by
    rw [hrc]
    exact ENNReal.coe_rpow_of_ne_zero hd0 e
  have hreq : (δt : ENNReal) ^ e ≠ 0 := ne_of_gt (ENNReal.rpow_pos hδt_pos hδt_ne_top)
  have hret : (δt : ENNReal) ^ e ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hδt_ne_zero hδt_ne_top
  -- The refinement gives `δt ^ e · μ(u') ≤ μ(u'')`.
  have href1 : (δt : ENNReal) ^ e * multiplicity u' T ≤ multiplicity u'' T := by
    have h0 : (c0 : ENNReal) * multiplicity u' T ≤ multiplicity u'' T :=
      IsCRefinement.mul_multiplicity_le (s' := u'') (V' := T) (s := u') (V := T) href
    simpa [hrE] using h0
  -- Power identities for re-arranging `((δt)^e)⁻¹ · μ(u'')` into the conclusion.
  have hneg : ((δt : ENNReal) ^ e)⁻¹ = (δt : ENNReal) ^ (-e) :=
    (ENNReal.rpow_neg (δt : ENNReal) e).symm
  have hpow : (δt : ENNReal) ^ (-e) * (δt : ENNReal) ^ (A + e) = (δt : ENNReal) ^ A := by
    rw [← ENNReal.rpow_add (x := (δt : ENNReal)) (-e) (A + e) hδt_ne_zero hδt_ne_top]
    congr 1
    ring
  -- Bracket monotonicity in the index count `u'' ≤ u'`.
  have hbr : ((u''.card : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
      ≤ ((u'.card : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    have hcard : (u''.card : ENNReal) ≤ (u'.card : ENNReal) := by
      exact_mod_cast (Finset.card_le_card hsub)
    have hbase : (u''.card : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)
        ≤ (u'.card : ENNReal) * (δt : ENNReal) ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right (a := (δt : ENNReal) ^ (2 : ℕ)) hcard bot_le
    exact ENNReal.rpow_le_rpow hbase hγ2
  calc
    multiplicity u' T ≤ ((δt : ENNReal) ^ e)⁻¹ * multiplicity u'' T := by
      exact (ENNReal.mul_le_iff_le_inv (r := (δt : ENNReal) ^ e)
        (a := multiplicity u' T) (b := multiplicity u'' T) hreq hret).mp href1
    _ ≤ ((δt : ENNReal) ^ e)⁻¹ * ((δt : ENNReal) ^ (A + e) * (δt : ENNReal) ^ (-2 * γ)
          * ((u''.card : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
          exact mul_le_mul_of_nonneg_left hmul bot_le
    _ = (δt : ENNReal) ^ A * (δt : ENNReal) ^ (-2 * γ)
          * ((u''.card : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          rw [← mul_assoc]
          rw [← mul_assoc]
          rw [hneg]
          rw [hpow]
    _ ≤ (δt : ENNReal) ^ A * (δt : ENNReal) ^ (-2 * γ)
          * ((u'.card : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          exact mul_le_mul_of_nonneg_left hbr bot_le

/-- **The refinement transfer with slack in the exponent.**

`Kakeya.ml1Boot.multiplicity_le_of_cRefinement_rpow` with the hypothesis exponent relaxed from
`A + e` to any `B ≥ A + e`.  The flat-prism dichotomy is run at a *raised* plank-ratio exponent
so that its conclusion has room for the refinement loss, and the raise is not exactly `e`; this
absorbs the difference in one step. -/
theorem multiplicity_le_of_cRefinement_rpow_le {δt : NNReal} (hδt0 : 0 < δt) (hδt1 : δt ≤ 1)
    {A B γ e : ℝ} (hγ2 : 0 ≤ 1 - γ / 2) (hAB : A + e ≤ B)
    {ι : Type*} {u'' u' : Finset ι}
    (T : ι → ShadedBody E) (hsub : u'' ⊆ u')
    (href : ShadedBody.IsCRefinement u'' T u' T ⟨(δt : ℝ) ^ e, by positivity⟩)
    (hmul : ShadedBody.multiplicity u'' T
      ≤ (δt : ENNReal) ^ B * (δt : ENNReal) ^ (-2 * γ)
        * ((u''.card : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) :
    ShadedBody.multiplicity u' T
      ≤ (δt : ENNReal) ^ A * (δt : ENNReal) ^ (-2 * γ)
        * ((u'.card : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  have hδt1E : (δt : ENNReal) ≤ 1 := by exact_mod_cast hδt1
  have hpow : (δt : ENNReal) ^ B ≤ (δt : ENNReal) ^ (A + e) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδt1E hAB
  have hmul' : ShadedBody.multiplicity u'' T
      ≤ (δt : ENNReal) ^ (A + e) * (δt : ENNReal) ^ (-2 * γ)
        * ((u''.card : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    calc
      ShadedBody.multiplicity u'' T
          ≤ (δt : ENNReal) ^ B * (δt : ENNReal) ^ (-2 * γ)
            * ((u''.card : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := hmul
      _ ≤ (δt : ENNReal) ^ (A + e) * (δt : ENNReal) ^ (-2 * γ)
            * ((u''.card : ENNReal) * (δt : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          gcongr
  exact multiplicity_le_of_cRefinement_rpow hδt0 hγ2 T hsub href hmul'

/-- **A `δ̃ ^ (-e)` loss on a `δ̃ ^ (-a)` bound is a `δ̃ ^ (-b)` bound**, whenever `e + a ≤ b`.

The Frostman bookkeeping of the middle-factor assembly: the plank pigeonhole degrades the
Frostman constant of the normalized family by `δ̃ ^ (-ε'')`, and the flat-prism dichotomy is
called at an exponent large enough to swallow that. -/
theorem rpow_neg_mul_le_rpow_neg {δt : NNReal} (hδt0 : 0 < δt) (hδt1 : δt ≤ 1)
    {e a b : ℝ} (hab : e + a ≤ b) {X : ENNReal} (hX : X ≤ (δt : ENNReal) ^ (-a)) :
    (δt : ENNReal) ^ (-e) * X ≤ (δt : ENNReal) ^ (-b) := by
  have hδt_ne_zero : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδt0)
  have hδt_ne_top : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδt1E : (δt : ENNReal) ≤ 1 := by exact_mod_cast hδt1
  calc
    (δt : ENNReal) ^ (-e) * X ≤ (δt : ENNReal) ^ (-e) * (δt : ENNReal) ^ (-a) := by
      exact mul_le_mul_of_nonneg_left hX bot_le
    _ = (δt : ENNReal) ^ (-e + -a) := by
      rw [ENNReal.rpow_add (x := (δt : ENNReal)) (-e) (-a) hδt_ne_zero hδt_ne_top]
    _ = (δt : ENNReal) ^ (-(e + a)) := by
      congr 1
      ring
    _ ≤ (δt : ENNReal) ^ (-b) := ENNReal.rpow_le_rpow_of_exponent_ge hδt1E
      (by linarith : -b ≤ -(e + a))

/-- **Fullness under a `c`-refinement**, at a general ambient space.

`Kakeya.Plank.fullness_ge_of_isCRefinement` is this statement, but its ambient space is
hard-coded to `EuclideanSpace ℝ (Fin 3)`, whereas this file works over an abstract `E` carrying
`hdim : Module.finrank ℝ E = 3`.  Nothing in the argument uses the ambient space: a
`c`-refinement raises the shaded mass by `c` and, being supported on a subset, can only lower
the total volume, so the ratio rises by `c`.  This is the general-`E` restatement.

It is what converts the fullness hypothesis of the middle-factor assembly, which is stated for
the normalized family `u'`, into the fullness hypothesis that
`Kakeya.ml1Boot.flatPrism_dichotomy_decoupled` reads on the plank-pigeonhole subfamily `u''`
produced by `Kakeya.ml1Boot.exists_plankDimensions`. -/
theorem fullness_ge_of_cRefinement {ι : Type*} {s' s : Finset ι} {V' V : ι → ShadedBody E}
    {c : NNReal} (h : ShadedBody.IsCRefinement s' V' s V c) :
    c * ShadedBody.fullness s V ≤ ShadedBody.fullness s' V' := by
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ShadedBody.coe_fullness s V,
    ShadedBody.coe_fullness s' V']
  dsimp [ShadedBody.fullness']
  rcases h with ⟨⟨hsub, hbody⟩, hmass⟩
  have hDS' : ∑ i ∈ s', volume (V' i).carrier ≤ ∑ i ∈ s, volume (V i).carrier := by
    calc
      ∑ i ∈ s', volume (V' i).carrier = ∑ i ∈ s', volume (V i).carrier := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [congrArg (fun (cb : ConvexSpaceBody E) =>
          volume (ConvexSpaceBody.carrier cb)) (hbody i hi).1]
      _ ≤ ∑ i ∈ s, volume (V i).carrier := Finset.sum_le_sum_of_subset hsub
  calc
    (c : ENNReal) * ((∑ i ∈ s, volume (V i).shade) / ∑ i ∈ s, volume (V i).carrier)
        = ((c : ENNReal) * ∑ i ∈ s, volume (V i).shade) / ∑ i ∈ s, volume (V i).carrier := by
      rw [mul_div_assoc]
    _ ≤ (∑ i ∈ s', volume (V' i).shade) / ∑ i ∈ s, volume (V i).carrier :=
      ENNReal.div_le_div_right hmass (∑ i ∈ s, volume (V i).carrier)
    _ ≤ (∑ i ∈ s', volume (V' i).shade) / ∑ i ∈ s', volume (V' i).carrier :=
      ENNReal.div_le_div_left hDS' (∑ i ∈ s', volume (V' i).shade)

/-- **Fullness at a prescribed exponent survives a `δ̃ ^ e`-refinement.**

`Kakeya.ml1Boot.fullness_ge_of_cRefinement` in the form the assembly uses: the fullness
hypothesis is carried at the exponent `f` of the family `s`, and it is re-read on the refined
family `s'` at any exponent `g ≥ e + f`.  The two consumers are the fullness clauses of
`Kakeya.ml1Boot.flatPrism_dichotomy_decoupled` and of
`Kakeya.ml1Boot.multTildeT_of_planksClose`, each at its own handed-out threshold, which is why
`g` is a separate binder rather than `e + f`. -/
theorem fullness_ge_rpow_of_cRefinement {δt : NNReal} (hδt0 : 0 < δt) (hδt1 : δt ≤ 1)
    {e f g : ℝ} (hg : e + f ≤ g) {ι : Type*} {s' s : Finset ι} (T : ι → ShadedBody E)
    (href : ShadedBody.IsCRefinement s' T s T ⟨(δt : ℝ) ^ e, by positivity⟩)
    (hfull : (δt : ENNReal) ^ f ≤ ShadedBody.fullness s T) :
    (δt : ENNReal) ^ g ≤ ShadedBody.fullness s' T := by
  have hd0 : δt ≠ 0 := ne_of_gt hδt0
  have hδt_ne_zero : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd0
  have hδt_ne_top : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδt1E : (δt : ENNReal) ≤ 1 := by exact_mod_cast hδt1
  let c0 : NNReal := ⟨(δt : ℝ) ^ e, by positivity⟩
  have hrc : c0 = δt ^ e := NNReal.coe_injective rfl
  have hrE : (c0 : ENNReal) = (δt : ENNReal) ^ e := by
    rw [hrc]
    exact ENNReal.coe_rpow_of_ne_zero hd0 e
  have hfin : (c0 : ENNReal) * (ShadedBody.fullness s T : ENNReal) ≤
      (ShadedBody.fullness s' T : ENNReal) := by
    have h0 : c0 * ShadedBody.fullness s T ≤ ShadedBody.fullness s' T :=
      fullness_ge_of_cRefinement (V' := T) (s := s) (V := T) (c := c0) href
    rw [← ENNReal.coe_mul]
    exact ENNReal.coe_le_coe.mpr h0
  calc
    (δt : ENNReal) ^ g ≤ (δt : ENNReal) ^ (e + f) := ENNReal.rpow_le_rpow_of_exponent_ge hδt1E hg
    _ = (δt : ENNReal) ^ e * (δt : ENNReal) ^ f := by
      rw [ENNReal.rpow_add (x := (δt : ENNReal)) e f hδt_ne_zero hδt_ne_top]
    _ ≤ (δt : ENNReal) ^ e * (ShadedBody.fullness s T : ENNReal) := by
      exact mul_le_mul_of_nonneg_left hfull bot_le
    _ = (c0 : ENNReal) * (ShadedBody.fullness s T : ENNReal) := by
      rw [← hrE]
    _ ≤ (ShadedBody.fullness s' T : ENNReal) := hfin

/-- **A mass refinement is a cardinality refinement, up to the incoming fullness**, at a general
ambient space.

`Kakeya.card_le_of_isCRefinement_of_fullness` is this statement, but its ambient space is
hard-coded to `EuclideanSpace ℝ (Fin 3)` and it lives under `Kakeya.DimensionThree.Plank`, which
no file of `MainLemma1` imports.  Nothing in the argument uses the ambient space: the chain is
`c · lam · |s| · v ≤ c · ∑_s |Y| ≤ ∑_{s'} |Y'| ≤ |s'| · v`, whose three steps are
`ShadedBody.coe_fullness_mul_le_sum_volume_shade`, the mass clause of the refinement, and
`Finset.sum_le_sum`, all of them already general in `E`.  This is the general-`E` restatement.

The factor `lam` is not an artefact: the middle inequality is the only information available
about `s'`, and a family of `|s'|` bodies of carrier volume `v` carries mass at most `|s'| · v`,
attained when the retained family is full. -/
theorem card_le_of_cRefinement_of_fullness {ι : Type*} {s' s : Finset ι}
    {V' V : ι → ShadedBody E} {c lam : NNReal} {v : ENNReal} (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (href : ShadedBody.IsCRefinement s' V' s V c)
    (hlam : lam ≤ ShadedBody.fullness s V)
    (hVlow : ∀ i ∈ s, v ≤ volume (V i).carrier)
    (hV'up : ∀ i ∈ s', volume (V' i).shade ≤ v) :
    (c * lam) * (s.card : NNReal) ≤ (s'.card : NNReal) := by
  have key : v * (((c * lam : NNReal) : ENNReal) * (s.card : ENNReal)) ≤ v * (s'.card : ENNReal) :=
    calc v * (((c * lam : NNReal) : ENNReal) * (s.card : ENNReal))
        = (c : ENNReal) * ((lam : ENNReal) * ((s.card : ENNReal) * v)) := by
          rw [ENNReal.coe_mul]
          ac_rfl
      _ ≤ (c : ENNReal) * ∑ i ∈ s, volume (V i).shade :=
        mul_le_mul_right (ShadedBody.coe_fullness_mul_le_sum_volume_shade s V hlam hVlow) _
      _ ≤ ∑ i ∈ s', volume (V' i).shade := href.2
      _ ≤ v * (s'.card : ENNReal) := by simpa [mul_comm] using Finset.sum_le_sum hV'up
  exact_mod_cast (ENNReal.mul_le_mul_iff_right hv0 hvtop).mp key

/-- **The cardinality share of a refinement of a one-scale tube family.**

`Kakeya.ml1Boot.card_le_of_cRefinement_of_fullness` at the shape this file uses: the members are
`δ̃`-tubes at one common scale, so the common carrier volume `v` that lemma cancels may be named
by any one of them (`Tube.volume_carrier_eq_volume_carrier`, which asks nothing at all) and is
positive and finite by `Tube.volume_pos_and_lt_top`.  The refinement constant `δ̃ ^ e` and the
incoming fullness `δ̃ ^ f` multiply, so the retained cardinality share is `δ̃ ^ (e + f)`.

Separated from `Kakeya.ml1Boot.frostmanConstIn_le_of_cRefinement_of_fullness` because it is the
whole of the `NNReal`/`ENNReal` coercion bookkeeping and none of the Frostman argument. -/
theorem rpow_mul_card_le_card_of_cRefinement_of_fullness [Nontrivial E] {δt : NNReal}
    (hδt0 : 0 < δt) (hδt1 : δt ≤ 1) {e f : ℝ}
    {ι : Type*} {u'' u' : Finset ι} (Ttil : ι → ShadedTube δt E) (hne : u'.Nonempty)
    (href : ShadedBody.IsCRefinement u'' (fun k => (Ttil k).toShadedBody) u'
      (fun k => (Ttil k).toShadedBody) ⟨(δt : ℝ) ^ e, by positivity⟩)
    (hfull : (δt : ENNReal) ^ f ≤ ShadedBody.fullness u' (fun k => (Ttil k).toShadedBody)) :
    (δt : ENNReal) ^ (e + f) * (u'.card : ENNReal) ≤ (u''.card : ENNReal) := by
  classical
  obtain ⟨k0, hk⟩ := hne
  let vv : ENNReal := volume ((Ttil k0).toTube).carrier
  have hv0 : vv ≠ 0 := by
    simpa [vv] using (Tube.volume_pos_and_lt_top (σ := δt) hδt0 hδt1 ((Ttil k0).toTube)).1.ne'
  have hvT : vv ≠ ⊤ := by
    simpa [vv] using (Tube.volume_pos_and_lt_top (σ := δt) hδt0 hδt1 ((Ttil k0).toTube)).2.ne
  let c0 : NNReal := ⟨(δt : ℝ) ^ e, by positivity⟩
  let lam : NNReal := δt ^ f
  have hzero : δt ≠ 0 := ne_of_gt hδt0
  have hze : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hzero
  have htop : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hEq : ∀ i, vv = volume ((Ttil i).toShadedBody).carrier := by
    intro i
    dsimp [vv]
    simpa using (Tube.volume_carrier_eq_volume_carrier ((Ttil k0).toTube) ((Ttil i).toTube))
  have hVlow : ∀ i ∈ u', vv ≤ volume ((Ttil i).toShadedBody).carrier := by
    intro i hi
    exact le_of_eq (hEq i)
  have hVup : ∀ i ∈ u'', volume ((Ttil i).toShadedBody).shade ≤ vv := by
    intro i hi
    calc
      volume ((Ttil i).toShadedBody).shade ≤ volume ((Ttil i).toShadedBody).carrier :=
        measure_mono (Ttil i).toShadedBody.shade_subset
      _ = vv := (hEq i).symm
  have hlamFull : lam ≤ ShadedBody.fullness u' (fun k => (Ttil k).toShadedBody) := by
    dsimp [lam]
    exact ENNReal.coe_le_coe.mp (by
      simpa [← ENNReal.coe_rpow_of_ne_zero hzero f] using hfull)
  have hCardNN : (c0 * lam) * (u'.card : NNReal) ≤ (u''.card : NNReal) :=
    card_le_of_cRefinement_of_fullness (s := u') (s' := u'')
      (V := fun i => (Ttil i).toShadedBody) (V' := fun i => (Ttil i).toShadedBody)
      (c := c0) (lam := lam) (v := vv) hv0 hvT href hlamFull hVlow hVup
  have hcN : c0 = δt ^ e := by
    dsimp [c0]
    exact NNReal.coe_injective rfl
  have hcE : (c0 : ENNReal) = (δt : ENNReal) ^ e := by
    rw [hcN]
    exact ENNReal.coe_rpow_of_ne_zero hzero e
  have hlE : (lam : ENNReal) = (δt : ENNReal) ^ f := by
    exact ENNReal.coe_rpow_of_ne_zero hzero f
  have hPowAdd : ((δt : ENNReal) ^ (e + f)) = ((c0 * lam : NNReal) : ENNReal) := by
    rw [ENNReal.coe_mul, hcE, hlE]
    rw [ENNReal.rpow_add e f hze htop]
  rw [hPowAdd]
  exact_mod_cast hCardNN

/-- **The Frostman constant of a refinement of a one-scale tube family**, at the refinement's own
loss.

This is the Frostman half of `Kakeya.ml1Boot.exists_plankDimensions_uniform`, isolated from the
selection.  `Kakeya.frostmanConstIn` is not monotone in the index set, and the only
ambient-to-subfamily transport `ConvexSpaceBody.IsFrostmanIn.of_subset` charges a *volume*
retention ratio, which `Kakeya.ShadedBody.IsCRefinement` does not supply — it retains shaded
mass, not volume.  Two facts close that gap for a family carried at one common scale:

* same-scale tubes have *exactly equal* carrier volume
  (`Tube.volume_carrier_eq_volume_carrier`), so a volume share is a cardinality share at the
  same factor, with nothing lost — this is what
  `ConvexSpaceBody.frostmanConstIn_subfamily_le` consumes;
* `Kakeya.ml1Boot.card_le_of_cRefinement_of_fullness` converts the mass share of the refinement
  into that cardinality share, at the price of one factor of the incoming fullness.

Hence the two exponents: the refinement's `e` and the fullness's `f` are *both* paid, and the
conclusion is read at any `g ≥ e + f`.  A consumer that wants the loss `δ̃ ^ (-ε'')` therefore
runs the refinement at `ε'' / 2` and needs the fullness at `ε'' / 2` as well.

Nonemptiness of `u''` comes free from the same cardinality bound: `|u'| ≥ 1` and the factor
`δ̃ ^ e · δ̃ ^ f > 0` force `|u''| > 0`.  It is returned here rather than assumed because no
hypothesis of the selection gives it. -/
theorem frostmanConstIn_le_of_cRefinement_of_fullness [Nontrivial E] {δt : NNReal}
    (hδt0 : 0 < δt) (hδt1 : δt ≤ 1) {e f g : ℝ} (hg : e + f ≤ g)
    {ι : Type*} {u'' u' : Finset ι} (Ttil : ι → ShadedTube δt E)
    (hne : u'.Nonempty) (hsub : u'' ⊆ u')
    (hball : ∀ k ∈ u', (Ttil k).carrier ⊆ Metric.closedBall 0 1)
    (href : ShadedBody.IsCRefinement u'' (fun k => (Ttil k).toShadedBody) u'
      (fun k => (Ttil k).toShadedBody) ⟨(δt : ℝ) ^ e, by positivity⟩)
    (hfull : (δt : ENNReal) ^ f ≤ ShadedBody.fullness u' (fun k => (Ttil k).toShadedBody)) :
    u''.Nonempty ∧
      frostmanConstIn u'' (fun k => (Ttil k).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall
        ≤ (δt : ENNReal) ^ (-g) * frostmanConstIn u' (fun k => (Ttil k).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall := by
  classical
  have hcard : (δt : ENNReal) ^ (e + f) * (u'.card : ENNReal) ≤ (u''.card : ENNReal) :=
    rpow_mul_card_le_card_of_cRefinement_of_fullness hδt0 hδt1 Ttil hne href hfull
  have hpos : 0 < (δt : ENNReal) := ENNReal.coe_pos.mpr hδt0
  have htop : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1e : (δt : ENNReal) ≤ 1 := by exact_mod_cast hδt1
  refine ⟨?_, ?_⟩
  · have hPowPos : 0 < (δt : ENNReal) ^ (e + f) := ENNReal.rpow_pos hpos htop
    have hcardPos : (0 : ENNReal) < (u'.card : ENNReal) := by
      exact_mod_cast Finset.card_pos.mpr hne
    have hprod : 0 < (δt : ENNReal) ^ (e + f) * (u'.card : ENNReal) :=
      ENNReal.mul_pos (ne_of_gt hPowPos) (ne_of_gt hcardPos)
    have hpos' : 0 < (u''.card : ENNReal) := lt_of_lt_of_le hprod hcard
    exact Finset.card_pos.mp (by exact_mod_cast hpos')
  · rw [ENNReal.rpow_neg]
    rcases hne with ⟨k0, hk0⟩
    let vv : ENNReal := volume ((Ttil k0).toTube).carrier
    have hEq : ∀ k, vv = volume ((Ttil k).toShadedBody).carrier := by
      intro k
      dsimp [vv]
      simpa using (Tube.volume_carrier_eq_volume_carrier ((Ttil k0).toTube) ((Ttil k).toTube))
    have hVol : ∀ k ∈ u', volume ((Ttil k).toConvexSpaceBody).carrier = vv := by
      intro k hk
      simpa using (hEq k).symm
    have hBall : ∀ k ∈ u', (Ttil k).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall := by
      intro k hk
      exact SetLike.coe_subset_coe.mpr (hball k hk)
    have hKappa : (δt : ENNReal) ^ g ≠ 0 := ne_of_gt (ENNReal.rpow_pos hpos htop)
    have hgexp : (δt : ENNReal) ^ g ≤ (δt : ENNReal) ^ (e + f) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδ1e hg
    have hCard2 : (δt : ENNReal) ^ g * (u'.card : ENNReal) ≤ (u''.card : ENNReal) := by
      calc
        (δt : ENNReal) ^ g * (u'.card : ENNReal) ≤
            (δt : ENNReal) ^ (e + f) * (u'.card : ENNReal) := by
              gcongr
        _ ≤ (u''.card : ENNReal) := hcard
    exact frostmanConstIn_subfamily_le (s := u') (s' := u'')
      (W := fun i => (Ttil i).toConvexSpaceBody) (K := ConvexSpaceBody.closedUnitBall)
      (v := vv) (hs := ⟨k0, hk0⟩) (hvol := hVol) (hWK := hBall) (hs' := hsub)
      (hκ := hKappa) (hcard := hCard2)

/-! ### The plank conclusion is preserved by keeping whole parts

The plank clause of `Kakeya.ml1Boot.exists_plankDimensions_uniformSelection` asks, for every
parent `m`, for a `ConvexSpaceBody.Factorization` of the *whole* fibre `fibre u'' pρ m` all of
whose parts are `ap × bp × 1` planks.  Which selections that clause survives is therefore a
question about the atoms of the factorization, and the answer is that the atom is the **part**:

* keeping a sub-collection of whole parts is free — `ConvexSpaceBody.Factorization.ofSubsetParts`
  for the factorization and `Kakeya.ml1Boot.isPlankFamilyOfDimensions_subset` for the plank
  dimensions, packaged as `Kakeya.ml1Boot.exists_plankFactorization_of_subsetParts`;
* discarding a whole fibre is free — `Kakeya.ml1Boot.exists_plankFactorization_of_eq_empty`;
* dropping members *inside* a part is not free, and no lemma here does it: the part's hull
  shrinks, and `Kakeya.IsPlankOfDimensions` is two-sided (`Kakeya/Factoring/FlatPrisms.lean`),
  so the lower bounds `C⁻¹ ≤ τ₀`, `C⁻¹ b ≤ τ₁`, `C⁻¹ a ≤ τ₂` are the ones that fail.

`Kakeya.ml1Boot.isPlankFamilyOfDimensions_subset` is a general fact about
`Kakeya.IsPlankFamilyOfDimensions` and belongs beside its definition in
`Kakeya/Factoring/FlatPrisms.lean`; it is stated here because that file is not open for this
round.
-/

/-- **Plank dimensions are inherited by a sub-collection of the family.**
`Kakeya.IsPlankFamilyOfDimensions` is `∀ i ∈ s, Kakeya.IsPlankOfDimensions C a b (W i)`, a
per-member condition, so it restricts along `P ⊆ Q` with the same `C`, `a`, `b`. -/
theorem isPlankFamilyOfDimensions_subset {κ : Type*} {C a b : NNReal} {P Q : Finset κ}
    (hPQ : P ⊆ Q) {W : κ → ConvexSpaceBody E}
    (h : IsPlankFamilyOfDimensions C a b Q W) : IsPlankFamilyOfDimensions C a b P W := by
  intro i hi
  exact h i (hPQ hi)

/-- **Keeping whole parts preserves the plank clause**, in the shape the plank clause of
`Kakeya.ml1Boot.exists_plankDimensions_uniformSelection` is stated in: from a factorization of
`f` into `ap × bp × 1` planks and a sub-collection `P` of its parts with union `f'`, the same
data at `f'`, with `parts = P` and the *same* dimensions `ap`, `bp` and constant `C`.

Nothing is lost and nothing is re-chosen: the retained parts and their hulls are literally the
old ones.  This is the lemma a class-compatible or mass-compatible re-selection would consume,
and it is the reason such a re-selection must be formulated on parts. -/
theorem exists_plankFactorization_of_subsetParts {ι : Type*} [DecidableEq ι] {δt : NNReal}
    (T : ι → ShadedTube δt E) {C ap bp : NNReal} {f : Finset ι}
    (F : ConvexSpaceBody.Factorization f (fun i => (T i).toConvexSpaceBody) 2)
    (hplank : IsPlankFamilyOfDimensions C ap bp F.parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {P : Finset (Finset ι)} (hP : P ⊆ F.parts) {f' : Finset ι} (hf' : P.sup id = f') :
    ∃ F' : ConvexSpaceBody.Factorization f' (fun i => (T i).toConvexSpaceBody) 2,
      F'.parts = P ∧
        IsPlankFamilyOfDimensions C ap bp F'.parts
          (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)) := by
  refine ⟨ConvexSpaceBody.Factorization.ofSubsetParts F hP hf', by simp, ?_⟩
  simpa using (isPlankFamilyOfDimensions_subset hP hplank)

/-- **Discarding a whole fibre is free**, in the shape the plank clause is stated in: an empty
fibre carries a factorization whose plank requirement is vacuous.  So a selection may filter the
parent set `tρ` at no cost, and needs no separate hypothesis for the parents it drops. -/
theorem exists_plankFactorization_of_eq_empty {ι : Type*} [DecidableEq ι] {δt : NNReal}
    (T : ι → ShadedTube δt E) (C ap bp : NNReal) {f : Finset ι} (hf : f = ∅) :
    ∃ F : ConvexSpaceBody.Factorization f (fun i => (T i).toConvexSpaceBody) 2,
      IsPlankFamilyOfDimensions C ap bp F.parts
        (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)) := by
  rcases ConvexSpaceBody.exists_factorization_of_eq_empty (V := fun i => (T i).toConvexSpaceBody)
      hf 2 with ⟨F, hFparts⟩
  exact ⟨F, by
    intro part hpart
    exact False.elim (by simpa [hFparts] using hpart)⟩

/-- **The plank pigeonhole with the uniformity of the family retained** — the selection half of
`Kakeya.ml1Boot.exists_plankDimensions_uniform`, and the one clause of it that is still owed.

This is `Kakeya.ml1Boot.exists_plankDimensions_uniform` with its Frostman *conclusion* clause
deleted and its fullness *hypothesis* deleted, and nothing else changed: the same `Cu` handed
out before `ε''`, and the same subfamily `u''` carrying nonemptiness, *one-sided* uniformity at
`Cu`, the `δ̃ ^ ε''`-refinement and the common plank dimensions.

`Kakeya.ml1Boot.exists_plankDimensions_uniform` invokes this statement at `ε'' / 2`, weakens
the `δ̃ ^ (ε'' / 2)`-refinement it returns to the `δ̃ ^ ε''` the conclusion asks for, and derives
the Frostman clause from that *unweakened* `δ̃ ^ (ε'' / 2)`-refinement together with the fullness
hypothesis, by `Kakeya.ml1Boot.frostmanConstIn_le_of_cRefinement_of_fullness`.

**The uniformity clause is the one-sided predicate, and that is what makes this provable.**
Blueprint item (B1) of `lem:ml1bootMiddleFactor` records the obstruction to the *two-sided*
clause: `IsOneSidedUniform` is two-sided, and restricting the index set shrinks
every `ShadedTube.shadeClass` (`Tube.coverClass_subset_of_subset`), so the *lower* brackets
`le_card_shadeClass` and `branchingN_le` do not descend — a class of `u'` may retain a single
member while the refinement's mass is retained elsewhere, and no constant depending only on
`Cunif` repairs that for a general subfamily.  The two-sided form at the prescribed `u''` is
therefore **not recoverable at any constant**, and it is no longer asked for: the clause below
is `Kakeya.IsFlatPrismUniform`, the half of GWZ Definition 2.2 that keeps `card_shadeClass_le`
and `le_branchingN` and drops the two lower brackets.

That half restricts to an *arbitrary* subfamily at the same constant and with no pigeonholing
(`Kakeya.IsFlatPrismUniform.mono_index`), and every two-sided hierarchy projects onto it
(`Kakeya.IsFlatPrismUniform.of_shadedUniformTubeSet`), so the whole clause is discharged by the
composite `Kakeya.IsFlatPrismUniform.of_shadedUniformTubeSet_subset` applied to the incoming
two-sided hypothesis at `u'` and the inclusion `u'' ⊆ u'` that the selection returns.  The
constant is `Cu = max 1 Cunif`, which makes `1 ≤ Cu` free — the incoming `Cunif` carries no
lower bound and none is assumed — and the incoming hierarchy is weakened to it by
`IsOneSidedUniform.mono` before the projection.  The side condition
`Cu ≤ δ̃ ^ (-ηu)` is what the `∀ᶠ δ̃ in 𝓝[>] 0` prefix is for: `Cunif` is fixed before the
filter and `ηu > 0`, so `Kakeya.ml1Boot.const_le_rpow_neg` absorbs it, at the explicit threshold
`δ̃ ≤ Cu ^ (-1 / ηu)` that it exhibits — no limiting argument is needed, only one more
`nhdsWithin_le_nhds (Iio_mem_nhds …)` in the `filter_upwards` list.

Everything else — `u'' ⊆ u'`, `u''.Nonempty`, the refinement and the per-parent plank
factorizations — is a single citation of `Kakeya.ml1Boot.exists_plankDimensions` at
`ρ := δ̃ ^ (6 ε)`, whose `ρ ∈ [δ̃, 1]` binder is discharged from `11 ε ≤ 1` and `δ̃ ≤ 1`.  Its
`F` is a *total* function of the parent, so the per-`m` `∃ F` is an application.

**This is a restatement, not a weakening of any definition.**  Neither
`IsOneSidedUniform` nor `Kakeya.IsPlankOfDimensions` changed, and no hypothesis
was added here.  What changed is which of the two uniformity predicates the conclusion carries,
and the consumer chain moved with it: `Kakeya.ml1Boot.flatPrism_dichotomy_decoupled` and
`Kakeya.ml1Boot.multTildeT_of_planksClose` now hypothesise the one-sided form, which is all
either ever used — the dichotomy packs it straight into `Kakeya.IsFlatPrismFamily.unif` and
reads no bracket.

**The debt is moved, not eliminated.**  `Kakeya.IsFlatPrismFamily.unif` is now the one-sided
predicate, so `Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'` — the conditional
Section 6 interface for GWZ Proposition 6.6(A) — receives a strictly weaker hypothesis and is
therefore a strictly stronger statement, harder for Section 6 to discharge. Its docstring
carries that record. The bookkeeping is worth stating precisely, because it is easy to overclaim:
this statement's own axiom closure is `[propext, Classical.choice, Quot.sound]` — clean, no
`sorryAx` — and so is that of `Kakeya.ml1Boot.exists_plankDimensions_uniform` above it. But its
consumer `Kakeya.ml1Boot.flatPrism_dichotomy_decoupled` closes over `sorryAx`, through
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'` and not through anything here, and every
Section-8 result downstream of the dichotomy inherits that. So Section 8 no longer owes a proof;
it still cannot be run unconditionally.

**This contradicts a standing blueprint verdict, deliberately and on the record.**  Item (1) of
blueprint `note:ml1bootPlanksCloseNeedsWhichBracket` says *do not* weaken this conclusion, on the
ground that the field `Kakeya.IsFlatPrismFamily.unif` is consumed only by
`prop:ml1bootFlatPrismsCorrected`, which has no proof, so "whether one-sided brackets suffice
there is not a question this development can answer today" — a weakening can only be assumed, not
certified. That reading of the cost is accepted here in full; what is rejected is the conclusion
that the leaf should therefore keep an unprovable clause. The trade made instead is
explicit: Section 8 is closed and Section 6's interface is strictly harder. The blueprint note
has not been updated to match — no `.tex` was touched — so it and this docstring disagree until a
human reconciles them. Item (3) of the same verdict, which calls weakening the uniformity
hypothesis of `Kakeya.ml1Boot.multTildeT_of_planksClose` a *strengthening* of that statement, is
consistent with what was done there.

**The route not taken, W3: align `pρ` to a grid scale.**  Whole-class retention does preserve
both lower brackets verbatim, at the same constant and branching function
(`Kakeya.ml1Boot.coverClass_filter_mem`); what blocks it here is that the parent map `pρ`
delivered by `Kakeya.ml1Boot.exists_parentFamily_atSixEps` is built from the pointwise
`ρ`-tubes of the lower Frostman hypothesis and is tied to no
`Tube.GridCoverSystem.assign` at any index.  W3 is to build the parent family *at a
grid index* instead: round the plank scale `ρ = δ̃ ^ (6 ε)` to the nearest scale `ρ_k` of
`Tube.ssfGridLen δ̃`, run the pigeonhole against the level-`k` nodes, and keep whole
classes at that level, so that `Kakeya.ml1Boot.coverClass_filter_mem` applies.

**W3 is not available inside this statement, and the rounding lemma is not a prerequisite of
it.**  `pρ` is a *binder* here, handed in together with `Kakeya.ml1Boot.IsParentFamily` and the
surjectivity, so nothing in a proof of this statement may re-choose it and no rounding is
applicable.  W3 is a change to the *caller's* interface — the parent family would have to be
built grid-aligned where it is constructed, in
`Kakeya.ml1Boot.exists_parentFamily_atSixEps` — so the absence of any `exists_gridScale_ge` on
this branch does not block this declaration.  Even carried out there, W3 leaves the *coarse*
levels `k < k₀` owed: `Tube.GridCoverSystem.nested` makes classes finer as `k` grows, so
a union of whole level-`k₀` classes is whole at every finer level and only partially retained at
coarser ones, and whole-class retention at every level would mean it at `k = 0`, where `ρ₀ = 1`.

**What a selection may keep or drop is settled, and the atom is the plank part.**
`Kakeya.ml1Boot.exists_plankFactorization_of_subsetParts` and
`Kakeya.ml1Boot.exists_plankFactorization_of_eq_empty` above, resting on
`ConvexSpaceBody.Factorization.ofSubsetParts` and
`ConvexSpaceBody.exists_factorization_of_eq_empty`, say that keeping a sub-collection of whole
parts and discarding whole fibres both preserve the plank clause verbatim, at the same `ap`,
`bp` and constant.  Dropping members *inside* a part does not: the part's hull shrinks and
`Kakeya.IsPlankOfDimensions` is two-sided.  So the granularities available to a selection are
the part and the fibre — and *not* the cover class.

**The dyadic-banding route is unvetted, and is deliberately not stated.**  Banding the per-class
retention ratio and keeping the heaviest band would give the two-sided share the lower brackets
want, but the shape that keeps whole *parts* (the only plank-safe shape) leaves classes
partially retained at every level: parts do not align with classes, since at levels finer than
the plank a part splits across many nodes and at coarser levels nothing forces two members of
one plank to share a node, `Tube.GridCoverSystem.assign` being an arbitrary function
subject only to containment, nesting and bounded overlap.  Two sharper facts are worth
recording.  `Tube.UniformTubeSet.le_card_class` is *shade-free* — it compares
`branchingN` with a `Tube.coverClass` cardinality — so shrinking shadings cannot repair
it, and the binding constraint sits at the tube level, before any point enters; and the
*pointwise* form of the shaded brackets is **not** the obstruction it was recorded as, because
dropping a member also removes its shade from the `∀ x ∈ ⋃ shade` domain.

**The input hypothesis is one-sided too.**  It used to be the two-sided
`ShadedTube.ShadedUniformTubeSet`, which made this statement strictly weaker than it now is: the
only use the proof makes of it is to weaken its constant and restrict it to the retained `u''`, and
both steps go through for `Kakeya.IsFlatPrismUniform` — `Kakeya.IsFlatPrismUniform.mono` and
`Kakeya.IsFlatPrismUniform.mono_index`, in place of `ShadedTube.ShadedUniformTubeSet.mono` followed
by `Kakeya.IsFlatPrismUniform.of_shadedUniformTubeSet_subset`.  The reason to match the two sides is
the chain above: this is where the fibre hierarchy handed down from
`Kakeya.ml1Boot.IsFactorTwoScales.midFibreUnif` finally lands, and that field is one-sided.

**What the two-sided clause would have needed, and why it is not merely a missing proof.**  It
would need a producer of `IsOneSidedUniform` on a *prescribed* index set with the
*original* shadings. A prescribed-subfamily producer would have to be false in general, by the
single-member-class mechanism recorded above. That is why the clause was restated rather than
proved, and why blueprint `note:ml1bootMiddleFactorGaps`(B1) does not owe Section 2 a shape of
it. -/
theorem exists_plankDimensions_uniformSelection (hdim : Module.finrank ℝ E = 3)
    {ε : ℝ} (hε0 : 0 < ε) (hε11 : 11 * ε ≤ 1) (Cunif : NNReal) :
    ∀ ηu > (0 : ℝ), ∀ ε'' > (0 : ℝ),
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {u' tρ : Finset ι}
        (Ttil : ι → ShadedTube δt E) (Tρ : ι → Tube (δt ^ (6 * ε)) E) (pρ : ι → ι),
        u'.Nonempty →
        IsFlatPrismUniform u' Ttil (Tube.ssfGridLen δt) Cunif →
        (∀ k ∈ u', (Ttil k).carrier ⊆ Metric.closedBall 0 1) →
        (u' : Set ι).Pairwise
          (fun k k' => IsEssentiallyDistinct (Ttil k).carrier (Ttil k').carrier) →
        IsParentFamily u' (fun k => (Ttil k).toTube) tρ Tρ pρ →
        Set.SurjOn pρ ↑u' ↑tρ →
        ∃ u'' ⊆ u', u''.Nonempty ∧
          (∃ Cu : NNReal, 1 ≤ Cu ∧ (Cu : ENNReal) ≤ (δt : ENNReal) ^ (-ηu) ∧
            Nonempty (IsFlatPrismUniform u'' Ttil (Tube.ssfGridLen δt) Cu)) ∧
          ShadedBody.IsCRefinement u'' (fun k => (Ttil k).toShadedBody) u'
            (fun k => (Ttil k).toShadedBody) ⟨(δt : ℝ) ^ ε'', by positivity⟩ ∧
          ∃ ap bp : NNReal, δt ≤ ap ∧ ap ≤ bp ∧ bp ≤ δt ^ (6 * ε) ∧
            ∀ m ∈ tρ, ∃ F : ConvexSpaceBody.Factorization (fibre u'' pρ m)
                (fun i => (Ttil i).toConvexSpaceBody) 2,
              IsPlankFamilyOfDimensions plankPigeonhole.C ap bp F.parts
                (fun part =>
                  part.convexHull_biUnion (fun i => (Ttil i).toConvexSpaceBody)) := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by
    rw [hdim]; norm_num : 0 < Module.finrank ℝ E)
  intro ηu hηu ε'' hε''0
  have hsel := exists_plankDimensions hdim hε''0
  let C : ENNReal := ((max 1 Cunif : NNReal) : ENNReal)
  have hC1 : 1 ≤ C := by
    dsimp [C]
    exact ENNReal.coe_le_coe.mpr (le_max_left 1 Cunif)
  have hCtop : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.coe_ne_top
  have hCpos : (0 : ENNReal) < C := zero_lt_one.trans_le hC1
  have htop : C ^ (-1 / ηu) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg' hCpos hCtop
  have hδ₁ : (0 : NNReal) < min 1 (C ^ (-1 / ηu)).toNNReal :=
    lt_min zero_lt_one (by
      rw [← ENNReal.coe_pos, ENNReal.coe_toNNReal htop]
      exact ENNReal.rpow_pos hCpos hCtop)
  filter_upwards [hsel, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num)),
      nhdsWithin_le_nhds (Iio_mem_nhds hδ₁)]
    with δt hsel' hδt0 hδtlt1 hδtlt2
  have hδt1 : δt ≤ 1 := le_of_lt hδtlt1
  have hρ1 : δt ^ (6 * ε) ≤ 1 := NNReal.rpow_le_one hδt1 (by linarith)
  have hδρ : δt ≤ δt ^ (6 * ε) := by
    simpa using (NNReal.rpow_le_rpow_of_exponent_ge hδt0 hδt1 (by linarith : 6 * ε ≤ 1))
  have hδtC : (δt : ENNReal) ≤ C ^ (-1 / ηu) := by
    calc
      (δt : ENNReal) ≤ ((C ^ (-1 / ηu)).toNNReal : ENNReal) :=
        ENNReal.coe_le_coe.mpr (hδtlt2.le.trans (min_le_right _ _))
      _ = C ^ (-1 / ηu) := ENNReal.coe_toNNReal htop
  have hCub : C ≤ (δt : ENNReal) ^ (-ηu) :=
    const_le_rpow_neg hC1 hCtop hηu hδt0 hδtC
  intro ι hdec u' tρ Ttil Tρ pρ hu' hunif hball hED hparent hsurj
  obtain ⟨u'', hu''sub, hu''ne, ap, bp, hδap, hapbp, hbpρ, F, href, hFne, hplank, hvol⟩ :=
    hsel' (ρ := δt ^ (6 * ε)) hδρ hρ1 (ι := ι) (κ := ι) (u := u') (tρ := tρ)
      Ttil Tρ pρ hu' hball hED hparent hsurj
  refine ⟨u'', hu''sub, hu''ne, ⟨max 1 Cunif, le_max_left _ _, hCub,
    ⟨IsFlatPrismUniform.mono_index
      (hunif.mono (le_max_right 1 Cunif)) hu''sub⟩⟩,
    href, ap, bp, hδap, hapbp, hbpρ, fun m hm => ⟨F m, hplank m hm⟩⟩

/-- **The plank pigeonhole with the family package retained** (obstructions (8) and (9) of
`Kakeya.ml1Boot.multTildeT_of_rescaledData`).

`Kakeya.ml1Boot.exists_plankDimensions` passes from `u'` to a subfamily `u''` and returns the
plank factorizations of the fibres of `u''`.  Its consumer
`Kakeya.ml1Boot.flatPrism_dichotomy_decoupled` must therefore be run at `u''`, since its plank
hypothesis is read on `fibre u pρ m` for the very family `u` it concludes about.  But the
dichotomy also demands, at `u''`, the uniformity and the Frostman upper bound that the
middle-factor data supplies only at `u'`, and **neither descends**:

* **Uniformity does not restrict.**  (The hypothesis is now stated one-sidedly for this very
  reason; what follows is why the two-sided form could not be carried.)
  `ShadedTube.ShadedUniformTubeSet` is two-sided, and
  restricting the index set shrinks every `ShadedTube.shadeClass`
  (`Tube.coverClass_subset_of_subset`), so exactly the two clauses that bound a *shrinking*
  quantity from below fail: `le_card_shadeClass`, which bounds `localN x k` by the class
  cardinality, and `branchingN_le`, which bounds `branchingN k` by `localN x k`.  A class of
  `u'` may retain a single member in `u''` while the refinement's mass is retained elsewhere,
  and no constant depending only on `Cunif` repairs that.
  `IsOneSidedUniform.mono` weakens the constant with the index set fixed, and
  `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` — which is proved — re-uniformizes but
  chooses *its own* subfamily, so it cannot deliver uniformity at the prescribed `u''`.

  The other two clauses do descend, and for two different reasons: `card_shadeClass_le` because
  it is an upper bound on the shrinking class, and `le_branchingN` because it never mentions the
  index set at all.  **Those two are what the uniformity clause below now asserts**, as
  `Kakeya.IsFlatPrismUniform`, which restricts to an arbitrary subfamily at the same constant
  and with no pigeonholing (`Kakeya.IsFlatPrismUniform.of_shadedUniformTubeSet_subset`).  The
  two-sided form is *not* asserted, and is not recoverable at any constant.  This costs the
  consumer nothing: `Kakeya.ml1Boot.flatPrism_dichotomy_decoupled` asks for uniformity only in
  order to fill the field `Kakeya.IsFlatPrismFamily.unif`, which is itself one-sided, and
  nothing in the dichotomy or in the flat-prism interface reads a bracket.  The Section-8 twin
  `Kakeya.ml1Boot.IsOneSidedUniform` is field-for-field the same predicate but is not the one
  used here, since the consumer chain is typed against the `Kakeya.Factoring` copy.
* **`Kakeya.frostmanConstIn` is not monotone in the index set.**  It is an infimum of
  admissible ratio constants, and shrinking the index set shrinks numerator and denominator
  alike, so it moves in neither direction.  The only ambient-to-subfamily transport,
  `ConvexSpaceBody.IsFrostmanIn.of_subset`, charges the volume-retention ratio of `u''` inside
  `u'`, which `Kakeya.ShadedBody.IsCRefinement` does not supply — it retains *shaded* mass, not
  volume.

This is the version the assembly needs: the same selection, made so that the retained
subfamily is again *one-sidedly* uniform at a constant `Cu` depending only on `Cunif`, and so
that its Frostman constant is controlled by the original one at the same `δ̃ ^ (-ε'')` loss
that the refinement already carries.  `Cu` is handed out *before* `ε''` so that the assembly may
choose `ε''` after seeing the fullness threshold that
`Kakeya.ml1Boot.flatPrism_dichotomy_decoupled` returns at `Cu`; quantifying `Cu` after `ε''`
would make that choice circular.

The parent scale is fixed at `δ̃ ^ (6 ε)`, the only one the middle-factor assembly uses, and the
`ρ ∈ [δ̃, 1]` binder of `Kakeya.ml1Boot.exists_plankDimensions` is discharged from `11 ε ≤ 1`.

**Neither clause is owed any longer.**  The Frostman half is derived, and the uniformity half is
now asserted in the one-sided form that descends for free; see
`Kakeya.ml1Boot.exists_plankDimensions_uniformSelection`, which is proved.  Every member here is
a `δ̃`-tube at one common scale,
and same-scale tubes have exactly equal carrier volume, so the volume-retention ratio that
`ConvexSpaceBody.IsFrostmanIn.of_subset` charges *is* a cardinality ratio, at the same factor;
`Kakeya.ml1Boot.frostmanConstIn_le_of_cRefinement_of_fullness` produces that ratio from the
mass share of the refinement, at the price of one factor of the incoming fullness.  What was
missing on that half was a hypothesis rather than a lemma: the statement carried no fullness
bound at all, and `IsOneSidedUniform` has none of its own — its brackets are on
`ShadedTube.shadeClass` and on the branching counts, nothing pointwise two-sided on
`|Y_i| / |T_i|`.  So the fullness hypothesis `δ̃ ^ (ε'' / 2) ≤ λ(𝕋̃|_{u'}, Ỹ)` is now carried,
and the two halves of the `δ̃ ^ (-ε'')` budget are spent one each: the selection
`Kakeya.ml1Boot.exists_plankDimensions_uniformSelection` is run at `ε'' / 2`, and its
`δ̃ ^ (ε'' / 2)`-refinement is read twice — weakened to the `δ̃ ^ ε''` of the refinement clause by
`Kakeya.ml1Boot.isCRefinement_weaken_exponent`, and, *unweakened*, fed to the Frostman
conversion, where it contributes `ε'' / 2` and the fullness hypothesis the other `ε'' / 2`.
Reading the conversion off the already-weakened `δ̃ ^ ε''` clause would overspend the budget and
would not close.  The hypothesis is free at the one call site,
`Kakeya.ml1Boot.multTildeT_of_rescaledData_atThreshold`, which hands out its own fullness
threshold and simply hands out `ε'' / 2`.

The crude free route is *not* enough, and this records why the fullness hypothesis is not
avoidable: `Kakeya.ml1Boot.card_le` bounds `|u'|` against `|u''| ≥ 1` at the fixed loss
`δ̃ ^ (-4)`, whereas the statement demands `δ̃ ^ (-ε'')` for **arbitrary** `ε'' > 0`.

Nonemptiness of `u''` is therefore proved twice over: it is a clause of the selection, and it
also follows from the cardinality bound.  The selection's copy is used. -/
theorem exists_plankDimensions_uniform (hdim : Module.finrank ℝ E = 3)
    {ε : ℝ} (hε0 : 0 < ε) (hε11 : 11 * ε ≤ 1) (Cunif : NNReal) :
    ∀ ηu > (0 : ℝ), ∀ ε'' > (0 : ℝ),
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {u' tρ : Finset ι}
        (Ttil : ι → ShadedTube δt E) (Tρ : ι → Tube (δt ^ (6 * ε)) E) (pρ : ι → ι),
        u'.Nonempty →
        IsFlatPrismUniform u' Ttil (Tube.ssfGridLen δt) Cunif →
        (∀ k ∈ u', (Ttil k).carrier ⊆ Metric.closedBall 0 1) →
        (u' : Set ι).Pairwise
          (fun k k' => IsEssentiallyDistinct (Ttil k).carrier (Ttil k').carrier) →
        IsParentFamily u' (fun k => (Ttil k).toTube) tρ Tρ pρ →
        Set.SurjOn pρ ↑u' ↑tρ →
        (δt : ENNReal) ^ (ε'' / 2)
          ≤ ShadedBody.fullness u' (fun k => (Ttil k).toShadedBody) →
        ∃ u'' ⊆ u', u''.Nonempty ∧
          (∃ Cu : NNReal, 1 ≤ Cu ∧ (Cu : ENNReal) ≤ (δt : ENNReal) ^ (-ηu) ∧
            Nonempty (IsFlatPrismUniform u'' Ttil (Tube.ssfGridLen δt) Cu)) ∧
          ShadedBody.IsCRefinement u'' (fun k => (Ttil k).toShadedBody) u'
            (fun k => (Ttil k).toShadedBody) ⟨(δt : ℝ) ^ ε'', by positivity⟩ ∧
          frostmanConstIn u'' (fun k => (Ttil k).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall
            ≤ (δt : ENNReal) ^ (-ε'') * frostmanConstIn u'
                (fun k => (Ttil k).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall ∧
          ∃ ap bp : NNReal, δt ≤ ap ∧ ap ≤ bp ∧ bp ≤ δt ^ (6 * ε) ∧
            ∀ m ∈ tρ, ∃ F : ConvexSpaceBody.Factorization (fibre u'' pρ m)
                (fun i => (Ttil i).toConvexSpaceBody) 2,
              IsPlankFamilyOfDimensions plankPigeonhole.C ap bp F.parts
                (fun part =>
                  part.convexHull_biUnion (fun i => (Ttil i).toConvexSpaceBody)) := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by
    rw [hdim]; norm_num : 0 < Module.finrank ℝ E)
  intro ηu hηu
  have hsel :=
    exists_plankDimensions_uniformSelection.{u} (ε := ε) hdim hε0 hε11 Cunif ηu hηu
  intro ε'' hε''0
  filter_upwards [hsel (ε'' / 2) (by positivity),
      self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num))]
    with δt hsel' hδt0 hδtlt1
  have hδt1 : δt ≤ 1 := le_of_lt hδtlt1
  intro ι hdec u' tρ Ttil Tρ pρ hu' hunif hball hED hparent hsurj hfull
  obtain ⟨u'', hu''sub, hu''ne, ⟨Cu, hCu1, hCub, ⟨hunif''⟩⟩, href, ap, bp,
      hδap, hapbp, hbpρ, hplank⟩ :=
    hsel' (ι := ι) (u' := u') (tρ := tρ) Ttil Tρ pρ hu' hunif hball hED hparent hsurj
  have hhref : ShadedBody.IsCRefinement u'' (fun k => (Ttil k).toShadedBody) u'
      (fun k => (Ttil k).toShadedBody) ⟨(δt : ℝ) ^ ε'', by positivity⟩ :=
    isCRefinement_weaken_exponent hδt0 hδt1 (by linarith : ε'' / 2 ≤ ε'') href
  have hfro : frostmanConstIn u'' (fun k => (Ttil k).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall
      ≤ (δt : ENNReal) ^ (-ε'') * frostmanConstIn u'
          (fun k => (Ttil k).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall := by
    exact (frostmanConstIn_le_of_cRefinement_of_fullness hδt0 hδt1
      (e := ε'' / 2) (f := ε'' / 2) (g := ε'')
      (by linarith : ε'' / 2 + ε'' / 2 ≤ ε'') Ttil hu' hu''sub hball href hfull).2
  exact ⟨u'', hu''sub, hu''ne, ⟨Cu, hCu1, hCub, ⟨hunif''⟩⟩, hhref, hfro, ap, bp,
    hδap, hapbp, hbpρ, hplank⟩

/-- **The plank-pigeonhole selection at a dilated parent scale.**

`Kakeya.ml1Boot.exists_plankDimensions_uniformSelection` with the parent hypothesis weakened
from `Kakeya.ml1Boot.IsParentFamily` to `Kakeya.ml1Boot.IsParentFamilyDilate c` and the width
bound correspondingly relaxed from `b_p ≤ δ̃ ^ (6 ε)` to `b_p ≤ c δ̃ ^ (6 ε)`.  It is
`Kakeya.ml1Boot.exists_plankDimensions_dilate` where the undilated form used
`Kakeya.ml1Boot.exists_plankDimensions`, and nothing else in the packaging changes: the
one-sided uniformity clause is `Kakeya.IsFlatPrismUniform.mono_index` applied to the retained
subfamily, which never mentions a parent.

The uniformity *hypothesis* is one-sided as well, matching the conclusion, so the constant
weakening runs through `Kakeya.IsFlatPrismUniform.mono` (Kakeya/Factoring/FlatPrisms.lean:310)
rather than `ShadedTube.ShadedUniformTubeSet.mono`.  This is the point at which the fibre
hierarchy coming down from `Kakeya.ml1Boot.IsFactorTwoScales.midFibreUnif` is finally consumed,
and it is one-sided from that field onwards.

The ratio `c` is a parameter fixed *before* the `∀ᶠ δ̃`, which is what lets the side condition
`c δ̃ ^ (6 ε) ≤ 1` of `Kakeya.ml1Boot.exists_plankDimensions_dilate` be discharged inside
rather than handed to the caller: with `c` and `ε > 0` fixed, `δ̃ ^ (6 ε) → 0`.  The same
condition is what makes the extra conclusion `b_p ≤ 1` available, and that clause is not
cosmetic — it is the scale hypothesis `hb1` of
`Kakeya.ml1Boot.maxDensity_coarse_le_of_card` and of
`Kakeya.ml1Boot.flatPrism_dichotomy_ambient`, which on the dilate route replaces the
`b_p ≤ ρ` that is no longer available. -/
theorem exists_plankDimensions_uniformSelection_dilate [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {ε : ℝ} (hε0 : 0 < ε) (hε11 : 11 * ε ≤ 1) (Cunif : NNReal) (c : ℝ) (hc1 : 1 ≤ c) :
    ∀ ηu > (0 : ℝ), ∀ ε'' > (0 : ℝ),
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {u' tρ : Finset ι}
        (Ttil : ι → ShadedTube δt E) (Tρ : ι → Tube (δt ^ (6 * ε)) E) (pρ : ι → ι),
        u'.Nonempty →
        IsFlatPrismUniform u' Ttil (Tube.ssfGridLen δt) Cunif →
        (∀ k ∈ u', (Ttil k).carrier ⊆ Metric.closedBall 0 1) →
        (u' : Set ι).Pairwise
          (fun k k' => IsEssentiallyDistinct (Ttil k).carrier (Ttil k').carrier) →
        IsParentFamilyDilate c u' (fun k => (Ttil k).toTube) tρ Tρ pρ →
        Set.SurjOn pρ ↑u' ↑tρ →
        ∃ u'' ⊆ u', u''.Nonempty ∧
          (∃ Cu : NNReal, 1 ≤ Cu ∧ (Cu : ENNReal) ≤ (δt : ENNReal) ^ (-ηu) ∧
            Nonempty (IsFlatPrismUniform u'' Ttil (Tube.ssfGridLen δt) Cu)) ∧
          ShadedBody.IsCRefinement u'' (fun k => (Ttil k).toShadedBody) u'
            (fun k => (Ttil k).toShadedBody) ⟨(δt : ℝ) ^ ε'', by positivity⟩ ∧
          ∃ ap bp : NNReal, δt ≤ ap ∧ ap ≤ bp ∧
            (bp : ℝ) ≤ c * ((δt ^ (6 * ε) : NNReal) : ℝ) ∧ bp ≤ 1 ∧
            ∀ m ∈ tρ, ∃ F : ConvexSpaceBody.Factorization (fibre u'' pρ m)
                (fun i => (Ttil i).toConvexSpaceBody) 2,
              IsPlankFamilyOfDimensions plankPigeonhole.C ap bp F.parts
                (fun part =>
                  part.convexHull_biUnion (fun i => (Ttil i).toConvexSpaceBody)) := by
  classical
  intro ηu hηu ε'' hε''0
  have hsel := exists_plankDimensions_dilate (hdim := hdim) hε''0
  let C : ENNReal := ((max 1 Cunif : NNReal) : ENNReal)
  have hC1 : 1 ≤ C := by
    dsimp [C]
    exact ENNReal.coe_le_coe.mpr (le_max_left 1 Cunif)
  have hCtop : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.coe_ne_top
  have hCpos : (0 : ENNReal) < C := zero_lt_one.trans_le hC1
  have htop : C ^ (-1 / ηu) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg' hCpos hCtop
  have hδ₁ : (0 : NNReal) < min 1 (C ^ (-1 / ηu)).toNNReal :=
    lt_min zero_lt_one (by
      rw [← ENNReal.coe_pos, ENNReal.coe_toNNReal htop]
      exact ENNReal.rpow_pos hCpos hCtop)
  have hc0 : (0 : ℝ) ≤ c := le_trans zero_le_one hc1
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc1
  let ρ₀ : NNReal := ⟨1 / c, le_of_lt (one_div_pos.mpr hcpos)⟩
  have hρ₀pos : (0 : NNReal) < ρ₀ := by
    rw [← NNReal.coe_pos]
    dsimp [ρ₀]
    exact one_div_pos.mpr hcpos
  have hcρ₀ : c * ((ρ₀ : NNReal) : ℝ) ≤ 1 := by
    dsimp [ρ₀]
    change c * (1 / c) ≤ 1
    field_simp [hcpos.ne']
    exact le_rfl
  have hε6pos : (0 : ℝ) < 6 * ε := by positivity
  have ht₀pos : (0 : NNReal) < ρ₀ ^ (1 / (6 * ε)) := NNReal.rpow_pos hρ₀pos
  filter_upwards [hsel, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num)),
      nhdsWithin_le_nhds (Iio_mem_nhds hδ₁),
      nhdsWithin_le_nhds (Iio_mem_nhds ht₀pos)]
    with δt hsel' hδt0 hδtlt1 hδtlt2 hδtltc
  have hδt1 : δt ≤ 1 := le_of_lt hδtlt1
  have hδρ : δt ≤ δt ^ (6 * ε) := by
    simpa using (NNReal.rpow_le_rpow_of_exponent_ge hδt0 hδt1 (by linarith : 6 * ε ≤ 1))
  have hcρ1 : c * ((δt ^ (6 * ε) : NNReal) : ℝ) ≤ 1 := by
    have hδtle : δt ≤ ρ₀ ^ (1 / (6 * ε)) := le_of_lt hδtltc
    have hδtρ0 : (δt : NNReal) ^ (6 * ε) ≤ ρ₀ := by
      calc
        (δt : NNReal) ^ (6 * ε) ≤ (ρ₀ ^ (1 / (6 * ε)) : NNReal) ^ (6 * ε) :=
          NNReal.rpow_le_rpow hδtle hε6pos.le
        _ = ρ₀ := by
          rw [← NNReal.rpow_mul]
          have hfin : (1 / (6 * ε)) * (6 * ε) = (1 : ℝ) := by
            field_simp [hε6pos.ne']
          rw [hfin, NNReal.rpow_one]
    exact (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hδtρ0) hc0).trans hcρ₀
  have hδtC : (δt : ENNReal) ≤ C ^ (-1 / ηu) := by
    calc
      (δt : ENNReal) ≤ ((C ^ (-1 / ηu)).toNNReal : ENNReal) :=
        ENNReal.coe_le_coe.mpr (hδtlt2.le.trans (min_le_right _ _))
      _ = C ^ (-1 / ηu) := ENNReal.coe_toNNReal htop
  have hCub : C ≤ (δt : ENNReal) ^ (-ηu) :=
    const_le_rpow_neg hC1 hCtop hηu hδt0 hδtC
  intro ι hdec u' tρ Ttil Tρ pρ hu' hunif hball hED hparent hsurj
  obtain ⟨u'', hu''sub, hu''ne, ap, bp, hδap, hapbp, hbpρ, F, href, hFne, hplank, hvol⟩ :=
    hsel' (ρ := δt ^ (6 * ε)) c hδρ hcρ1 (ι := ι) (κ := ι) (u := u') (tρ := tρ)
      Ttil Tρ pρ hu' hball hED hparent hsurj
  have hbp1 : bp ≤ 1 := NNReal.coe_le_coe.mp (hbpρ.trans hcρ1)
  refine ⟨u'', hu''sub, hu''ne, ⟨max 1 Cunif, le_max_left _ _, hCub,
    ⟨IsFlatPrismUniform.mono_index
      (hunif.mono (le_max_right 1 Cunif)) hu''sub⟩⟩,
    href, ap, bp, hδap, hapbp, hbpρ, hbp1, fun m hm => ⟨F m, hplank m hm⟩⟩

/-- **The plank pigeonhole with the family package retained, at a dilated parent scale.**

`Kakeya.ml1Boot.exists_plankDimensions_uniform` with the parent hypothesis weakened from
`Kakeya.ml1Boot.IsParentFamily` to `Kakeya.ml1Boot.IsParentFamilyDilate c`, the width bound
relaxed from `b_p ≤ δ̃ ^ (6 ε)` to `b_p ≤ c δ̃ ^ (6 ε)`, and the extra clause `b_p ≤ 1` carried.

The derivation is the undilated one verbatim on top of
`Kakeya.ml1Boot.exists_plankDimensions_uniformSelection_dilate`: the Frostman descent
`Kakeya.ml1Boot.frostmanConstIn_le_of_cRefinement_of_fullness` and the weakening
`Kakeya.ml1Boot.isCRefinement_weaken_exponent` read the refinement and the fullness bound only,
so the parent relation is inert in both halves of the `δ̃ ^ (-ε'')` budget.

This is the form the endgame runs, because the `ρ`-parents it can obtain pairwise essentially
distinct are the merged ones of `Kakeya.ml1Boot.exists_merged_rhoParentFamily`, which are
parents only up to the ratio `Kakeya.ml1Boot.plankTubeParents.C 3`.  Running the pigeonhole
*after* the merge is forced: a plank factorization taken at the unmerged `p_ρ` is not one at
`p_ρ'`, the fibres of the latter being unions of the fibres of the former. -/
theorem exists_plankDimensions_uniform_dilate [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {ε : ℝ} (hε0 : 0 < ε) (hε11 : 11 * ε ≤ 1) (Cunif : NNReal) (c : ℝ) (hc1 : 1 ≤ c) :
    ∀ ηu > (0 : ℝ), ∀ ε'' > (0 : ℝ),
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {u' tρ : Finset ι}
        (Ttil : ι → ShadedTube δt E) (Tρ : ι → Tube (δt ^ (6 * ε)) E) (pρ : ι → ι),
        u'.Nonempty →
        IsFlatPrismUniform u' Ttil (Tube.ssfGridLen δt) Cunif →
        (∀ k ∈ u', (Ttil k).carrier ⊆ Metric.closedBall 0 1) →
        (u' : Set ι).Pairwise
          (fun k k' => IsEssentiallyDistinct (Ttil k).carrier (Ttil k').carrier) →
        IsParentFamilyDilate c u' (fun k => (Ttil k).toTube) tρ Tρ pρ →
        Set.SurjOn pρ ↑u' ↑tρ →
        (δt : ENNReal) ^ (ε'' / 2)
          ≤ ShadedBody.fullness u' (fun k => (Ttil k).toShadedBody) →
        ∃ u'' ⊆ u', u''.Nonempty ∧
          (∃ Cu : NNReal, 1 ≤ Cu ∧ (Cu : ENNReal) ≤ (δt : ENNReal) ^ (-ηu) ∧
            Nonempty (IsFlatPrismUniform u'' Ttil (Tube.ssfGridLen δt) Cu)) ∧
          ShadedBody.IsCRefinement u'' (fun k => (Ttil k).toShadedBody) u'
            (fun k => (Ttil k).toShadedBody) ⟨(δt : ℝ) ^ ε'', by positivity⟩ ∧
          frostmanConstIn u'' (fun k => (Ttil k).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall
            ≤ (δt : ENNReal) ^ (-ε'') * frostmanConstIn u'
                (fun k => (Ttil k).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall ∧
          ∃ ap bp : NNReal, δt ≤ ap ∧ ap ≤ bp ∧
            (bp : ℝ) ≤ c * ((δt ^ (6 * ε) : NNReal) : ℝ) ∧ bp ≤ 1 ∧
            ∀ m ∈ tρ, ∃ F : ConvexSpaceBody.Factorization (fibre u'' pρ m)
                (fun i => (Ttil i).toConvexSpaceBody) 2,
              IsPlankFamilyOfDimensions plankPigeonhole.C ap bp F.parts
                (fun part =>
                  part.convexHull_biUnion (fun i => (Ttil i).toConvexSpaceBody)) := by
  classical
  intro ηu hηu
  have hsel :=
    exists_plankDimensions_uniformSelection_dilate (ε := ε) hdim hε0 hε11 Cunif c hc1
      ηu hηu
  intro ε'' hε''0
  filter_upwards [hsel (ε'' / 2) (by positivity),
      self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num))]
    with δt hsel' hδt0 hδtlt1
  have hδt1 : δt ≤ 1 := le_of_lt hδtlt1
  intro ι hdec u' tρ Ttil Tρ pρ hu' hunif hball hED hparent hsurj hfull
  obtain ⟨u'', hu''sub, hu''ne, ⟨Cu, hCu1, hCub, ⟨hunif''⟩⟩, href, ap, bp,
      hδap, hapbp, hbpρ, hbp1, hplank⟩ :=
    hsel' (ι := ι) (u' := u') (tρ := tρ) Ttil Tρ pρ hu' hunif hball hED hparent hsurj
  have hhref : ShadedBody.IsCRefinement u'' (fun k => (Ttil k).toShadedBody) u'
      (fun k => (Ttil k).toShadedBody) ⟨(δt : ℝ) ^ ε'', by positivity⟩ :=
    isCRefinement_weaken_exponent hδt0 hδt1 (by linarith : ε'' / 2 ≤ ε'') href
  have hfro : frostmanConstIn u'' (fun k => (Ttil k).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall
      ≤ (δt : ENNReal) ^ (-ε'') * frostmanConstIn u'
          (fun k => (Ttil k).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall := by
    exact (frostmanConstIn_le_of_cRefinement_of_fullness hδt0 hδt1
      (e := ε'' / 2) (f := ε'' / 2) (g := ε'')
      (by linarith : ε'' / 2 + ε'' / 2 ≤ ε'') Ttil hu' hu''sub hball href hfull).2
  exact ⟨u'', hu''sub, hu''ne, ⟨Cu, hCu1, hCub, ⟨hunif''⟩⟩, hhref, hfro, ap, bp,
    hδap, hapbp, hbpρ, hbp1, hplank⟩

/-! ### Absorbing the dyadic-pigeonhole factor of the coarse Frostman bound

`Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le` delivers the coarse Frostman bound with the
factor `C_↑(3, |u|, δ̃) = 2 (1 + log₂ (8 |u| / (c₃ δ̃ ^ 3)))₊` of
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C`, while hypothesis (c) of
`Kakeya.ml1Boot.multiplicity_coarse_le` reads a bound of the shape `C_Δ δ̃ ^ (-ap')`.  That
factor is *not* a constant, but it is subpolynomial once `|u|` is bounded, and on this chain it
is bounded: the fine family is a nonempty family of pairwise essentially distinct `δ̃`-tubes in
`B₁`, so `Kakeya.ml1Boot.card_le` gives `|u| ≤ C_card δ̃ ^ (-4)` and therefore
`C_↑(3, |u|, δ̃) ≤ A (1 + log₂ (1 / δ̃))` with `A` depending only on `C_card` and on the
dimensional constant `c₃ = Kakeya.lt_volume_convexHull.c 3`.

The three lemmas below carry out the absorption in the same shape as the plank-pigeonhole
absorption `Kakeya.ml1Boot.eventually_plankPigeonhole_loss_le`: the cardinality bound enters as
a hypothesis on `n = |u|`, the polylogarithm is absorbed by
`ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg` and the fixed constant by
`Kakeya.absorb_const_le_rpow_neg`, both at half the available exponent.

The exponent room `σ` is not created here; it is read off the parameter instantiation.  With
`aF ≤ 6 aλ / ε` (the Frostman binder of `Kakeya.ml1Boot.multTildeT_of_planksClose`),
`10 aλ / (ε γ) ≤ η'_{j-1}` (`Kakeya.ml1Boot.middleFactor_numerics`(vi)) and `γ ≤ 1`, one gets
`aF ≤ (3/5) η'_{j-1}`, so at the intended `ap' = η'_{j-1}` any
`σ ≤ (2/5) η'_{j-1}` satisfies `aF + σ ≤ ap'`.  This spends none of the room that
`Kakeya.ml1Boot.multiplicity_coarse_le` itself needs: its `hnum` and `hnum'` constrain `ap'`,
`ε` and `g = γ - β'` only, and are untouched by the choice of `σ`. -/

/-- The arithmetic half of `Kakeya.ml1Boot.eventually_inheritedUpwards_C_le`: with the
cardinality bounded by `C_card δ̃ ^ (-4)`, the dyadic-pigeonhole factor is at most a fixed
constant times `1 + log₂ (1 / δ̃)`.  The constant is existentially quantified because its value
— it involves `log₂ (8 C_card / c₃)` — is of no interest to the consumer; only its independence
of `δ̃` and `n` is.  This is the analogue of the private
`plankPigeonhole_loss_le_polylog` of `Rescaling/Pigeonhole.lean`. -/
private lemma exists_inheritedUpwards_C_le_polylog {Ccard : NNReal} (hCcard : 1 ≤ Ccard) :
    ∃ A : ℝ, 0 < A ∧ ∀ {δt : NNReal}, 0 < δt → δt ≤ 1 → ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ≤ (Ccard : ℝ) * (δt : ℝ) ^ (-4 : ℝ) →
        ((ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C 3 n δt : NNReal) : ENNReal)
          ≤ ENNReal.ofReal A * ENNReal.ofReal (1 + Real.logb 2 (1 / (δt : ℝ))) := by
  let c0 : ℝ := Real.logb 2 (8 * (Ccard : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ))
  let A : ℝ := 2 * (1 + |c0| + 7)
  have hApos : 0 < A := by
    dsimp [A]
    nlinarith [abs_nonneg c0]
  have hA_gec : 2 + 2 * c0 ≤ A := by
    dsimp [A]
    nlinarith [le_abs_self c0]
  have hA_14 : 14 ≤ A := by
    dsimp [A]
    nlinarith [abs_nonneg c0]
  refine ⟨A, hApos, ?_⟩
  intro δt hδ0 hδ1 n hn1 hn
  have hδt0 : (0 : ℝ) < (δt : ℝ) := by exact_mod_cast hδ0
  have hδtne : (δt : ℝ) ≠ 0 := ne_of_gt hδt0
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn1)
  let x : ℝ := Real.logb 2 (1 / (δt : ℝ))
  have h1δ : (1 : ℝ) ≤ 1 / (δt : ℝ) := (one_le_div hδt0).mpr hδ1
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) h1δ
  have hc3pos : 0 < (Metric.lt_volume_convexHull.c 3 : ℝ) := by
    exact_mod_cast Metric.lt_volume_convexHull.c_pos 3
  have hc3ne : (Metric.lt_volume_convexHull.c 3 : ℝ) ≠ 0 := ne_of_gt hc3pos
  have hCpos : (0 : ℝ) < (Ccard : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hCcard)
  have hpos8 : (0 : ℝ) < 8 * (n : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ) := by
    positivity
  have hδp : (0 : ℝ) < (δt : ℝ) ^ (-4 : ℝ) := Real.rpow_pos_of_pos hδt0 (-4 : ℝ)
  have hδpn : (δt : ℝ) ^ (-4 : ℝ) ≠ 0 := ne_of_gt hδp
  have hloginv : Real.logb 2 (δt : ℝ) = -Real.logb 2 (1 / (δt : ℝ)) := by
    rw [one_div, Real.logb_inv]
    ring
  have hlog4 : Real.logb 2 ((δt : ℝ) ^ (-4 : ℝ)) = 4 * x := by
    calc
      Real.logb 2 ((δt : ℝ) ^ (-4 : ℝ)) = (-4 : ℝ) * Real.logb 2 (δt : ℝ) := by
        rw [Real.logb_rpow_eq_mul_logb_of_pos hδt0]
      _ = 4 * x := by
        rw [hloginv]
        dsimp [x]
        ring
  have hlog8n : Real.logb 2 (8 * (n : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ))
      ≤ c0 + 4 * x := by
    have hle8 : (8 : ℝ) * (n : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ)
        ≤ (8 * (Ccard : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ))
            * (δt : ℝ) ^ (-4 : ℝ) := by
      have hn8 : (8 : ℝ) * (n : ℝ)
          ≤ (8 : ℝ) * ((Ccard : ℝ) * (δt : ℝ) ^ (-4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 8)
      calc
        (8 : ℝ) * (n : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ)
            ≤ (8 : ℝ) * ((Ccard : ℝ) * (δt : ℝ) ^ (-4 : ℝ))
                / (Metric.lt_volume_convexHull.c 3 : ℝ) :=
              (div_le_div_of_nonneg_right hn8 hc3pos.le)
        _ = (8 * (Ccard : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ))
              * (δt : ℝ) ^ (-4 : ℝ) := by ring
    have hposC0 : (0 : ℝ) < 8 * (Ccard : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ) := by
      positivity
    have hposC : (0 : ℝ)
        < (8 * (Ccard : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ))
          * (δt : ℝ) ^ (-4 : ℝ) := by
      positivity
    calc
      Real.logb 2 (8 * (n : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ))
          ≤ Real.logb 2 ((8 * (Ccard : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ))
              * (δt : ℝ) ^ (-4 : ℝ)) := by
            exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos8 hle8
      _ = Real.logb 2 (8 * (Ccard : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ))
          + Real.logb 2 ((δt : ℝ) ^ (-4 : ℝ)) := by
            rw [Real.logb_mul (ne_of_gt hposC0) hδpn]
      _ = c0 + 4 * x := by
            dsimp [c0]
            rw [hlog4]
  let arg : ℝ :=
    (n : ℝ) * (2 : ℝ) ^ (3 : ℕ) / ((Metric.lt_volume_convexHull.c 3 : ℝ) * (δt : ℝ) ^ (3 : ℕ))
  have hidt : arg = (8 * (n : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ))
      * (1 / (δt : ℝ)) ^ (3 : ℕ) := by
    dsimp [arg]
    rw [show ((2 : ℝ) ^ (3 : ℕ)) = 8 by norm_num]
    field_simp [hc3ne, hδtne]
  have hlog_arg : Real.logb 2 arg ≤ c0 + 7 * x := by
    rw [hidt]
    calc
      Real.logb 2 ((8 * (n : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ))
          * (1 / (δt : ℝ)) ^ (3 : ℕ))
          = Real.logb 2 (8 * (n : ℝ) / (Metric.lt_volume_convexHull.c 3 : ℝ))
              + Real.logb 2 ((1 / (δt : ℝ)) ^ (3 : ℕ)) := by
              rw [Real.logb_mul (ne_of_gt hpos8)
                (ne_of_gt (by positivity : (0 : ℝ) < (1 / (δt : ℝ)) ^ 3))]
      _ ≤ (c0 + 4 * x) + 3 * x := by
            have h3 : Real.logb 2 ((1 / (δt : ℝ)) ^ (3 : ℕ)) = 3 * x := by
              rw [Real.logb_pow]
              norm_num [x]
            rw [h3]
            linarith
      _ = c0 + 7 * x := by ring
  have hRealle : 2 * (1 + Real.logb 2 arg) ≤ A * (1 + x) := by
    nlinarith [hlog_arg, hA_gec, hA_14, hx0]
  have hRealle_top : ENNReal.ofReal (2 * (1 + Real.logb 2 arg)) ≤ ENNReal.ofReal (A * (1 + x)) :=
    ENNReal.ofReal_le_ofReal hRealle
  have hC : ((ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C 3 n δt : NNReal) : ENNReal)
      = 2 * ENNReal.ofReal (1 + Real.logb 2 arg) := by
    dsimp [arg]
    push_cast
    rfl
  calc
    ((ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C 3 n δt : NNReal) : ENNReal)
        = 2 * ENNReal.ofReal (1 + Real.logb 2 arg) := hC
    _ = ENNReal.ofReal (2 * (1 + Real.logb 2 arg)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    _ ≤ ENNReal.ofReal (A * (1 + x)) := hRealle_top
    _ = ENNReal.ofReal A * ENNReal.ofReal (1 + x) := by
      exact ENNReal.ofReal_mul hApos.le

/-- **The dyadic-pigeonhole factor of the coarse Frostman bound is subpolynomial.**

For every `σ > 0` and every cardinality constant `C_card ≥ 1`, for all sufficiently small
`δ̃ > 0`: whenever `1 ≤ n` and `n ≤ C_card δ̃ ^ (-4)`,

`C_↑(3, n, δ̃) ≤ δ̃ ^ (-σ)`.

The cardinality hypothesis is in the shape `Kakeya.ml1Boot.card_le` supplies, and `n` is
quantified *inside* the eventuality because the tube family is chosen after `δ̃`; the bound is
uniform in `n` on that range.  Compare
`Kakeya.ml1Boot.eventually_plankPigeonhole_loss_le`, which absorbs the analogous factor of
`Kakeya.ConvexSpaceBody.nonempty_factorization.C`. -/
theorem eventually_inheritedUpwards_C_le {σ : ℝ} (hσ : 0 < σ)
    {Ccard : NNReal} (hCcard : 1 ≤ Ccard) :
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ≤ (Ccard : ℝ) * (δt : ℝ) ^ (-4 : ℝ) →
        ((ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C 3 n δt : NNReal) : ENNReal)
          ≤ (δt : ENNReal) ^ (-σ) := by
  obtain ⟨A, hA0, hpoly⟩ := exists_inheritedUpwards_C_le_polylog hCcard
  have hσ2 : 0 < σ / 2 := half_pos hσ
  have hevt_const : ∀ᶠ (δt : NNReal) in 𝓝[>] 0,
      ENNReal.ofReal A ≤ (δt : ENNReal) ^ (-(σ / 2)) := by
    filter_upwards [nnreal_eventually_of_real_eventually (absorb_const_le_rpow_neg hA0 hσ2),
      self_mem_nhdsWithin] with δt hAδ hδ0
    have hδR : 0 < (δt : ℝ) := by exact_mod_cast hδ0
    rw [ennreal_coe_nnreal_rpow hδR]
    exact ENNReal.ofReal_le_ofReal hAδ
  have hevt_poly : ∀ᶠ (δt : NNReal) in 𝓝[>] 0,
      ENNReal.ofReal (1 + Real.logb 2 (1 / (δt : ℝ))) ^ 1
        ≤ (δt : ENNReal) ^ (-(σ / 2)) :=
    ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg hσ2 1
  filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num)),
      hevt_const, hevt_poly] with δt hδ0 hδ1 hAδ hpoly1
  intro n h1n hn
  calc
    ((ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C 3 n δt : NNReal) : ENNReal)
        ≤ ENNReal.ofReal A * ENNReal.ofReal (1 + Real.logb 2 (1 / (δt : ℝ))) :=
          hpoly (δt := δt) hδ0 hδ1.le n h1n hn
    _ = ENNReal.ofReal A * (ENNReal.ofReal (1 + Real.logb 2 (1 / (δt : ℝ))) ^ 1) := by
          rw [pow_one]
    _ ≤ (δt : ENNReal) ^ (-(σ / 2)) * (δt : ENNReal) ^ (-(σ / 2)) := by
          exact mul_le_mul' hAδ hpoly1
    _ = (δt : ENNReal) ^ (-σ) := by
          have hδne : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ0)
          have hδtop : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
          rw [← ENNReal.rpow_add (-(σ / 2)) (-(σ / 2)) hδne hδtop]
          congr 1
          ring

/-- **The dyadic-pigeonhole factor of the coarse Frostman bound, read on a tube family.**

`Kakeya.ml1Boot.eventually_inheritedUpwards_C_le` with the cardinality hypothesis discharged by
`Kakeya.ml1Boot.card_le`: for every `σ > 0`, for all sufficiently small `δ̃ > 0`, every nonempty
family of pairwise essentially distinct `δ̃`-tubes in `B₁ ⊆ ℝ³` satisfies
`C_↑(3, |u|, δ̃) ≤ δ̃ ^ (-σ)`.

This is the form the coarse route consumes: the two hypotheses are exactly the ambient
containment and the essential distinctness that `Kakeya.ml1Boot.multTildeT_of_planksClose`
already carries for the fine family, and both pass to a subfamily, so the bound also holds at
the refined `u'' ⊆ u` that the plank pigeonhole returns. -/
theorem eventually_inheritedUpwards_C_card_le (hdim : Module.finrank ℝ E = 3)
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} {u : Finset ι} (T : ι → Tube δt E),
        u.Nonempty →
        (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (u : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        ((ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C 3 u.card δt : NNReal) : ENNReal)
          ≤ (δt : ENNReal) ^ (-σ) := by
  filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num)),
      eventually_inheritedUpwards_C_le hσ cardBound.one_le_C] with δt hδt0 hδt1 hC
  intro ι u T hne hball hED
  have h1card : 1 ≤ u.card := Nat.succ_le_of_lt (Finset.card_pos.mpr hne)
  have hcardE : (u.card : ENNReal) ≤ (cardBound.C : ENNReal) * (δt : ENNReal) ^ (-4 : ℝ) :=
    card_le hdim hδt0 hδt1.le u T hball hED
  have hδt0R : (0 : ℝ) < (δt : ℝ) := by exact_mod_cast hδt0
  have heq0 : (δt : ENNReal) ^ (-4 : ℝ) = ENNReal.ofReal ((δt : ℝ) ^ (-4 : ℝ)) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := (δt : NNReal))]
    exact ENNReal.ofReal_rpow_of_pos (x := (δt : ℝ)) (p := (-4 : ℝ)) hδt0R
  have heqC : (cardBound.C : ENNReal) * (δt : ENNReal) ^ (-4 : ℝ)
      = ENNReal.ofReal ((cardBound.C : ℝ) * (δt : ℝ) ^ (-4 : ℝ)) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := (cardBound.C : NNReal))]
    rw [heq0]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (cardBound.C : ℝ))]
  have h' : ENNReal.ofReal (u.card : ℝ)
      ≤ ENNReal.ofReal ((cardBound.C : ℝ) * (δt : ℝ) ^ (-4 : ℝ)) := by
    rw [ENNReal.ofReal_natCast, ← heqC]
    exact hcardE
  have hnn : 0 ≤ (cardBound.C : ℝ) * (δt : ℝ) ^ (-4 : ℝ) := by
    exact mul_nonneg (by positivity : 0 ≤ (cardBound.C : ℝ))
      ((Real.rpow_pos_of_pos hδt0R (-4 : ℝ)).le)
  have hcard : (u.card : ℝ) ≤ (cardBound.C : ℝ) * (δt : ℝ) ^ (-4 : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff hnn).mp h'
  exact hC (n := u.card) h1card hcard

/-- **The coarse Frostman bound in the shape hypothesis (c) demands.**

If a quantity `X` is bounded by `L δ̃ ^ (-aF)`, if the subpolynomial factor `L` is below
`δ̃ ^ (-σ)`, and if the exponents leave the room `aF + σ ≤ ap'`, then
`X ≤ C_Δ δ̃ ^ (-ap')`, which is hypothesis (c) of
`Kakeya.ml1Boot.multiplicity_coarse_le`.

Stated for an arbitrary `L` rather than for `C_↑(3, |u|, δ̃)` so that the arithmetic is
separated from the source of the factor, in the same way as
`Kakeya.ml1Boot.rescaled_frostman_le`; the intended `L` is the one bounded by
`Kakeya.ml1Boot.eventually_inheritedUpwards_C_card_le`, and `C_Δ ≥ 1` is only used to weaken
the conclusion into the shape the consumer reads. -/
theorem frostmanConstIn_coarse_absorbed {σ aF ap' : ℝ} {δt : NNReal} (hδt0 : 0 < δt)
    (hδt1 : δt ≤ 1) (hle : aF + σ ≤ ap') {L X : ENNReal}
    (hL : L ≤ (δt : ENNReal) ^ (-σ))
    (hX : X ≤ L * (δt : ENNReal) ^ (-aF)) :
    X ≤ (coarsePlank.C : ENNReal) * (δt : ENNReal) ^ (-ap') := by
  -- 1 ≤ coarsePlank.C
  have one_le_volC : ∀ n : ℕ, (1 : NNReal) ≤ Metric.volume_comparison.C n := by
    intro n
    have hCval : Metric.volume_comparison.C n = ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) : ℝ) := by
      dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      push_cast
      field_simp
    have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hfac : (1 : ℝ) ≤ (Nat.factorial n : ℝ) :=
      mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
    have : (1 : ℝ) ≤ (Metric.volume_comparison.C n : ℝ) := by
      rw [hCval]
      nlinarith
    exact_mod_cast this
  have hdilate : (1 : NNReal) ≤ dilateTestBody.C := by
    dsimp [dilateTestBody.C]
    exact one_le_mul (by norm_num : (1 : NNReal) ≤ 3 ^ 3) (one_le_volC 3)
  have hplink : (1 : NNReal) ≤ plankInTube.C := by
    dsimp [plankInTube.C]
    have hCw : (1 : NNReal) ≤ plankPigeonhole.C := by
      dsimp [plankPigeonhole.C]
      exact one_le_mul (by norm_num : (1 : NNReal) ≤ 16) (one_le_volC 3)
    exact one_le_mul (one_le_mul (by norm_num : (1 : NNReal) ≤ 256) (one_le_pow₀ hCw))
      (one_le_volC 3)
  have hCp : (1 : NNReal) ≤ coarsePlank.C := by
    dsimp [coarsePlank.C]
    exact one_le_mul (one_le_mul (one_le_mul hdilate (by norm_num : (1 : NNReal) ≤ 2)) hplink)
      cardBound.one_le_C
  have hCpE : (1 : ENNReal) ≤ (coarsePlank.C : ENNReal) := by exact_mod_cast hCp
  have hδtE : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδt0.ne'
  have hδtEt : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδt1E : (δt : ENNReal) ≤ 1 := by exact_mod_cast hδt1
  calc
    X ≤ (δt : ENNReal) ^ (-(σ + aF)) := by
      calc
        X ≤ L * (δt : ENNReal) ^ (-aF) := hX
        _ ≤ (δt : ENNReal) ^ (-σ) * (δt : ENNReal) ^ (-aF) :=
          mul_le_mul_of_nonneg_right hL bot_le
        _ = (δt : ENNReal) ^ (-(σ + aF)) := by
              rw [← ENNReal.rpow_add (x := (δt : ENNReal)) (-σ) (-aF) hδtE hδtEt]
              congr 1
              ring
    _ ≤ (δt : ENNReal) ^ (-ap') :=
          ENNReal.rpow_le_rpow_of_exponent_ge hδt1E (by linarith : -ap' ≤ -(σ + aF))
    _ ≤ (coarsePlank.C : ENNReal) * (δt : ENNReal) ^ (-ap') := by
          exact le_mul_of_one_le_left (a := (coarsePlank.C : ENNReal))
            (b := (δt : ENNReal) ^ (-ap')) bot_le hCpE

/-- **The numeric ledger of the coarse endgame at the pinned eccentricity exponent.**

`Kakeya.ml1Boot.normalized_le_of_coarse` does not leave the eccentricity exponent free: its
hypothesis `γ ap' = 10 a / ε` pins `ap' = 10 aλ / (ε γ)` once the fine fullness exponent is
the one the assembly supplies, `a = aλ`.  At that pinned value this lemma discharges the whole
numeric account the coarse route then owes, for `g = γ - β'(γ)`:

* `0 < ap'`, the positivity both `Kakeya.ml1Boot.multiplicity_coarse_le` and
  `Kakeya.ml1Boot.normalized_le_of_coarse` ask for;
* `hnum` and `hnum'` of `Kakeya.ml1Boot.multiplicity_coarse_le`, that is `72 ε + 2 ap' ≤ g`
  and `10 ap' ≤ g / 2`;
* the exponent room `∃ σ > 0, aF + σ ≤ ap'` that
  `Kakeya.ml1Boot.frostmanConstIn_coarse_absorbed` consumes.

**Why `hap'le` carries the factor `2`, and where the factor comes from.**  The only caller of
`Kakeya.ml1Boot.multTildeT_of_planksClose` is
`Kakeya.ml1Boot.multTildeT_of_rescaledData_atThreshold`, and it applies it at
`aLam = 2 aλ₀`, not at `aλ₀`: see the `obtain` in its proof, where the plank-ratio
exponent handed over is `2 * aL` with `aL = aλ₀ = η_{j-1} γ₀ / β'(γ₀)`, the doubling being what
buys the strict room `aF (1 - γ/2) < 5 aLam / ε` that
`Kakeya.ml1Boot.flatPrism_dichotomy_decoupled` needs once `aF` has been degraded to
`6 aλ₀ / ε`.  So the pinned exponent that reaches this ledger is
`ap' = 10 (2 aλ₀) / (ε γ) = 20 aλ₀ / (ε γ)`, twice what clause (vi) of
`Kakeya.ml1Boot.middleFactor_numerics` bounds: that clause gives only
`10 aλ₀ / (ε γ) ≤ η'_{j-1}`.  Stating `hap'le` as `ap' ≤ η'_{j-1}` would therefore make this
lemma unusable at its own call site, and it is stated as `ap' ≤ 2 η'_{j-1}` instead — the
weakest form under which clause (vi) still supplies it for free at `aLam = 2 aλ₀`.

**The two `hnum` clauses are no longer `Kakeya.ml1Boot.numerics_strong` read a fortiori.**  That
lemma states its second conclusion as `10 η'_{j-1} ≤ g / 2`, and what is needed here is
`20 η'_{j-1} ≤ g / 2`, which does *not* follow from it in that direction.  Both clauses are
re-derived from `Kakeya.ml1Boot.Params.Spec.etaPrimeLeGap` and
`Kakeya.ml1Boot.Params.Spec.ninetySixEpsLe` together with the scale monotonicity
`g₀ = gap β γ₀ ≤ gap β γ = g` of `Kakeya.ml1Boot.gap_spec`:

* `hnum'` is **exactly saturated**.  `10 ap' ≤ 20 η'_{j-1} ≤ 20 (g₀ / 40) = g₀ / 2 ≤ g / 2`, and
  the only slack in the chain is `g₀ ≤ g`.  Equality holds precisely when
  `η'_{j-1} = g₀ / 40` and `g₀ = g`, that is at `γ = γ₀`; for `γ > γ₀` the margin is exactly
  `(g - g₀) / 2`.  This is the numeric ceiling of the whole coarse route: nothing here can
  absorb a further constant factor in `aLam`.
* `hnum` still has room.  `72 ε ≤ 72 g₀ / 96 = (3/4) g₀` and `2 ap' ≤ 4 η'_{j-1} ≤ g₀ / 10`,
  which sum to `(17/20) g₀ ≤ g₀ ≤ g`.

The room for `σ` is disjoint from both, as blueprint `note:ml1bootMiddleFactorGaps` records:
`γ ≤ 1` and `aλ₀ ≤ aLam` give
`aF ≤ 6 aλ₀ / ε ≤ 6 aLam / ε = (3/5)(10 aLam / ε) ≤ (3/5) ap'`, so `σ = (2/5) ap'` works, and
that holds for *every* `aLam` above `aλ₀`.

**`hap'le` is a hypothesis, not a consequence of the binders accompanying it.**  It cannot be
dropped: `ap'` grows linearly in `aLam` once `normalized_le_of_coarse` has pinned it, so `hnum'`
reads `100 aLam / (ε γ) ≤ g / 2` and fails for every `aLam > ε γ g / 200`, whatever the package.
What supplies it is the *pinning* of `aLam` upstream.  `Kakeya.ml1Boot.multTildeT_of_planksClose`
fixes `aLam = 2 aλ₀` by an equation — see item (5) of its ledger — and at that value clause (vi)
of `Kakeya.ml1Boot.middleFactor_numerics` gives `hap'le` for free.  `2 aλ₀` sits *on the
boundary* of the bound above: the saturated chain turns `hap'le` into
`100 (2 aλ₀) / (ε γ) ≤ g / 2` with equality at `γ = γ₀`, so the route holds with no margin to
spare, and this lemma is where that margin is accounted for. -/
theorem planksClose_numerics {β γ₀ : ℝ} (hβ0 : 0 ≤ β) (hγ₀ : γ₀ ∈ Set.Ioc β 1)
    {p : Params} (hp : p.Spec β γ₀) {γ : ℝ} (hγ : γ ∈ Set.Icc γ₀ 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ p.N) {aLam aF ap' : ℝ}
    (haLam : p.η (j - 1) * γ₀ / betaPrime β γ₀ ≤ aLam)
    (haF : aF ≤ 6 * (p.η (j - 1) * γ₀ / betaPrime β γ₀) / p.ε)
    (hap'eq : γ * ap' = 10 * aLam / p.ε)
    (hap'le : 10 * aLam / (p.ε * γ) ≤ 2 * p.etaPrime β γ₀ (j - 1)) :
    0 < ap' ∧
      γ - betaPrime β γ ≤ -72 * p.ε - 2 * ap' + 2 * (γ - betaPrime β γ) ∧
      10 * ap' ≤ (γ - betaPrime β γ) / 2 ∧
      ∃ σ > (0 : ℝ), aF + σ ≤ ap' := by
  have hβγ : β < γ₀ := hγ₀.1
  have hγ₀pos : 0 < γ₀ := lt_of_le_of_lt hβ0 hβγ
  have hb0spec := betaPrime_spec hβ0 γ₀ hγ₀
  have hb0pos : 0 < betaPrime β γ₀ := hb0spec.1
  have he : 0 < p.ε := hp.epsPos
  have hsub : j - 1 ≤ p.N := le_trans (Nat.sub_le j 1) hjN
  have hmonoE : p.η 0 ≤ p.η (j - 1) :=
    hp.etaMono (Set.mem_Iic.mpr (Nat.zero_le _)) (Set.mem_Iic.mpr hsub) (Nat.zero_le _)
  have ha_pos : 0 < p.η (j - 1) := lt_of_lt_of_le hp.etaZeroPos hmonoE
  have hlam0 : 0 < p.η (j - 1) * γ₀ / betaPrime β γ₀ :=
    div_pos (mul_pos ha_pos hγ₀pos) hb0pos
  have haLampos : 0 < aLam := lt_of_lt_of_le hlam0 haLam
  have hγ₀leγ : γ₀ ≤ γ := hγ.1
  have hγle1 : γ ≤ 1 := hγ.2
  have hγoc : γ ∈ Set.Ioc β 1 := ⟨lt_of_lt_of_le hβγ hγ₀leγ, hγle1⟩
  have hγpos : 0 < γ := lt_of_lt_of_le hγ₀pos hγ₀leγ
  have hεγpos : 0 < p.ε * γ := mul_pos he hγpos
  have hap'val : ap' = 10 * aLam / (p.ε * γ) := by
    rw [eq_div_iff_mul_eq (show (p.ε * γ) ≠ 0 by positivity)]
    have h1 : p.ε * (γ * ap') = 10 * aLam := by
      rw [hap'eq]
      field_simp [he.ne']
    nlinarith [h1]
  have hap'pos : 0 < ap' := by
    rw [hap'val]
    positivity
  have hap'eta : ap' ≤ 2 * p.etaPrime β γ₀ (j - 1) := by
    rw [hap'val]
    exact hap'le
  -- The two numeric conjuncts, derived directly from `Params.Spec` and `gap_spec`.
  have hεg0 : 96 * p.ε ≤ gap β γ₀ := hp.ninetySixEpsLe
  have hη' : p.etaPrime β γ₀ (j - 1) ≤ gap β γ₀ / 40 := hp.etaPrimeLeGap j hj1 hjN
  have hgap := gap_spec hβ0
  have hgap0 : 0 < gap β γ₀ := hgap.2.1 γ₀ hγ₀
  have hmono : gap β γ₀ ≤ gap β γ := hgap.2.2 hγ₀ hγoc hγ₀leγ
  have hgapSum : 72 * p.ε + 2 * ap' ≤ gap β γ := by
    nlinarith [hεg0, hη', hmono, hgap0, hap'eta]
  have hc2 : gap β γ ≤ -72 * p.ε - 2 * ap' + 2 * gap β γ := by
    nlinarith [hgapSum]
  have hc3 : 10 * ap' ≤ gap β γ / 2 := by
    nlinarith [hη', hmono, hap'eta]
  constructor
  · exact hap'pos
  constructor
  · simpa [gap] using hc2
  constructor
  · simpa [gap] using hc3
  · refine ⟨(2 / 5) * ap', ?_, ?_⟩
    · exact mul_pos (by norm_num) hap'pos
    · have hAF1 : aF ≤ 6 * aLam / p.ε := by
        calc
          aF ≤ 6 * (p.η (j - 1) * γ₀ / betaPrime β γ₀) / p.ε := haF
          _ ≤ 6 * aLam / p.ε := by
            rw [div_le_div_iff₀ he he]
            nlinarith [haLam]
      have hεγle : p.ε * γ ≤ p.ε := by
        simpa using mul_le_mul_of_nonneg_left hγle1 he.le
      have hAF2 : 6 * aLam / p.ε ≤ 6 * aLam / (p.ε * γ) := by
        rw [div_le_div_iff₀ he hεγpos]
        exact mul_le_mul_of_nonneg_left hεγle (mul_nonneg (by norm_num) haLampos.le)
      have hAF3 : aF ≤ (3 / 5) * ap' := by
        calc
          aF ≤ 6 * aLam / p.ε := hAF1
          _ ≤ 6 * aLam / (p.ε * γ) := hAF2
          _ = (3 / 5) * ap' := by
            rw [hap'val]
            field_simp [show p.ε * γ ≠ 0 by positivity]
            ring
      nlinarith [hAF3]

/-- **The plank-width smallness `hbq1` is eventually available in the `𝓝[>] 0` filter.**

Both `b`-tube producers of blueprint `lem:ml1bootPlankTubeParents` take
`hbq1 : plankPigeonhole.C * bp ≤ 1` as an `NNReal` inequality —
`Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` (CoarseDensity.lean:2321) and its
dilated analogue (CoarseDensity.lean:2708).  The constant is the concrete numeral
`plankPigeonhole.C = 16 · Metric.volume_comparison.C 3 = 6144`, so the clause reads
`bp ≤ 1 / 6144`; nothing on the route of `Kakeya.ml1Boot.multTildeT_of_planksClose` produces
it directly.  It is discharged inside that statement's eventually-filter instead: with the
width binder `(bp : ℝ) ≤ 2 · δt ^ (6 · ε)` and `δt → 0`, the real `δt ^ (6 ε)` — hence `bp` —
is eventually below the fixed `1 / (2 · 6144)`, uniformly in `bp`: for every `0 < ε` this lemma
gives `plankPigeonhole.C * bp ≤ 1` eventually. -/
theorem eventually_plankPigeonhole_C_mul_le_one {ε : ℝ} (hε0 : 0 < ε) :
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ bp : NNReal,
      (bp : ℝ) ≤ 2 * ((δt ^ (6 * ε) : NNReal) : ℝ) → plankPigeonhole.C * bp ≤ 1 := by
  have hCeq : plankPigeonhole.C = 6144 := by
    dsimp [plankPigeonhole.C, Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
    norm_num
  have hC0 : 0 < (plankPigeonhole.C : ℝ) := by
    rw [show (plankPigeonhole.C : ℝ) = (6144 : ℝ) by exact_mod_cast hCeq]
    norm_num
  have hε6 : 0 < 6 * ε := by positivity
  let c : NNReal := (2 * plankPigeonhole.C)⁻¹
  have hc0 : 0 < (c : ℝ) := by
    dsimp [c]
    norm_num
  have hc0E : 0 < (c : ENNReal) := by exact_mod_cast hc0
  have hev : ∀ᶠ (δt : NNReal) in 𝓝[>] (0 : NNReal), (δt : ENNReal) ^ (6 * ε) ≤ (c : ENNReal) :=
    ENNReal.eventually_coe_rpow_le_of_pos (ρ := 6 * ε) hε6 hc0E
  filter_upwards [hev] with δt hδ
  have hδt : δt ^ (6 * ε) ≤ c := by
    have hδ' : ((δt ^ (6 * ε) : NNReal) : ENNReal) ≤ (c : ENNReal) := by
      calc
        ((δt ^ (6 * ε) : NNReal) : ENNReal) = (δt : ENNReal) ^ (6 * ε) :=
          ENNReal.coe_rpow_of_nonneg δt (by positivity : (0 : ℝ) ≤ 6 * ε)
        _ ≤ (c : ENNReal) := hδ
    exact ENNReal.coe_le_coe.mp hδ'
  intro bp hbp
  have hcCle : (c : ℝ) = (2 * (plankPigeonhole.C : ℝ))⁻¹ := by
    dsimp [c]
  have hbC : (plankPigeonhole.C : ℝ) * (bp : ℝ) ≤ 1 := by
    calc
      (plankPigeonhole.C : ℝ) * (bp : ℝ)
          ≤ (plankPigeonhole.C : ℝ) * (2 * ((δt ^ (6 * ε) : NNReal) : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hbp hC0.le
      _ = (2 * (plankPigeonhole.C : ℝ)) * ((δt ^ (6 * ε) : NNReal) : ℝ) := by ring
      _ ≤ (2 * (plankPigeonhole.C : ℝ)) * (c : ℝ) := by
              exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hδt)
                (mul_nonneg (by norm_num) hC0.le)
      _ = 1 := by
              rw [hcCle]
              exact mul_inv_cancel₀ (ne_of_gt
                (by positivity : (0 : ℝ) < 2 * (plankPigeonhole.C : ℝ)))
  exact (NNReal.coe_le_coe.mp (by simpa [NNReal.coe_mul] using hbC))

/-- **the whole `K_b`-side obligation of the coarse seam, discharged.**

`Kakeya.ml1Boot.normalized_le_of_coarse_dilate` (Assembly.lean:896) is the step
`Kakeya.ml1Boot.multTildeT_of_planksClose` has to reach.  Exactly **seven** of its hypotheses
mention `K_b`, `M` or `C_F`: the two constant side conditions `1 ≤ M` and
`densityTransfer.C ≤ C_F`, the three `K_b` side conditions, hypothesis (a), and the numeric
clause (d).  Six of the seven are produced below — in the consumer's own syntax, at
`K_b l = hull (fibre u p_b l)`, `M = C_share · b_p / a_p`, `C_F = C_share` — together with the
consumer's parent clause, its pairwise-essential-distinctness clause for the `b`-tubes, and both
of its scale bounds `δ̃ ≤ b`, `b ≤ 1`.  Clause (d) is below, at the same `M` and
`C_F`.  So this is the complete `K_b`-side obligation and not a projection of one: no hypothesis
of the consumer that mentions `K_b`, `M` or `C_F` is left over.

`tb.Nonempty` is asserted so that the `∀ l ∈ t_b` clauses are not vacuously true.

**Two ledger fears, both refuted here.**  The hull route does **not** refine `u`: the producer is
entered at `u'' = u` (`Finset.Subset.refl u`) and every clause below is read at `u` and at
`fibre u p_b l`, so the conclusion is not established at a refinement.  And no `|t_ρ|` enters:
the ρ-parent count is nowhere in this statement or its proof — the block count cancels inside
`Kakeya.ml1Boot.densityIn_fibre_le_mul_sum`, as item (3)'s ledger entry records.

**What is assumed and is not available at the caller.**  `F` here is a *total* family of
plank factorizations, whereas `Kakeya.ml1Boot.multTildeT_of_planksClose` carries the skolemized
`∀ m ∈ tρ, ∃ F, …`.  Producing the total form from it is choice plus an empty `Finpartition`
transported along `fibre u pρ m = ∅` for `m ∉ tρ`; it is plumbing, it is unwritten, and it
belongs to no ledger item.  `h2ρ1` and `hbq1` are eventual facts at `ρ = δ̃ ^ (6 ε)`, the second
being `Kakeya.ml1Boot.eventually_plankPigeonhole_C_mul_le_one`.  Everything else is a binder
`multTildeT_of_planksClose` already has.

It is a named theorem rather than an `example` for the reason the declaration dependency structure requires: `lake shake`
does not see the constants an `example` uses, so the `Rescaling/MassShare.lean` import this file
now carries would be reported unused. -/
theorem Gate.ledgerThree_KbSide [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp ρ : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp)
    (hb2ρ : (bp : ℝ) ≤ 2 * (ρ : ℝ)) (h2ρ1 : 2 * (ρ : ℝ) ≤ 1)
    (hbq1 : plankPigeonhole.C * bp ≤ 1)
    {ap' : ℝ}
    (hratio : (bp : ENNReal) / (ap : ENNReal) ≤ (δt : ENNReal) ^ (-ap'))
    {ι : Type*} [DecidableEq ι] {u tρ : Finset ι}
    (Ttil : ι → ShadedTube δt E) (Tρ : ι → Tube ρ E) (pρ : ι → ι)
    (hu : u.Nonempty)
    (hball : ∀ k ∈ u, (Ttil k).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamilyDilate 2 u (fun k => (Ttil k).toTube) tρ Tρ pρ)
    (F : (m : ι) → ConvexSpaceBody.Factorization (fibre u pρ m)
      (fun i => (Ttil i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (Ttil i).toConvexSpaceBody))) :
    ∃ (tb : Finset (ι × Finset ι)) (Tb : ι × Finset ι → Tube (plankPigeonhole.C * bp) E)
      (pb : ι → ι × Finset ι) (Kb : ι × Finset ι → ConvexSpaceBody E) (cN M CF : NNReal),
      -- NOT VACUOUS: the clauses below are quantified over a NONEMPTY index set
      tb.Nonempty ∧
      -- the `b`-tube scale is admissible for the consumer: `δ̃ ≤ b ≤ 1`
      δt ≤ plankPigeonhole.C * bp ∧ plankPigeonhole.C * bp ≤ 1 ∧
      -- the parent clause of `normalized_le_of_coarse_dilate`, at the `NNReal` ratio `cN`
      IsParentFamilyDilate (cN : ℝ) u (fun i => (Ttil i).toTube) tb Tb pb ∧
      (tb : Set (ι × Finset ι)).Pairwise
        (fun l l' => IsEssentiallyDistinct (Tb l).carrier (Tb l').carrier) ∧
      -- `hM`
      1 ≤ M ∧
      -- `hCF`
      densityTransfer.C ≤ CF ∧
      -- `hKle`
      (∀ l ∈ tb, Kb l ≤ Tube.dilate (Tb l) (cN : ℝ)) ∧
      -- `hKfat`
      (∀ l ∈ tb, volume (Tube.dilate (Tb l) (cN : ℝ)).carrier
        ≤ (M : ENNReal) * volume (Kb l).carrier) ∧
      -- `hKfib`
      (∀ l ∈ tb, ∀ i ∈ u, pb i = l → (Ttil i).toConvexSpaceBody ≤ Kb l) ∧
      -- (a), at the caller's Frostman budget `CF`
      (∀ l ∈ tb, frostmanConstIn (fibre u pb l) (fun i => (Ttil i).toConvexSpaceBody) (Kb l)
        ≤ 2 * (CF : ENNReal) * (δt : ENNReal) ^ (-ap')) ∧
      -- `hballb`, at the free radius `Kakeya.ml1Boot.normalized_le_of_coarse_dilate` now reads
      (∀ l ∈ tb, (Tb l).carrier ⊆ Metric.closedBall (0 : E)
        (5 / 2 + 3 * ((plankPigeonhole.C * bp : NNReal) : ℝ))) ∧
      -- the parent map is onto `tb`, so no `b`-tube index is unused
      Set.SurjOn pb ↑u ↑tb := by
  classical
  have hap : 0 < ap := lt_of_lt_of_le hδt hδa
  have hbp : 0 < bp := lt_of_lt_of_le hap hab
  have hCw : (1 : NNReal) ≤ plankPigeonhole.C := by
    dsimp [plankPigeonhole.C, Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
    norm_num
  have hc0 : (0 : ℝ) ≤ plankTubeParents.C 3 :=
    le_trans (by norm_num) le_plankTubeParents_C_three
  have hcN : ((Real.toNNReal (plankTubeParents.C 3) : NNReal) : ℝ) = plankTubeParents.C 3 :=
    Real.coe_toNNReal _ hc0
  obtain ⟨tb, Tb, pb, htbs, hpf, hsurj, hpair, hcl⟩ :=
    exists_plankTube_parentFamily_essDistinct_dilate hdim hδt hδa hab hb2ρ h2ρ1 hbq1
      (fun k => (Ttil k).toTube) Tρ pρ (Finset.Subset.refl u) hball hparent F hparts hdims
  -- the fibre over a retained `b`-tube index is nonempty, by the producer's surjectivity
  have hne : ∀ l ∈ tb, (fibre u pb l).Nonempty := by
    intro l hl
    obtain ⟨i, hi, hpi⟩ := hsurj hl
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hpi⟩⟩
  have hdb : δt ≤ plankPigeonhole.C * bp := by
    refine le_trans (le_trans hδa hab) ?_
    calc bp = 1 * bp := (one_mul bp).symm
      _ ≤ plankPigeonhole.C * bp := mul_le_mul_left hCw bp
  refine ⟨tb, Tb, pb,
    fun l => (fibre u pb l).convexHull_biUnion (fun i => (Ttil i).toConvexSpaceBody),
    Real.toNNReal (plankTubeParents.C 3), fibreMassShare.C * bp / ap, fibreMassShare.C,
    ⟨pb hu.choose, hpf.mapsTo _ hu.choose_spec⟩,
    hdb, hbq1, ?_, hpair, one_le_fibreMassShare_mul_ratio hap hab,
    densityTransfer_C_le_fibreMassShare_C, ?_, ?_, ?_, ?_,
    fun l hl => (hcl l hl).2.2.2.2.1, hsurj⟩
  · rw [hcN]; exact hpf
  -- `hKle`
  · intro l hl
    rw [hcN]
    exact convexHull_biUnion_le_parent_dilate (fun k => (Ttil k).toTube) Tb pb
      (Finset.Subset.refl u) hpf (hne l hl) (Finset.Subset.refl _)
  -- `hKfat`
  · intro l hl
    rw [hcN]
    exact volume_dilate_le_mul_volume_fibre_convexHull hdim hap hbp hbq1
      (fun k => (Ttil k).toTube) pρ (Finset.Subset.refl u) hparent.mapsTo F hparts hdims Tb pb l
      ((hcl l hl).2.2.2.2.2.2) (hne l hl)
  -- `hKfib`
  · intro l hl i hi hpi
    exact Finset.le_convexHull_biUnion (fun i => (Ttil i).toConvexSpaceBody)
      (Finset.mem_filter.mpr ⟨hi, hpi⟩)
  -- (a)
  · intro l hl
    exact frostmanConstIn_fibre_convexHull_le_dilate hdim hδt hδa hab hbq1 hratio
      (fun k => (Ttil k).toTube) Tρ pρ (Finset.Subset.refl u) hparent F hparts hdims Tb pb hpf
      (fun j hj => (hcl j hj).2.2.2.2.2.2) hl

/-- **clause (d) survives item (3)'s constant, and no exponent moves.**

`Rescaling/MassShare.lean`'s module docstring names one knock-on of settling item (3)'s numeral
at `Kakeya.ml1Boot.fibreMassShare.C` rather than at `2 C_T`: hypotheses (a) **and** (d) of
`Kakeya.ml1Boot.normalized_le_of_coarse_dilate` both read that factor, so (d) has to stay
dischargeable at the new constant.  It does.  The `M` that supplies is
`C_share · b_p / a_p ≤ C_share · δ̃ ^ (-a'_p)` by `hratio`, so the left side is a `δ̃`-free
constant times `δ̃ ^ (-2 a'_p)` against a right side `δ̃ ^ (-5 a'_p)` — three powers of `a'_p` of
slack, absorbed by `Kakeya.ml1Boot.eventually_mul_rpow_le_rpow` (BallRadius.lean:165).

Stated at the same `M` and `C_F` supplies, and quantified over `a_p`, `b_p` so that
it holds at whatever widths the caller is handed. -/
theorem Gate.ledgerThree_clauseD (c : NNReal) {ap' : ℝ} (hap' : 0 < ap') :
    ∀ᶠ (δt : NNReal) in 𝓝[>] (0 : NNReal), ∀ ap bp : NNReal, 0 < ap →
      (bp : ENNReal) / (ap : ENNReal) ≤ (δt : ENNReal) ^ (-ap') →
      4 * (factorOneScaleUniformDilate.C : ENNReal)
          * ((fineNormalizeDilate.C c : ENNReal) ^ 2
              * ((fibreMassShare.C * bp / ap : NNReal) : ENNReal))
          * 2 * (2 * (fibreMassShare.C : ENNReal)) * (δt : ENNReal) ^ (-ap')
        ≤ (δt : ENNReal) ^ (-5 * ap') := by
  set K : ENNReal := 4 * (factorOneScaleUniformDilate.C : ENNReal)
      * ((fineNormalizeDilate.C c : ENNReal) ^ 2 * (fibreMassShare.C : ENNReal))
      * 2 * (2 * (fibreMassShare.C : ENNReal)) with hK
  have hKtop : K ≠ ⊤ := by
    rw [hK]; finiteness
  filter_upwards [eventually_mul_rpow_le_rpow hKtop
      (p := -2 * ap') (q := -5 * ap') (by linarith), self_mem_nhdsWithin] with δt habs hδt0
  intro ap bp hap hratio
  have hδpos : (0 : NNReal) < δt := hδt0
  have hδne : (δt : ENNReal) ≠ 0 := by simpa using (ne_of_gt hδpos)
  have hδtop : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hM : ((fibreMassShare.C * bp / ap : NNReal) : ENNReal)
      ≤ (fibreMassShare.C : ENNReal) * (δt : ENNReal) ^ (-ap') := by
    rw [ENNReal.coe_div (ne_of_gt hap), ENNReal.coe_mul, mul_div_assoc]
    gcongr
  calc 4 * (factorOneScaleUniformDilate.C : ENNReal)
          * ((fineNormalizeDilate.C c : ENNReal) ^ 2
              * ((fibreMassShare.C * bp / ap : NNReal) : ENNReal))
          * 2 * (2 * (fibreMassShare.C : ENNReal)) * (δt : ENNReal) ^ (-ap')
      ≤ 4 * (factorOneScaleUniformDilate.C : ENNReal)
          * ((fineNormalizeDilate.C c : ENNReal) ^ 2
              * ((fibreMassShare.C : ENNReal) * (δt : ENNReal) ^ (-ap')))
          * 2 * (2 * (fibreMassShare.C : ENNReal)) * (δt : ENNReal) ^ (-ap') := by
        gcongr
    _ = K * ((δt : ENNReal) ^ (-ap') * (δt : ENNReal) ^ (-ap')) := by rw [hK]; ring
    _ = K * (δt : ENNReal) ^ (-ap' + -ap') := by rw [ENNReal.rpow_add _ _ hδne hδtop]
    _ = K * (δt : ENNReal) ^ (-2 * ap') := by ring_nf
    _ ≤ (δt : ENNReal) ^ (-5 * ap') := habs





/-- **The empty index set carries a factorization at every constant.**

The plumbing half of `ConvexSpaceBody.Factorization` extends `Finpartition`, and
`Finpartition.empty` partitions `∅`; the three remaining fields — `isKatzTao`,
`maxDensity_le_mul` and `simDims` — quantify over `parts = ∅` and are vacuous.  This is what lets
the skolemization below produce a *total* family of factorizations from one that is asserted only
over `tρ`. -/
theorem factorization_of_eq_empty {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (V : ι → ConvexSpaceBody E) {C : NNReal} (hs : s = ∅) :
    Nonempty (ConvexSpaceBody.Factorization s V C) := by
  subst hs
  refine ⟨{ toFinpartition := Finpartition.empty _, isKatzTao := ?_,
            maxDensity_le_mul := ?_, simDims := ?_ }⟩ <;> simp [IsKatzTao]

/-- **the skolemization of the plank factorizations is free.**

`Kakeya.ml1Boot.multTildeT_of_planksClose` carries its plank factorizations in the skolemized
shape `∀ m ∈ tρ, ∃ F, IsPlankFamilyOfDimensions …`, whereas
`Kakeya.ml1Boot.Gate.ledgerThree_KbSide` — and, through it,
`Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct_dilate` and every step of the coarse
route — consumes a **total** family `F : (m : ι) → Factorization (fibre u pρ m) 𝕍 2`. Producing
the total form was recorded as "choice plus an empty `Finpartition` transported along
`fibre u pρ m = ∅` for `m ∉ tρ`; it is plumbing, it is unwritten, and it belongs to no ledger
item".

Two things fall out for free and are exported with it:

* the transport is legitimate because `hmapsTo` — the field
  `Kakeya.ml1Boot.IsParentFamilyDilate.mapsTo`, which the statement holds at ratio `2` — forces
  `fibre u pρ m = ∅` off `tρ`, so `Kakeya.ml1Boot.factorization_of_eq_empty` applies there;
* `hparts`, the nonemptiness of the parts that both the `b`-tube producer and
  `Kakeya.ml1Boot.volume_dilate_le_mul_volume_fibre_convexHull` demand, is **not** an extra
  obligation at all: it is `Finpartition.nonempty_of_mem_parts`, true of every factorization, and
  needs no hypothesis of this statement.

Stated over an arbitrary body family `𝕍` and arbitrary widths, so that it is not tied to the
endgame's `plankPigeonhole.C`. -/
theorem exists_totalFactorization {ι : Type*} [DecidableEq ι] {u tρ : Finset ι}
    (V : ι → ConvexSpaceBody E) (pρ : ι → ι) (hmapsTo : ∀ i ∈ u, pρ i ∈ tρ)
    {Cw ap bp : NNReal}
    (hex : ∀ m ∈ tρ, ∃ F : ConvexSpaceBody.Factorization (fibre u pρ m) V 2,
      IsPlankFamilyOfDimensions Cw ap bp F.parts
        (fun part => part.convexHull_biUnion V)) :
    ∃ F : (m : ι) → ConvexSpaceBody.Factorization (fibre u pρ m) V 2,
      (∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty) ∧
      (∀ m ∈ tρ, IsPlankFamilyOfDimensions Cw ap bp (F m).parts
        (fun part => part.convexHull_biUnion V)) := by
  classical
  have hempty : ∀ m : ι, m ∉ tρ → fibre u pρ m = ∅ := by
    intro m hm
    refine Finset.eq_empty_of_forall_notMem ?_
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hiu, hpi⟩
    exact hm (hpi ▸ hmapsTo i hiu)
  refine ⟨fun m => if h : m ∈ tρ then (hex m h).choose
      else (factorization_of_eq_empty V (C := 2) (hempty m h)).some, ?_, ?_⟩
  · intro m _ part hpart
    exact Finpartition.nonempty_of_mem_parts _ hpart
  · intro m hm
    dsimp only
    rw [dif_pos hm]
    exact (hex m hm).choose_spec








end KatzTao

end ml1Boot

end Kakeya
