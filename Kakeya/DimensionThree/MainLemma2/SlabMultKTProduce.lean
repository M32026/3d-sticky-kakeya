/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.KTRho2Interface
public import Kakeya.DimensionThree.MainLemma2.SetupSideData

/-!
# The slab multiplicity input `SlabMultKT` on the degenerate path (T10, route R15)

Row T10 of the side-data construction plan ((a)), conjunct 4 of
`Kakeya.VeryNotSticky.SideDataObligations`: for every small `δ`, every configuration at
`(δ, β, η, exscal, ϱ)` on the degenerate path `b = δ` and every `bd : BallData cfg` with
`bd.C₀ = C₀bd`, the estimate `cfg.KTRho2ScaleData bd (4ϱ) (9·cfg.η) (3ϱ)` holds — GWZ Lemma 3.7
(`gwz.txt` l.330–336, blueprint `genKKT`) in its Remark 3.6 form (l.294–310) at the tangential
step, equation (104) (l.2387–2392): a family of bodies comparable to `ρ₂`-tubes in `B₁`, Katz–Tao at
`δ^{-3ϱ}` and `δ^{9η}`-full, has multiplicity at most `δ^{-4ϱ} |𝕋|^β`.

## Where the fullness threshold `9·cfg.η` comes from

`Kakeya.VeryNotSticky.ktRho2ScaleData_of_katzTaoEstimate` (T7K) derives the same estimate from
`K_KT(β)` but at an unspecified threshold `η₁ > 0` chosen before `δ`, so the clause
`Kakeya.VeryNotSticky.SlabMultKT.fullness_threshold : 9 * cfg.η ≤ η₁` cannot be discharged from
it. The tree's one mechanism for a `K_KT`-dependent constraint on `η`
fixed *before* `η` is the window datum `Kakeya.CoarseKTWindow` every configuration carries as
`cfg.ckt` (`Kakeya.CoarseKTData`): its field `hwin : Kakeya.WindowFour … β we wη wρ` is Lemma 3.7
with the Katz–Tao parameter `τ` free below the tube scale and the fullness threshold `τ^{wη}`,
and `hηKT : 3 * η ≤ exscal * wη` is the budget clause. Reading `hwin` for the enclosing
`C₀ρ₂`-tubes with

  `τ := δ ^ max 1 (10η / wη)`

gives `τ^{wη} ≤ δ^{10η} = δ^{9η} · δ^{η}`, so the `δ^{9η}`-fullness of the bodies survives the
enclosure (which costs the constant `K = ktRho2EnclosureConstant C₀ ≤ δ^{-η}`), and the loss
`τ^{-we} = δ^{-we · max 1 (10η/wη)} ≤ δ^{-ϱ/2}` because `10η/wη ≤ (10/3) exscal ≤ 5/3` (`hηKT`)
and `we ≤ ϱ² wb/1440 ≤ ϱ/1440` (`hwe`, `wb ≤ β ≤ 1`, `ϱ ≤ 1`). With `Δ_max ≤ K δ^{-3ϱ}` and
`K ≤ δ^{-ϱ/2}` the total loss is `ϱ/2 + ϱ/2 + 3ϱ(1-β) ≤ 4ϱ`
(`Kakeya.VeryNotSticky.ktRho2_loss_arith`). So `η₁ := 9 * cfg.η` is data and
`fullness_threshold` is `le_rfl`; no new field, no new premise, no clause on `K_KT`.

## The route in this file

* `Kakeya.VeryNotSticky.exists_enclosing_shadedTubes_of_ktRho2` — the geometric half of T7K,
  factored out: the `1/8`-homothety and the `C₀ρ₂`-tube enclosure of the bodies, with
  multiplicity preserved, `Δ_max` multiplied by `K` and fullness divided by at most `K`.
* `Kakeya.VeryNotSticky.ktRho2_window_loss_le` — the exponent arithmetic of the `τ` choice.
* `Kakeya.VeryNotSticky.ktRho2ScaleData_of_ckt` — the estimate at `(4ϱ, 9η, 3ϱ)` from
  `cfg.ckt.hwin` at `b = δ`, under four smallness conditions on `δ`.
* `Kakeya.VeryNotSticky.eventually_ktRho2ScaleData_degenerate` — the `∀ᶠ δ` form, conjunct 4
  of `Kakeya.VeryNotSticky.SideDataObligations` verbatim (tripwires below).
* `Kakeya.VeryNotSticky.slabMultKTOfThresholds` — the four-field `SlabMultKT` from the estimate
  and the density-constant threshold `tangentialSlabDecompConstant tc.C ≤ δ^{-η}` (which T6,
  conjunct 2, supplies); `Kakeya.VeryNotSticky.eventually_nonempty_slabMultKT_degenerate` is
  its `∀ᶠ δ` form.

The two `δ`-thresholds of the tube scale are `C₀ρ₂ ≤ 1/8` (the enclosure) and `C₀ρ₂ ≤ wρ`
(the window radius, from `cfg.ckt.hδrad : 6 δ^{exscal-η} ≤ wρ`): at `b = δ`,
`ρ₂ = δ^{1-exscal}`, and `C₀ δ^{1-exscal} ≤ 6 δ^{exscal-η}` is the absorption
`C₀ δ^{1-2exscal+η} ≤ 6` of the `δ`-free `C₀`, which needs `exscal ≤ 1/2`. The hypotheses
`exscal ≤ 1/2` and `ϱ ≤ 1` are those of `Kakeya.VeryNotSticky.CaseParams` (`scale`, `slabBias`) that
the assembly already extracts (T8 takes the same two).
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Filter Topology

universe u

/-! ### The enclosure, factored out of T7K -/

/-- **Bodies comparable to `ρ₂`-tubes are enclosed in `C₀ρ₂`-tubes** with multiplicity
preserved, the Katz–Tao bound multiplied by `K = ktRho2EnclosureConstant C₀` and fullness divided
by at most `K`. This is the geometric half of
`Kakeya.VeryNotSticky.ktRho2ScaleData_of_katzTaoEstimate`, stated on
its own so that the analytic input can be `Kakeya.WindowFour` instead of Lemma 3.7 at `τ = δ`.

The bodies are first shrunk by the homothety of centre `0` and ratio `1/8`
(`ShadedBody.homothety`; `μ`, `λ` and `Δ_max` are exactly invariant), then each shrunk body,
of `1`-thickness `≤ 2C₀ρ₂/8 ≤ C₀ρ₂`, is enclosed in a unit `C₀ρ₂`-tube inside `B₁`
(`Kakeya.VeryNotSticky.exists_tube_of_thickness_one_le`) shaded by the body's own shade
(`Kakeya.VeryNotSticky.shadedTubeOfSubset`); off `t` a default empty-shaded tube is used. The
volume ratio tube/body is at most `K` (`Kakeya.VeryNotSticky.tube_volume_le_sixteen_mul_sq`
against `Kakeya.VeryNotSticky.ofReal_le_volume_of_tubeProfile`), whence the `Δ_max` clause
(`ConvexSpaceBody.IsVolumeControlledEnlargement.isKatzTao`) and the fullness clause
(`Kakeya.VeryNotSticky.le_fullness_of_enlargement`). -/
theorem exists_enclosing_shadedTubes_of_ktRho2 (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    {t : Finset bd.ω} (htne : t.Nonempty) (T : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ j ∈ t, (T j).carrier ⊆ closedBall 0 1)
    (hthick : ∀ j ∈ t, HasThicknesses (T j).carrier (2 * bd.C₀)
      ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)])
    {κ : ℝ} (hKTt : ConvexSpaceBody.IsKatzTao t (fun j ↦ (T j).toConvexSpaceBody)
      ((cfg.δ : ENNReal) ^ (-κ)))
    (hr8 : ((bd.C₀ * cfg.rho2 : NNReal) : ℝ) ≤ 1 / 8) :
    ∃ T' : bd.ω → ShadedTube (bd.C₀ * cfg.rho2) (EuclideanSpace ℝ (Fin 3)),
      (∀ j, (T' j).carrier ⊆ closedBall 0 1) ∧
      ShadedBody.multiplicity t (fun j ↦ (T' j).toShadedBody) = ShadedBody.multiplicity t T ∧
      ConvexSpaceBody.IsKatzTao t (fun j ↦ (T' j).toConvexSpaceBody)
        ((ktRho2EnclosureConstant bd.C₀ : ENNReal) * (cfg.δ : ENNReal) ^ (-κ)) ∧
      ∀ x y : ENNReal, x ≤ (ShadedBody.fullness t T : ENNReal) →
        y * (ktRho2EnclosureConstant bd.C₀ : ENNReal) ≤ x →
        y ≤ (ShadedBody.fullness t (fun j ↦ (T' j).toShadedBody) : ENNReal) := by
  have hδ0 : 0 < cfg.δ := cfg.hδ
  have hδ1 : cfg.δ ≤ 1 := cfg.hδ1
  have hC₀ : 1 ≤ bd.C₀ := bd.hC₀
  have hC₀pos : (0 : NNReal) < bd.C₀ := lt_of_lt_of_le zero_lt_one hC₀
  set K : NNReal := ktRho2EnclosureConstant bd.C₀ with hK_def
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
  set r : NNReal := bd.C₀ * ρ with hr_def
  have hr1 : r ≤ 1 := by
    have : (r : ℝ) ≤ 1 := hr8.trans (by norm_num)
    exact_mod_cast this
  -- the `1/8`-homothety of the family
  have h8 : (8⁻¹ : ℝ) ≠ 0 := by norm_num
  set W' : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j ↦ (T j).homothety (0 : EuclideanSpace ℝ (Fin 3)) h8 with hW'_def
  have hone_le_two : (1 : NNReal) ≤ 2 * bd.C₀ := by
    calc (1 : NNReal) ≤ bd.C₀ := hC₀
      _ = 1 * bd.C₀ := (one_mul _).symm
      _ ≤ 2 * bd.C₀ := by gcongr; norm_num
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
        have h2C : thickness ℝ (T j).carrier 1 ≤ 2 * (bd.C₀ : ℝ) * (ρ : ℝ) := by
          simpa using (hthick j hj 1).2
        have hbddT : Bornology.IsBounded (T j).carrier := (T j).isCompact'.isBounded
        calc thickness ℝ (W' j).carrier 1
            = thickness ℝ (AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) (8⁻¹ : ℝ) ''
                (T j).carrier) 1 := rfl
          _ = |(8⁻¹ : ℝ)| * thickness ℝ (T j).carrier 1 :=
              thickness_homothety_image_eq hbddT 0 h8 1
          _ ≤ |(8⁻¹ : ℝ)| * (2 * (bd.C₀ : ℝ) * (ρ : ℝ)) := by gcongr
          _ ≤ (r : ℝ) := by
              rw [hr_def, NNReal.coe_mul, abs_of_pos (by norm_num : (0:ℝ) < 8⁻¹)]
              have : (0 : ℝ) ≤ (bd.C₀ : ℝ) * ρ := by positivity
              nlinarith
      obtain ⟨x, y, hxy, hsubK, htube⟩ :=
        exists_tube_of_thickness_one_le hbdd hne hball' hth hr8
      refine ⟨shadedTubeOfSubset (Tube.mk' r hxy) (W' j) hsubK, htube, fun _ ↦
        ⟨hsubK, rfl, ?_⟩⟩
      -- volume comparison: `16 r² = K · 8⁻³ · ρ₂² / (6 (2C₀)³)`
      have hvolT : ENNReal.ofReal (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : NNReal) : ℝ) ^ 3)) ≤
          volume (T j).carrier :=
        ofReal_le_volume_of_tubeProfile (T j).toConvexSpaceBody hone_le_two (hthick j hj)
      have hvolW' : volume (W' j).carrier = ENNReal.ofReal (1 / 512) * volume (T j).carrier :=
        volume_homothety_eighth (T j).toConvexSpaceBody
      calc volume (shadedTubeOfSubset (Tube.mk' r hxy) (W' j) hsubK).carrier
          = volume (Tube.mk' r hxy).carrier := rfl
        _ ≤ ((16 : NNReal) : ENNReal) * ((r : ENNReal) ^ (2 : ℕ)) :=
            tube_volume_le_sixteen_mul_sq hr1 _
        _ = (K : ENNReal) * (ENNReal.ofReal (1 / 512) *
              ENNReal.ofReal (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : NNReal) : ℝ) ^ 3))) := by
            have hreal : (16 : ℝ) * ((r : ℝ)) ^ 2 =
                (K : ℝ) * (1 / 512 * (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : NNReal) : ℝ) ^ 3))) := by
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
                    (1 / 512 * (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : NNReal) : ℝ) ^ 3)))) := by
                  rw [hreal]
              _ = (K : ENNReal) * (ENNReal.ofReal (1 / 512) *
                    ENNReal.ofReal (((ρ : ℝ) ^ 2) / (6 * ((2 * bd.C₀ : NNReal) : ℝ) ^ 3))) := by
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
          have : (0 : ℝ) < bd.C₀ := hC₀pos
          positivity
        exact ENNReal.mul_pos (by simp) hT0.ne'
      exact hpos.ne' hj0
    exact le_fullness_of_enlargement (t := t) (V := W') (W := fun j ↦ (T' j).toShadedBody)
      (K := (K : ENNReal)) (fun j hj ↦ hshj j hj)
      (fun j hj ↦ measure_mono (hsubj j hj)) (fun j hj ↦ hvolj j hj) h0 hfullW' hxy

/-! ### The exponent arithmetic of the `τ` choice -/

/-- **The loss exponent of the window read at `τ = δ^{max 1 (10η/wη)}`.** From the budget
clause `3η ≤ exscal · wη` of `Kakeya.CoarseKTWindow` (`hηKT`) and `exscal ≤ 1/2`,
`10η/wη ≤ 5/3`; from `we ≤ ϱ² wb/1440` (`hwe`), `wb ≤ β ≤ 1` and `ϱ ≤ 1`, `we ≤ ϱ/1440`. Hence
`we · max 1 (10η/wη) ≤ ϱ/2`, which is the `δ^{-ϱ/2}` that
`Kakeya.VeryNotSticky.ktRho2_loss_arith` charges for Lemma 3.7's loss. -/
theorem ktRho2_window_loss_le {η ϱ exscal we wη wb β : ℝ} (hϱ : 0 < ϱ) (hϱ1 : ϱ ≤ 1)
    (hexscal12 : exscal ≤ 1 / 2) (hwe0 : 0 < we) (hwe : we ≤ ϱ ^ 2 * wb / 1440)
    (hwb : wb ≤ β) (hβ1 : β ≤ 1) (hwη : 0 < wη)
    (hηKT : 3 * η ≤ exscal * wη) :
    we * max 1 (10 * η / wη) ≤ ϱ / 2 := by
  have h1 : 10 * η / wη ≤ 5 / 3 := by
    rw [div_le_iff₀ hwη]
    nlinarith
  have hL : max 1 (10 * η / wη) ≤ 5 / 3 := max_le (by norm_num) h1
  have hwe' : we ≤ ϱ / 1440 := by
    refine hwe.trans ?_
    have : ϱ ^ 2 * wb ≤ ϱ := by nlinarith
    linarith
  calc we * max 1 (10 * η / wη) ≤ (ϱ / 1440) * (5 / 3) :=
        mul_le_mul hwe' hL (le_trans zero_le_one (le_max_left _ _)) (by positivity)
    _ ≤ ϱ / 2 := by linarith

/-! ### The estimate from `cfg.ckt` at `b = δ` -/

/-- **The slab Katz–Tao estimate at the threshold `9·cfg.η`, from the configuration's own
window** (GWZ Lemma 3.7 via Remark 3.6 at the tangential step, (104), `gwz.txt` l.2387–2392;
route R15 of ). On the degenerate path `b = δ` (so
`ρ₂ = δ^{1-exscal}`) and under four smallness conditions on `δ` — `C₀ρ₂ ≤ 1/8` for the
enclosure, `C₀ δ^{1-2exscal+η} ≤ 6` for the window radius `C₀ρ₂ ≤ wρ`
(`Kakeya.CoarseKTData.hδrad`), and `K ≤ δ^{-η}`, `K ≤ δ^{-ϱ/2}` for the enclosure constant
`K = Kakeya.VeryNotSticky.ktRho2EnclosureConstant C₀` — every family of bodies comparable to
`ρ₂`-tubes in `B₁`, Katz–Tao at `δ^{-3ϱ}` and `δ^{9η}`-full, has multiplicity
`≤ δ^{-4ϱ} |𝕋|^β`.

Proof: enclose (`Kakeya.VeryNotSticky.exists_enclosing_shadedTubes_of_ktRho2`), then read
`cfg.ckt.hwin` at tube scale `C₀ρ₂` and Katz–Tao parameter `τ = δ^{max 1 (10η/wη)} ≤ δ ≤ C₀ρ₂`:
the fullness `τ^{wη} ≤ δ^{10η} ≤ δ^{9η}/K` of the tubes is granted, the loss `τ^{-we} ≤ δ^{-ϱ/2}`
(`Kakeya.VeryNotSticky.ktRho2_window_loss_le`), and `Δ_max ≤ K δ^{-3ϱ}` closes by
`Kakeya.VeryNotSticky.ktRho2_loss_arith`. -/
theorem ktRho2ScaleData_of_ckt (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (hb : cfg.b = cfg.δ) (hexscal12 : cfg.exscal ≤ 1 / 2) (hϱ1 : cfg.ϱ ≤ 1)
    (h8 : cfg.δ ^ (1 - cfg.exscal) ≤ (8 * bd.C₀)⁻¹)
    (hwρ : cfg.δ ^ (1 - 2 * cfg.exscal + cfg.η) ≤ 6 / bd.C₀)
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
  -- `ρ₂ = δ^{1-exscal}` at `b = δ`
  have hρ : cfg.rho2 = cfg.δ ^ (1 - cfg.exscal) := by
    rw [VeryNotSticky.rho2, VeryNotSticky.r₁, hb, NNReal.rpow_sub hδ0.ne', NNReal.rpow_one]
  -- the tube scale `r = C₀ ρ₂`
  set r : NNReal := bd.C₀ * cfg.rho2 with hr_def
  have hr8 : (r : ℝ) ≤ 1 / 8 := by
    have : r ≤ 1 / 8 := by
      calc r = bd.C₀ * cfg.δ ^ (1 - cfg.exscal) := by rw [hr_def, hρ]
        _ ≤ bd.C₀ * (8 * bd.C₀)⁻¹ := by gcongr
        _ = 1 / 8 := by
            rw [mul_inv, ← mul_assoc, mul_comm bd.C₀, mul_assoc, mul_inv_cancel₀ hC₀pos.ne',
              mul_one, one_div]
    exact_mod_cast this
  have hδρ : cfg.δ ≤ cfg.rho2 := by
    rw [hρ]
    calc cfg.δ = cfg.δ ^ (1 : ℝ) := (NNReal.rpow_one _).symm
      _ ≤ cfg.δ ^ (1 - cfg.exscal) :=
          NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith [cfg.hexscal])
  have hδr : cfg.δ ≤ r := by
    calc cfg.δ ≤ cfg.rho2 := hδρ
      _ = 1 * cfg.rho2 := (one_mul _).symm
      _ ≤ bd.C₀ * cfg.rho2 := by gcongr
  have hr0 : 0 < r := lt_of_lt_of_le hδ0 hδr
  -- the window radius: `C₀ ρ₂ = C₀ δ^{1-2exscal+η} · δ^{exscal-η} ≤ 6 δ^{exscal-η} ≤ wρ`
  have hrwρ : r ≤ cfg.ckt.wρ := by
    have hsplit : cfg.δ ^ (1 - cfg.exscal) =
        cfg.δ ^ (1 - 2 * cfg.exscal + cfg.η) * cfg.δ ^ (cfg.exscal - cfg.η) := by
      rw [← NNReal.rpow_add hδ0.ne']
      congr 1
      ring
    calc r = bd.C₀ * cfg.δ ^ (1 - cfg.exscal) := by rw [hr_def, hρ]
      _ = (bd.C₀ * cfg.δ ^ (1 - 2 * cfg.exscal + cfg.η)) * cfg.δ ^ (cfg.exscal - cfg.η) := by
          rw [hsplit, mul_assoc]
      _ ≤ 6 * cfg.δ ^ (cfg.exscal - cfg.η) := by
          gcongr
          calc bd.C₀ * cfg.δ ^ (1 - 2 * cfg.exscal + cfg.η) ≤ bd.C₀ * (6 / bd.C₀) := by gcongr
            _ = 6 := mul_div_cancel₀ (6 : NNReal) hC₀pos.ne'
      _ ≤ cfg.ckt.wρ := cfg.ckt.hδrad
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
    have := hfull' ((cfg.δ ^ (9 * cfg.η) : NNReal) : ENNReal) ((τ ^ cfg.ckt.wη : NNReal) : ENNReal)
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

/-- **The Katz–Tao estimate at `Cmp = bd.C₀`, `∀ᶠ δ`** (T10, route R15): for every small `δ`,
every configuration at `(δ, β, η, exscal, ϱ)` with `b = δ` and every `bd` with `bd.C₀ = C₀bd`
satisfies `cfg.KTRho2ScaleData bd (4ϱ) (9·cfg.η) (3ϱ)`.

**This is no longer conjunct 4** of `Kakeya.VeryNotSticky.SideDataObligations`: since re-cut R5
the conjunct is read at `Kakeya.VeryNotSticky.latticeRescaleConstant bd.C₀`, and
`Kakeya.VeryNotSticky.eventually_ktRho2ScaleDataAt_degenerate`
(`Kakeya.DimensionThree.MainLemma2.SlabMultKTGeneral`) is what discharges it. The theorem is
retained: it is the `Cmp = bd.C₀` instance and nothing about it changed. The four thresholds of
`Kakeya.VeryNotSticky.ktRho2ScaleData_of_ckt` are arranged by
`Kakeya.VeryNotSticky.eventually_rpow_le_of_pos_nnreal` from the `δ`-free data `C₀bd`,
`exscal ≤ 1/2`, `η > 0`, `ϱ > 0`. The pin `cfg.β = β` is carried for the consumer and not read. -/
theorem eventually_ktRho2ScaleData_degenerate {β exscal ϱ η : ℝ} (hη : 0 < η) (hϱ : 0 < ϱ)
    (hϱ1 : ϱ ≤ 1) (hexscal12 : exscal ≤ 1 / 2) (C₀bd : NNReal) (hC₀ : 1 ≤ C₀bd) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      cfg.KTRho2ScaleData bd (4 * cfg.ϱ) (9 * cfg.η) (3 * cfg.ϱ) := by
  have hC₀pos : (0 : NNReal) < C₀bd := lt_of_lt_of_le zero_lt_one hC₀
  have hKpos : (0 : NNReal) < ktRho2EnclosureConstant C₀bd :=
    lt_of_lt_of_le zero_lt_one (one_le_ktRho2EnclosureConstant hC₀)
  have hT1 := eventually_rpow_le_of_pos_nnreal (a := 1 - exscal) (by linarith)
    (c := (8 * C₀bd)⁻¹) (by positivity)
  have hT2 := eventually_rpow_le_of_pos_nnreal (a := 1 - 2 * exscal + η) (by linarith)
    (c := 6 / C₀bd) (div_pos (by norm_num) hC₀pos)
  have hT3 := eventually_rpow_le_of_pos_nnreal hη (c := (ktRho2EnclosureConstant C₀bd)⁻¹)
    (by positivity)
  have hT4 := eventually_rpow_le_of_pos_nnreal (half_pos hϱ)
    (c := (ktRho2EnclosureConstant C₀bd)⁻¹) (by positivity)
  filter_upwards [hT1, hT2, hT3, hT4] with δ h1 h2 h3 h4
  intro cfg bd hδ _hβ hη' hex hϱ' hb hC₀'
  subst hδ hη' hex hϱ' hC₀'
  exact ktRho2ScaleData_of_ckt cfg bd hb hexscal12 hϱ1 h1 h2 h3 h4

/-! ### `SlabMultKT` -/

/-- **The four-field `Kakeya.VeryNotSticky.SlabMultKT`** at `η₁ := 9 * cfg.η`: the
`fullness_threshold` is `le_rfl`, the `estimate` is the input (conjunct 4 above), and the
`densityConstant` is the threshold `tangentialSlabDecompConstant tc.C ≤ δ^{-η}` — T6's third
conjunct (conjunct 2 of `SideDataObligations`), taken here as a hypothesis. This is the
producer of the `slabMult` component of `Kakeya.VeryNotSticky.TangentialInputs` on the
degenerate path. -/
def slabMultKTOfThresholds (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd)
    (hest : cfg.KTRho2ScaleDataAt bd (latticeRescaleConstant bd.C₀)
      (4 * cfg.ϱ) (9 * cfg.η) (3 * cfg.ϱ))
    (hdens : ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-cfg.η)) :
    SlabMultKT cfg tc :=
  { η₁ := 9 * cfg.η
    fullness_threshold := le_rfl
    estimate := hest
    densityConstant := hdens }

/-- The threshold of `Kakeya.VeryNotSticky.slabMultKTOfThresholds` is `9 * cfg.η`. -/
theorem slabMultKTOfThresholds_η₁ (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd)
    (hest : cfg.KTRho2ScaleDataAt bd (latticeRescaleConstant bd.C₀)
      (4 * cfg.ϱ) (9 * cfg.η) (3 * cfg.ϱ))
    (hdens : ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-cfg.η)) :
    (slabMultKTOfThresholds cfg tc hest hdens).η₁ = 9 * cfg.η := rfl

/-! The `∀ᶠ δ` producer of `Kakeya.VeryNotSticky.SlabMultKT` on the degenerate path, and the
tripwires against conjunct 4 of `Kakeya.VeryNotSticky.SideDataObligations`, live in
`Kakeya.DimensionThree.MainLemma2.SlabMultKTGeneral`: since re-cut R5 the conjunct is read at
`Kakeya.VeryNotSticky.latticeRescaleConstant bd.C₀`, and the general-`Cmp` chain that proves
it at those unchanged exponents needs `Kakeya.VeryNotSticky.rho2_le_rpow_exscal` and
`Kakeya.VeryNotSticky.delta_le_rho2_general`, which are declared downstream of this file. -/

end Kakeya.VeryNotSticky
