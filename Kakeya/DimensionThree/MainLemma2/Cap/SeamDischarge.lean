/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Cap.Wiring
public import Kakeya.DimensionThree.MainLemma2.Cap.Rescale
public import Kakeya.DimensionThree.MainLemma2.Cap.ColumnGeometry

/-!
# Discharging the cap-rescaling seam (band item A7, part 3)

`Kakeya.ML2Cap.CapSeamOn` is the one hypothesis `Cap/Scheme.lean` leaves open. This file
discharges it, by composing

* the A4-to-A5 column bridge, `Kakeya.CapColumn.exists_column_localisation`, and
* band item A5's cap rescaling, `Kakeya.CapRescale.exists_capRescaledFamily`,

and doing the three pieces of bookkeeping that neither of them owns: the `ℝ≥0∞` arithmetic of the
threshold `t = λ / (8 C_P · 18)`, the transport of `ConvexSpaceBody.IsKatzTao` to the rescaled
family, and `v.card ≤ u.card`.

## The constants

`K_c = 16`, `C₁ = Kakeya.CapRescale.capLoss`, and `c₁` is left abstract with the single
inequality `c₁ ≤ capLoss⁻¹ / (8 C_P) / 18` (`Kakeya.ML2Cap.capSeamOn_of_column`); a positive such
`c₁` exists (`Kakeya.ML2Cap.exists_capFullness`). Keeping `c₁` abstract is deliberate: it puts
the whole `ℝ≥0∞`-versus-`ℝ≥0` friction — `Kakeya.ML2Cap.LevelData.full` is an `ℝ≥0` while
`Kakeya.ML2Cap.CapSeam`'s fullness clause is in `ℝ≥0∞` — into one small lemma, and leaves the
discharge itself pure monotonicity.

## Where the scale identity is

`Kakeya.ML2Cap.capScaleStep_eq_capScale` is the one identity that makes the two halves meet:
`capScaleStep 16 c d = Kakeya.CapRescale.capScale (4 d^c) d`, i.e. the scheme's step **is** A5's
output scale at cap radius `4 d^c`. It is `4 · (4 x) = 16 x` and nothing more, but it is the
place where a mismatch would have hidden.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology ConvexSpaceBody Module
open scoped NNReal ENNReal

namespace Kakeya.ML2Cap

open Kakeya.CapBroadNarrow Kakeya.CapRescale Kakeya.CapColumn

universe u v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## 1. The scale identity -/

/-- **The scheme's scale step is A5's output scale at cap radius `4 d^c`.** -/
theorem capScaleStep_eq_capScale (c : ℝ) (d : NNReal) :
    capScaleStep 16 c d = capScale (4 * d ^ c) d := by
  rw [capScaleStep, capScale]
  congr 1
  ring

/-! ## 2. The fullness constant -/

/-- **A positive fullness constant for the composed seam exists.**  `c₁` has to satisfy
`c₁ ≤ capLoss⁻¹ / (8 C_P) / 18`, and the right-hand side is a positive, finite `ℝ≥0∞` because
`Kakeya.CapRescale.capLoss` is a nonzero `ℝ≥0` and `Kakeya.CapBroadNarrow.capPackingConst` is
finite and nonzero. -/
theorem exists_capFullness (hCP : capPackingConst E ≠ 0) :
    ∃ c₁ : NNReal, 0 < c₁ ∧ c₁ ≤ 1 ∧
      (c₁ : ENNReal) ≤ (capLoss : ENNReal)⁻¹ / (8 * capPackingConst E) / 18 := by
  have hLne : (capLoss : ENNReal) ≠ 0 := by
    simp only [ne_eq, ENNReal.coe_eq_zero]
    exact capLoss_ne_zero
  have hinv0 : (capLoss : ENNReal)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  have hinvtop : (capLoss : ENNReal)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hLne
  have hdenne : (8 : ENNReal) * capPackingConst E ≠ 0 := by
    exact mul_ne_zero (by norm_num) hCP
  have hdentop : (8 : ENNReal) * capPackingConst E ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) capPackingConst_ne_top
  set R : ENNReal := (capLoss : ENNReal)⁻¹ / (8 * capPackingConst E) / 18 with hR
  have h1ne : (capLoss : ENNReal)⁻¹ / (8 * capPackingConst E) ≠ 0 :=
    ne_of_gt (ENNReal.div_pos hinv0 hdentop)
  have hR0 : R ≠ 0 := ne_of_gt (ENNReal.div_pos h1ne (by norm_num))
  have hRtop : R ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.div_ne_top hinvtop hdenne) (by norm_num)
  refine ⟨min 1 R.toNNReal,
    lt_min zero_lt_one (ENNReal.toNNReal_pos hR0 hRtop), min_le_left _ _, ?_⟩
  calc ((min 1 R.toNNReal : NNReal) : ENNReal) ≤ ((R.toNNReal : NNReal) : ENNReal) := by
        exact_mod_cast min_le_right (1 : NNReal) R.toNNReal
    _ = R := ENNReal.coe_toNNReal hRtop

/-! ## 3. The multiplicity conclusion, with the scale cast eliminated -/

/-- **The conclusion of `Kakeya.ML2Cap.CapSeam`, assembled.**

Stated with the next level's scale as a *bound variable* `σ` and the equation
`L'.scale = σ` as a hypothesis, so that the dependent cast between
`ShadedTube (capScale θ δ) E` and `ShadedTube L'.scale E` is discharged by one `subst` rather
than by a transport.  The three bookkeeping facts the composition owes
`Kakeya.ML2Cap.CapSeam` are its three middle hypotheses: `hkt'` (band item A5 delivers
`Kakeya.maxDensity`, and `ConvexSpaceBody.IsKatzTao` is that by definition), `hfull'`, and
`hvu` — which is where `v.card ≤ u.card`, and with it `CapSeam`'s `u.card ^ γ`, is existing. -/
theorem seam_conclusion {L L' : LevelData} {γ : ℝ} {σ : NNReal}
    (hsc : L'.scale = σ) (hγ0 : 0 ≤ γ) (hnext : L'.Holds.{u} E γ)
    {ι : Type u} (u v : Finset ι) (W Wc : ι → ShadedTube L.scale E) (T' : ι → ShadedTube σ E)
    (hvu : v ⊆ u)
    (hball' : ∀ i ∈ v, (T' i).carrier ⊆ closedBall (0 : E) 1)
    (hkt' : IsKatzTao v (fun i => (T' i).toConvexSpaceBody) L'.ktBound)
    (hfull' : L'.full ≤ ShadedBody.fullness v (fun i => (T' i).toShadedBody))
    (hmulteq : ShadedBody.multiplicity v (fun i => (T' i).toShadedBody)
      = ShadedBody.multiplicity v (fun i => (Wc i).toShadedBody))
    (hmult : ShadedBody.multiplicity u (fun i => (W i).toShadedBody)
      ≤ 2 * ShadedBody.multiplicity v (fun i => (Wc i).toShadedBody)) :
    ShadedBody.multiplicity u (fun i => (W i).toShadedBody)
      ≤ 2 * (L'.factor * (u.card : ENNReal) ^ γ) := by
  subst hsc
  have hinner := hnext v T' hball' hkt' hfull'
  have hcard : (v.card : ENNReal) ≤ (u.card : ENNReal) :=
    Nat.cast_le.mpr (Finset.card_le_card hvu)
  calc ShadedBody.multiplicity u (fun i => (W i).toShadedBody)
      ≤ 2 * ShadedBody.multiplicity v (fun i => (Wc i).toShadedBody) := hmult
    _ = 2 * ShadedBody.multiplicity v (fun i => (T' i).toShadedBody) := by rw [hmulteq]
    _ ≤ 2 * (L'.factor * (v.card : ENNReal) ^ γ) := by gcongr
    _ ≤ 2 * (L'.factor * (u.card : ENNReal) ^ γ) := by gcongr

/-! ## 4. The seam, discharged -/

/-- **`Kakeya.ML2Cap.CapSeamOn` is discharged by the column bridge composed with A5.**

The three constants are `K_c = 16` (`Kakeya.ML2Cap.capScaleStep_eq_capScale`),
`C₁ = Kakeya.CapRescale.capLoss` (A5's `Δ_max` loss) and `c₁` abstract, subject only to
`c₁ ≤ capLoss⁻¹ / (8 C_P) / 18`, which `Kakeya.ML2Cap.exists_capFullness` shows is satisfiable by
a positive `c₁ ≤ 1`.

Everything the two halves need is available: A5's `θ ≤ 1` is `Kakeya.ML2Cap.CapSeamOn`'s
`4 δ_k^c ≤ 1` clause, the column bridge's `4 δ ≤ θ` and A5's `δ ≤ θ` are both free from
`δ_k ≤ 1` and `c ≤ 1`, and the threshold `18 t ≤ λ` is `CapSeam`'s own fullness binder with
`t = λ / (8 C_P) / 18`, so no inequality slack is spent anywhere. -/
theorem capSeamOn_of_column (hn : finrank ℝ E = 3) {γ c : ℝ} {c₁ : NNReal}
    (hc1 : c ≤ 1) (hγ0 : 0 ≤ γ)
    (hc₁le : (c₁ : ENNReal) ≤ (capLoss : ENNReal)⁻¹ / (8 * capPackingConst E) / 18) :
    CapSeamOn.{u} E γ c 16 capLoss c₁ := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hn]; norm_num)
  intro L L' hδ0 hδ1 hfull0 hrad hscale hkt hfl ι u W p hp hball hdir hKT hfullness hnext
  have hδ0r : (0 : ℝ) < (L.scale : ℝ) := NNReal.coe_pos.mpr hδ0
  have hδ1r : (L.scale : ℝ) ≤ 1 := NNReal.coe_le_one.mpr hδ1
  -- the cap radius, as an `ℝ≥0`
  set θ : NNReal := 4 * L.scale ^ c with hθdef
  have hθcoe : (θ : ℝ) = 4 * (L.scale : ℝ) ^ c := by
    rw [hθdef]; push_cast [NNReal.coe_rpow]; ring
  have hθ0 : 0 < θ := by
    rw [hθdef]; exact mul_pos (by norm_num) (NNReal.rpow_pos hδ0)
  have hθ0r : (0 : ℝ) < (θ : ℝ) := NNReal.coe_pos.mpr hθ0
  have hθ1 : θ ≤ 1 := by
    have h : (θ : ℝ) ≤ 1 := by rw [hθcoe]; exact hrad
    exact_mod_cast h
  -- `4 δ ≤ θ` for the column bridge, and `δ ≤ θ` for A5: both free
  have hpow : (L.scale : ℝ) ≤ (L.scale : ℝ) ^ c := by
    have h := Real.rpow_le_rpow_of_exponent_ge hδ0r hδ1r hc1
    simpa using h
  have hδθ4 : 4 * (L.scale : ℝ) ≤ (θ : ℝ) := by rw [hθcoe]; linarith
  have hδθ : L.scale ≤ θ := by
    have h : (L.scale : ℝ) ≤ (θ : ℝ) := by linarith
    exact_mod_cast h
  -- the threshold `t = λ / (8 C_P) / 18`, and the `ℝ≥0∞` bookkeeping
  have hfullne : (L.full : ENNReal) ≠ 0 := by
    simp only [ne_eq, ENNReal.coe_eq_zero]; exact ne_of_gt hfull0
  have hdentop : (8 : ENNReal) * capPackingConst E ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) capPackingConst_ne_top
  set t : ENNReal := (L.full : ENNReal) / (8 * capPackingConst E) / 18 with htdef
  have ht0 : 0 < t := by
    rw [htdef]
    exact ENNReal.div_pos (ne_of_gt (ENNReal.div_pos hfullne hdentop)) (by norm_num)
  have hthr : 18 * t ≤ (ShadedBody.fullness u (fun i => (W i).toShadedBody) : ENNReal) := by
    rw [htdef, mul_comm, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
    exact hfullness
  have hposfull : 0 < ShadedBody.fullness u (fun i => (W i).toShadedBody) := by
    have h18 : (0 : ENNReal) < 18 * t :=
      ENNReal.mul_pos (by norm_num) (ne_of_gt ht0)
    have h : (0 : ENNReal) < (ShadedBody.fullness u (fun i => (W i).toShadedBody) : ENNReal) :=
      lt_of_lt_of_le h18 hthr
    exact_mod_cast h
  have hM : (∑ i ∈ u, volume (W i).shade) ≠ 0 :=
    ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos u _ hposfull
  -- the A4-to-A5 column bridge
  obtain ⟨v, b, Y, hY, hvu, hb, hdir', hball', hcol', hfullv, hmult⟩ :=
    exists_column_localisation hn hθ0r hp hδθ4 u W
      (fun i hi => by rw [hθcoe]; exact hdir i hi) hball hthr hM
  -- A5's cap rescaling
  have hcolumn : IsCapColumn (capRefTube θ b hp) v (capShadeFam W Y hY) :=
    isCapColumn_capRefTube hp hb hdir' hcol' hball'
  obtain ⟨T', hT'ball, hT'mult, hT'full, hT'max⟩ :=
    exists_capRescaledFamily hn hθ0 hθ1 hδ0 hδθ (capRefTube θ b hp) hcolumn
  -- the scale identity
  have hsc : L'.scale = capScale θ L.scale := by
    rw [hscale, capScaleStep_eq_capScale, hθdef]
  -- item (b): `IsKatzTao` transport
  have hktv : Kakeya.maxDensity v (fun i => (W i).toConvexSpaceBody) ≤ L.ktBound :=
    hKT.subset hvu
  have hkt' : IsKatzTao v (fun i => (T' i).toConvexSpaceBody) L'.ktBound := by
    rw [IsKatzTao_def, hkt]
    refine hT'max.trans ?_
    have hbodies : (fun i => (capShadeFam W Y hY i).toConvexSpaceBody)
        = fun i => (W i).toConvexSpaceBody := rfl
    rw [hbodies]
    gcongr
  -- the fullness bookkeeping
  have hfull' : L'.full ≤ ShadedBody.fullness v (fun i => (T' i).toShadedBody) := by
    have hstep : ((c₁ : ENNReal)) * (L.full : ENNReal) ≤ (capLoss : ENNReal)⁻¹ * t := by
      have hmono : ((c₁ : ENNReal)) * (L.full : ENNReal)
          ≤ ((capLoss : ENNReal)⁻¹ / (8 * capPackingConst E) / 18) * (L.full : ENNReal) := by
        gcongr
      refine le_trans hmono ?_
      rw [htdef]
      simp only [div_eq_mul_inv]
      ring_nf
      exact le_rfl
    have hchain : ((L'.full : NNReal) : ENNReal)
        ≤ (ShadedBody.fullness v (fun i => (T' i).toShadedBody) : ENNReal) := by
      calc ((L'.full : NNReal) : ENNReal) = ((c₁ : ENNReal)) * (L.full : ENNReal) := by
            rw [hfl]; push_cast; ring
        _ ≤ (capLoss : ENNReal)⁻¹ * t := hstep
        _ ≤ (capLoss : ENNReal)⁻¹ * (ShadedBody.fullness v
              (fun i => (capShadeFam W Y hY i).toShadedBody) : ENNReal) := by gcongr
        _ ≤ _ := hT'full
    exact_mod_cast hchain
  exact seam_conclusion hsc hγ0 hnext u v W (capShadeFam W Y hY) T' hvu hT'ball hkt' hfull'
    hT'mult hmult

/-! ## 5. The packing constant is nonzero, and the seam holds outright -/

/-- `C_P ≠ 0`.  Each of the three factors of `Kakeya.CapBroadNarrow.capBranchConst` is nonzero:
the covering constant is a finite `ℝ≥0`, so its inverse is nonzero; `10^d > 0`; and the unit ball
has positive volume. -/
theorem capPackingConst_ne_zero [Nontrivial E] : capPackingConst E ≠ 0 := by
  rw [capPackingConst, capBranchConst]
  refine mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
  · exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  · exact ne_of_gt (measure_ball_pos volume 0 one_pos)

/-- **The seam of band item A6 holds outright in `ℝ³`.**  The witness `c₁` is
`min 1 ((capLoss⁻¹ / (8 C_P) / 18).toNNReal)`. -/
theorem exists_capSeamAll :
    ∃ c₁ : NNReal, 0 < c₁ ∧ c₁ ≤ 1 ∧ CapSeamAll.{u} 16 capLoss c₁ := by
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  haveI : Nontrivial (EuclideanSpace ℝ (Fin 3)) :=
    Module.nontrivial_of_finrank_pos (by rw [hn]; norm_num)
  obtain ⟨c₁, hc₁0, hc₁1, hc₁le⟩ :=
    exists_capFullness (E := EuclideanSpace ℝ (Fin 3)) capPackingConst_ne_zero
  refine ⟨c₁, hc₁0, hc₁1, ?_⟩
  intro γ hγ0 hγ1
  exact capSeamOn_of_column hn (by linarith) hγ0.le hc₁le

/-! ## 6. The Cap Lemma and the route to Main Lemma 2, with the seam discharged -/

/-- **The Cap Lemma `L(γ) ⇒ K_KT(γ)` in `ℝ³`, unconditionally.**

's `katzTaoEstimate_of_largeOne`, with band items A0--A7 and the
A4-to-A5 column bridge composed and nothing assumed. -/
theorem katzTaoEstimate_of_largeOne {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hL : KatzTaoEstimateLargeOne.{u} (EuclideanSpace ℝ (Fin 3)) γ) :
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ := by
  obtain ⟨c₁, hc₁0, hc₁1, hseam⟩ := exists_capSeamAll.{u}
  exact katzTaoEstimate_of_largeOne_three hγ0 hγ1 (by norm_num) one_le_capLoss hc₁0 hc₁1
    (hseam γ hγ0 hγ1) hL

/-- **`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` with `hsmall` deleted and nothing
assumed in its place.** -/
theorem katzTaoEstimate_sub_of_dichotomy_free {β g η c : ℝ}
    (hc : 0 < c) (hcβ : 2 * c ≤ β) (hβ1 : β - c ≤ 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hdich : ML2Assembly.Dichotomy.{u} β (β / 2) g η) :
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) := by
  obtain ⟨c₁, hc₁0, hc₁1, hseam⟩ := exists_capSeamAll.{u}
  exact katzTaoEstimate_sub_of_dichotomy' (by norm_num) one_le_capLoss hc₁0 hc₁1 hc hcβ hβ1
    hη0 hη1 hg (hseam (β - c) (by linarith) hβ1) hdich

/-- **The pointwise drop from the geometric core, and nothing else.** -/
theorem pointwiseDrop_of_geometricCoreAt_free (hcore : ML2Assembly.GeometricCoreAt.{u}) :
    ML2Assembly.PointwiseDrop.{u} := by
  obtain ⟨c₁, hc₁0, hc₁1, hseam⟩ := exists_capSeamAll.{u}
  exact pointwiseDrop_of_geometricCoreAt (by norm_num) one_le_capLoss hc₁0 hc₁1 hseam hcore

/-- **`Kakeya.ML2Assembly.GeometricCoreAt` ⟹ the conclusion of the protected Main Lemma 2, with
no other hypothesis.**

This is the band's endpoint: `Kakeya.VNSUniform.MainLemma2Statement` — a **pre-existing** `Prop`,
pinned to `Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate` by the tripwires of
`Kakeya/DimensionThree/MainLemma2Ptw.lean` — from the single geometric obligation.  No protected
text changes and no cardinality clause is added anywhere.

It is **not** a proof of Main Lemma 2: `Kakeya.ML2Assembly.GeometricCoreAt` has no producer in
the tree, and GWZ Lemma 9.1 (`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`) is consumed by
the pointwise route as a term. -/
theorem mainLemma2Statement_of_geometricCoreAt_free
    (hcore : ML2Assembly.GeometricCoreAt.{u}) : VNSUniform.MainLemma2Statement.{u} :=
  VNSUniform.mainLemma2Statement_of_pointwise_drop.{u}
    (pointwiseDrop_of_geometricCoreAt_free hcore)

/-- **The padding lemma of `Kakeya.ML2Large.padding_iff_small`, at the `δ^{-1}` threshold,
discharged.** -/
theorem largeOne_padding {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    KatzTaoEstimateLargeOne.{u} (EuclideanSpace ℝ (Fin 3)) γ →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ :=
  katzTaoEstimate_of_largeOne hγ0 hγ1

end Kakeya.ML2Cap

end
