/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.Clump
public import Kakeya.MultiScaleFac.StoppingA
public import Kakeya.MultiScaleFac.StoppingKT

/-!
# The paired band and the stopping time that carries it

`Kakeya.MultiScaleFac.PairBandOn` and the self-banding pass that establishes it, together with the
stopping time whose terminal family carries a band on its own grid-uniform cover.

This module is the merge of the former `Bullet3Band`, `Bullet3BandStopping`.  Each keeps its own
section, so its file-level `open`s and `variable`s stay confined to it.

## The banded pass of the Frostman stopping time

The half-(A) stopping time
`Kakeya.MultiScaleFac.exists_maximal_cuts_state_instance_hoisted_blocks_quad`
carries an abstract invariant `Inv : ℕ → Finset ι → Prop` and asks its caller for a **pass** that
restores the invariant on a subfamily, at a displayed cardinality cost, a displayed per-anchor
fibre-retention ratio, and *at the grid-uniform constant of the state*.  This section builds that
pass out of the paired homogenizing pass
`Kakeya.Homogenize.exists_homogenizing_pass_gridUniform`.

## Why the invariant is a statement about a superfamily

The paired pass returns a grid-uniform system at the inflated constant
`Kakeya.MultiScaleFac.gridUniformBandConst C 2`, never at `C`.  The state of the stopping time is
read at one fixed constant `Cv`, so the inflation has to be undone, and the only way to undo it is
to re-uniformize, by `Kakeya.MultiScaleFac.exists_uniformize_subfamily_hoisted`, which returns the
canonical constant whatever it is handed.  Re-uniformizing deletes members, and deleting members
lowers `Kakeya.maxDensity`, so the *lower* half of the band established by the pass does not
survive on the family that the stopping time carries forward.

What does survive is the band on the family the pass produced, together with the inclusion and the
cardinality proportion relating it to the family carried forward.  That is the content of
`Kakeya.MultiScaleFac.BandedSuper`, and it is the strongest invariant a pass of this shape can
maintain.

## The displayed cost

The paired pass costs `(1 - log δ)^{2 (M+2)(M+1)}`, an exponent *quadratic* in the grid length,
because it homogenizes one band for every pair of grid levels.  The re-uniformization costs a
further `A^{M+1} (1 - log δ)^{K (M+1)}`.  Both are displayed here in the single shape
`A^{M+1} (1 - log δ)^{K (M+2)(M+1)}`.

This is *one factor of `M + 2` more* than the budget
`A^{M+1} (1 - log δ)^{K (M+1)}` that
The abstract pass of
`Kakeya.MultiScaleFac.exists_maximal_cuts_state_instance_hoisted_blocks_quad` displays that budget,
and no choice of the constants `A, K`, which are quantified before `δ` and before the grid
length, closes that gap.  The engine's pass budget therefore has to be widened to the quadratic
shape before the pass built here can be handed to it; nothing else in the engine is affected, since
`Kakeya.MultiScaleFac.gridLoss` carries a quadratic polylogarithmic exponent already and
`Kakeya.Homogenize.polylog_pow_le_gridLoss` absorbs the wider loss exactly as it absorbs the
narrower one.

## The order of the per-anchor constant

The per-anchor retention ratio is read off `Kakeya.MultiScaleFac.card_fibreIndex_le_mul_of_card_le`,
whose constant is a power of the grid-uniform constant of the **larger** family, that is of the
state constant `Cv`.  The pass built here therefore fixes its per-anchor constant only after `Cv` is
known, whereas
`Kakeya.MultiScaleFac.exists_maximal_cuts_state_instance_hoisted_blocks_quad` takes it as a
parameter fixed before `Cv` is produced.  This is the second place where the engine's abstract pass
interface has to be widened; both widenings are changes of quantifier order and of a displayed
exponent, and neither touches the run of the stopping time.

## The half-(A) stopping time carrying a band

`Kakeya/MultiScaleFac/Band.lean` builds the banded pass
`Kakeya.StickyKakeya.exists_banded_pass_gridUniform`, and
`Kakeya/MultiScaleFac/StoppingA.lean` runs the half-(A) stopping time with an abstract state
invariant at the two budgets that pass meets.  This section is the single instantiation that joins
them: the invariant is `Kakeya.MultiScaleFac.BandedSuper`, the pass is the banded pass, and the
result is a stopping time whose terminal family carries a band.

Nothing here is new mathematics.  The only step with content is the comparison of the two per-anchor
coefficients, which is `Kakeya.MultiScaleFac.passRatio_const_le`: the pass displays its ratio as a
constant times the real cardinality loss `A_pass^{M+1} W`, and the engine asks for a constant raised
to the power `M + 1` times `W`, so the base `A_pass` is absorbed into the constant.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The invariant maintained by a banded pass -/

/-- **A family sitting inside a banded family of comparable size** (blueprint `def:bandedSuper`).
`t` is a subfamily of a family `u` of size at most `Λ |t|` carrying a grid-uniform system with the
paired band `Φ` of `Kakeya.Homogenize.exists_homogenizing_pass_gridUniform`.  The band is asserted
of `u` and not of `t`, since its lower half is not inherited by subfamilies. -/
def BandedSuper {ι : Type*} {δ : NNReal} (t : Finset ι) (T : ι → Tube δ E) (M : ℕ)
    (Cb : NNReal) (Λ : ℝ) : Prop :=
  ∃ (u : Finset ι) (𝒢 : GridUniform u T M Cb) (Φ : ℕ → ℕ → ENNReal),
    t ⊆ u ∧ (u.card : ℝ) ≤ Λ * (t.card : ℝ) ∧ PairBandOn u 𝒢 2 Φ M

/-! ### The per-anchor fibre ratio of a sub-system -/

/-- A real product inequality between two natural cardinalities lifts to `ENNReal`. -/
private lemma ofReal_mul_coe_le {n m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h : (n : ℝ) ≤ c * (m : ℝ)) :
    (n : ENNReal) ≤ ENNReal.ofReal c * (m : ENNReal) := by
  rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal h

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A global proportion between two nested grid-uniform sub-systems is a proportion in every
fibre, at every grid index** (blueprint `lem:fibreRatioSubsystem`).  The grid-indexed,
`ENNReal`-valued form of `Kakeya.MultiScaleFac.card_fibreIndex_le_mul_of_card_le`, with the two
fibres compared at the *same* radius `gridScale δ M a`. -/
theorem exists_fibre_ratio_of_subsystem (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ Cr : NNReal, 1 ≤ Cr ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 →
      ∀ (M : ℕ) (t t' : Finset ι) (T : ι → Tube δ E), t' ⊆ t →
      ∀ (𝒢 : GridUniform t T M Cu) (𝒢' : GridUniform t' T M Cu),
      (∀ k (hk : k ≤ M), (𝒢'.uniformAt k hk).parent ⊆ (𝒢.uniformAt k hk).parent) →
      ComparableFibreCountsInflated t' T (gridScales δ M) Cu →
      ∀ A : ℝ, 1 ≤ A → (t.card : ℝ) ≤ A * (t'.card : ℝ) →
      ∀ i₀ ∈ t', ∀ a ≤ M,
        ((fibreIndex t T δ (gridScale δ M a) i₀).card : ENNReal)
          ≤ (Cr : ENNReal) * ENNReal.ofReal A
              * ((fibreIndex t' T δ (gridScale δ M a) i₀).card : ENNReal) := by
  refine ⟨Cu ^ 7, one_le_pow₀ hCu, ?_⟩
  classical
  intro ι δ hδ hδ1 M t t' T htt' 𝒢 𝒢' hpsub hcomp A hA1 hA i₀ hi₀ a ha
  set ρ : NNReal := gridScale δ M a with hρ
  have hδ1nn : (δ : NNReal) ≤ 1 := by exact_mod_cast hδ1
  have hδr : δ ≤ ρ := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp [hρ, gridScale, hδ1nn]
    · simpa [hρ, gridScale_self δ hM] using gridScale_antitone hδ hδ1nn M ha
  have hA0 : (0 : ℝ) ≤ A := zero_le_one.trans hA1
  have hCu0 : (0 : ℝ) ≤ (Cu : ℝ) := Cu.coe_nonneg
  have hcmpR : ((fibreIndex t' T δ (4 * ρ) i₀).card : ℝ)
      ≤ (Cu : ℝ) * ((fibreIndex t' T δ ρ i₀).card : ℝ) := by
    exact_mod_cast hcomp ρ (by rw [hρ]; exact gridScale_mem_gridScales δ ha) i₀ hi₀ i₀ hi₀
  have hmain : ((fibreIndex t T δ ρ i₀).card : ℝ)
      ≤ (Cu : ℝ) ^ 7 * A * ((fibreIndex t' T δ ρ i₀).card : ℝ) := by
    calc
      ((fibreIndex t T δ ρ i₀).card : ℝ)
          ≤ (Cu : ℝ) ^ 6 * A * ((fibreIndex t' T δ (4 * ρ) i₀).card : ℝ) :=
            card_fibreIndex_le_mul_of_card_le_four (𝒢.uniformAt a ha) (𝒢'.uniformAt a ha)
              htt' hδr (by exact_mod_cast Finset.card_le_card (hpsub a ha)) hA1 hA hi₀
      _ ≤ (Cu : ℝ) ^ 6 * A * ((Cu : ℝ) * ((fibreIndex t' T δ ρ i₀).card : ℝ)) :=
            mul_le_mul_of_nonneg_left hcmpR (mul_nonneg (pow_nonneg hCu0 6) hA0)
      _ = (Cu : ℝ) ^ 7 * A * ((fibreIndex t' T δ ρ i₀).card : ℝ) := by ring
  have hfin := ofReal_mul_coe_le (mul_nonneg (pow_nonneg hCu0 7) hA0) hmain
  rwa [ENNReal.ofReal_mul (pow_nonneg hCu0 7), ← NNReal.coe_pow,
    ENNReal.ofReal_coe_nnreal] at hfin

/-! ### The banded pass -/

/-! ### The banded pass with the band on the family itself -/

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The bundle-level band constant dominates the constant it inflates. -/
theorem le_gridUniformBandConst {C A : NNReal} : C ≤ gridUniformBandConst (E := E) C A :=
  (le_max_of_le_left (le_max_left C _)).trans
    (le_self_pow one_le_bandRestrictConst two_ne_zero)

/-- **One banded pass of the Frostman stopping time, with the band on the produced family**
(blueprint `lem:bandedPassSelfBand`).  The two operations of
`Kakeya.StickyKakeya.exists_banded_pass_gridUniform` composed in the *opposite* order —
re-uniformize first, homogenize second — so that the band is read on the family the pass returns.
The price of the reordering is paid in the floor constant, not in cardinality. -/
theorem exists_banded_pass_gridUniform_selfBand (hn : Module.finrank ℝ E = 3) :
    ∃ (Apass : ℝ) (Kpass : ℕ) (Cu₀ δ₀ : NNReal),
      1 ≤ Apass ∧ 1 ≤ Cu₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ Cv : NNReal, Cu₀ ≤ Cv →
      ∃ Cpass : NNReal, 1 ≤ Cpass ∧
      ∀ (M : ℕ), 0 < M →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ → (δ : ℝ) ≤ 1 →
        δ ≤ (16 : NNReal) ^ (-(M : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (↑s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      ∀ (t : Finset ι), t ⊆ s → ∀ hG : GridUniform t T M Cv,
      ∃ t' ⊆ t,
        (t.card : ℝ)
            ≤ Apass ^ (M + 1) * (1 - Real.log (δ : ℝ)) ^ (Kpass * ((M + 2) * (M + 1)))
              * (t'.card : ℝ) ∧
          ComparableFibreCounts t' T (gridScales δ M) Cv ∧
          ComparableFibreCountsInflated t' T (gridScales δ M) Cv ∧
          (∃ (𝒢' : GridUniform t' T M Cv) (Φ : ℕ → ℕ → ENNReal),
            PairBandOn t' 𝒢' 2 Φ M ∧
            (∀ k (hk : k ≤ M), (𝒢'.uniformAt k hk).parent ⊆ (hG.uniformAt k hk).parent) ∧
            BandedSuper t' T M (gridUniformBandConst (E := E) Cv 2)
              (Apass ^ (M + 1) * (1 - Real.log (δ : ℝ)) ^ (Kpass * ((M + 2) * (M + 1))))) ∧
          ∀ i₀ ∈ t', ∀ a ≤ M,
            ((fibreIndex t T δ (gridScale δ M a) i₀).card : ENNReal)
              ≤ (Cpass : ENNReal)
                  * ENNReal.ofReal (Apass ^ (M + 1)
                      * (1 - Real.log (δ : ℝ)) ^ (Kpass * ((M + 2) * (M + 1))))
                * ((fibreIndex t' T δ (gridScale δ M a) i₀).card : ENNReal) := by
  classical
  obtain ⟨d0, hd0pos, hd0le1, hpass⟩ :=
    Kakeya.Homogenize.exists_homogenizing_pass_gridUniform (E := E) hn
  obtain ⟨A1, K1, Cu1, hA1, hCu1, huni⟩ :=
    Kakeya.MultiScaleFac.exists_uniformize_subfamily_hoisted.{u, _} (E := E)
  let Cb1 : NNReal := gridUniformBandConst (E := E) Cu1 2
  let Cu0 : NNReal := comparableCuOf (E := E) Cb1
  have hCb1 : 1 ≤ Cb1 := le_trans hCu1 le_gridUniformBandConst
  have hCb1Cu0 : Cb1 ≤ Cu0 := (le_self_pow hCb1 two_ne_zero).trans le_comparableCuOf.1
  let Kpass : ℕ := 2 + K1
  refine ⟨A1, Kpass, Cu0, d0, hA1, le_trans hCb1 hCb1Cu0, hd0pos, hd0le1, ?_⟩
  intro Cv hCu0Cv
  have hCb1Cv : Cb1 ≤ Cv := le_trans hCb1Cu0 hCu0Cv
  obtain ⟨Cr, hCr1, hfibre⟩ :=
    exists_fibre_ratio_of_subsystem (E := E) Cv (le_trans hCb1 hCb1Cv)
  refine ⟨Cr, hCr1, ?_⟩
  intro M hMpos ι δ hdpos hdd0 hdle1 hd16 s T hball hED t hts hG
  set W : ℝ := 1 - Real.log (δ : ℝ) with hWdef
  have hW1 : (1 : ℝ) ≤ W :=
    Kakeya.MultiScaleFac.KT.one_le_one_sub_log (δ' := δ) hdpos hdle1
  have hWnn : (0 : ℝ) ≤ W := by linarith
  have hA1nn : (0 : ℝ) ≤ A1 := by linarith
  have hballt : ∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1 :=
    fun i hi => hball i (hts hi)
  have hEDt : (t : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) :=
    Set.Pairwise.mono (Finset.coe_subset.mpr hts) hED
  obtain ⟨t2, ht2t, hloss2, G2, hpar2, htub2, hcomp2, hcomp2i⟩ :=
    huni M hMpos hdpos hd16 t t T (Finset.Subset.refl t) hballt hEDt Cv hG
  have hEDt2 : (t2 : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) :=
    Set.Pairwise.mono (Finset.coe_subset.mpr ht2t) hEDt
  obtain ⟨t3, ht3t2, hloss3, G3, Phi, hassign3, htub3, hidx3, hband3⟩ :=
    hpass (δ := δ) (ι := ι) hdpos hdd0 M Cu1 t2 T
      (fun i hi => hball i (hts (ht2t hi))) hEDt2 G2
  have hEDt3 : (t3 : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) :=
    Set.Pairwise.mono (Finset.coe_subset.mpr ht3t2) hEDt2
  have hd1nn : (δ : NNReal) ≤ 1 := by exact_mod_cast hdle1
  have hcmp := comparableFibreCounts_of_gridUniform hdpos hd1nn hMpos hd16 G3 G3.le_card_class
    G3.clumped hEDt3
  have hcmpCv : ComparableFibreCounts t3 T (gridScales δ M) Cv :=
    ComparableFibreCounts.mono hcmp.1 hCu0Cv
  have hcmpiCv : ComparableFibreCountsInflated t3 T (gridScales δ M) Cv :=
    ComparableFibreCountsInflated.mono hcmp.2 hCu0Cv
  let G3m : GridUniform t3 T M Cv := G3.mono hCb1Cv
  have hpar : ∀ k (hk : k ≤ M), (G3m.uniformAt k hk).parent ⊆ (hG.uniformAt k hk).parent := by
    intro k hk
    refine subset_trans ?_ (hpar2 k hk)
    rw [show (G3m.uniformAt k hk).parent = (G3.uniformAt k hk).parent from rfl,
      G3.parent_eq k hk, G2.parent_eq k hk, hidx3 k hk]
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact G2.cover.assign_mem k hk i (ht3t2 hi)
  have hyX : (M + 1) ≤ (M + 2) * (M + 1) := Nat.le_mul_of_pos_left (M + 1) (by omega)
  have hExp : K1 * (M + 1) + 2 * ((M + 2) * (M + 1)) ≤ Kpass * ((M + 2) * (M + 1)) :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left K1 hyX) _).trans
      (le_of_eq (by dsimp [Kpass]; ring))
  have hWtot : W ^ (K1 * (M + 1)) * W ^ (2 * ((M + 2) * (M + 1)))
      ≤ W ^ (Kpass * ((M + 2) * (M + 1))) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hW1 hExp
  let Ap : ℝ := A1 ^ (M + 1) * W ^ (Kpass * ((M + 2) * (M + 1)))
  have hAp1 : (1 : ℝ) ≤ Ap :=
    (one_le_pow₀ hA1).trans
      (le_mul_of_one_le_right (pow_nonneg hA1nn (M + 1)) (one_le_pow₀ hW1))
  have hst3nn : (0 : ℝ) ≤ (t3.card : ℝ) := Nat.cast_nonneg _
  have hloss_tot : (t.card : ℝ)
      ≤ A1 ^ (M + 1) * W ^ (Kpass * ((M + 2) * (M + 1))) * (t3.card : ℝ) := by
    calc
      (t.card : ℝ) ≤ A1 ^ (M + 1) * W ^ (K1 * (M + 1)) * (t2.card : ℝ) := hloss2
      _ ≤ A1 ^ (M + 1) * W ^ (K1 * (M + 1)) * (W ^ (2 * ((M + 2) * (M + 1))) * (t3.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hloss3
            (mul_nonneg (pow_nonneg hA1nn (M + 1)) (pow_nonneg hWnn _))
      _ = A1 ^ (M + 1) * (W ^ (K1 * (M + 1)) * W ^ (2 * ((M + 2) * (M + 1))))
            * (t3.card : ℝ) := by ring
      _ ≤ A1 ^ (M + 1) * W ^ (Kpass * ((M + 2) * (M + 1))) * (t3.card : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hWtot (pow_nonneg hA1nn (M + 1))) hst3nn
  have hbandOn : ∀ (Cx : NNReal) (hx : Cb1 ≤ Cx), PairBandOn t3 (G3.mono hx) 2 Phi M :=
    fun _ _ a ha c hc j hj => hband3 a ha c hc j hj
  have hcst : Cb1 ≤ gridUniformBandConst (E := E) Cv 2 :=
    le_trans hCb1Cv (le_gridUniformBandConst (C := Cv) (A := 2))
  have hBS : BandedSuper t3 T M (gridUniformBandConst (E := E) Cv 2) Ap :=
    ⟨t3, G3.mono hcst, Phi, Finset.Subset.refl t3,
      le_mul_of_one_le_left hst3nn hAp1, hbandOn _ hcst⟩
  refine ⟨t3, subset_trans ht3t2 ht2t, hloss_tot, hcmpCv, hcmpiCv,
    ⟨G3m, Phi, hbandOn Cv hCb1Cv, hpar, hBS⟩, fun i0 hi0 a ha =>
      hfibre (δ := δ) hdpos hdle1 M t t3 T (subset_trans ht3t2 ht2t)
        hG G3m hpar hcmpiCv Ap hAp1 hloss_tot i0 hi0 a ha⟩

/-! ### The stopping time whose terminal family carries its own band -/

/-- **The half-(A) stopping time carrying a band on the terminal family itself** (blueprint
`lem:bandedStoppingTimeSelfBand`).  The same instantiation as
`Kakeya.StickyKakeya.exists_maximal_cuts_banded_hoisted`, run with the self-banding pass
`Kakeya.MultiScaleFac.exists_banded_pass_gridUniform_selfBand`, so that the terminal family also
carries a `PairBandOn` band read on its own grid-uniform cover. -/
theorem exists_maximal_cuts_banded_hoisted_selfBand (hn : Module.finrank ℝ E = 3) :
    ∃ (A Apass : ℝ) (K K₁ Kpass : ℕ) (Cv C₁ δ₀ : NNReal),
      1 ≤ A ∧ 1 ≤ Apass ∧ 1 ≤ Cv ∧ 1 ≤ C₁ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (N : ℕ), 4096 ≤ N → ∀ {ε : ℝ}, ε = 1 / Real.sqrt (N : ℝ) →
      ∀ (Mgrid : ℕ), 16 ≤ Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ → (δ : ℝ) ≤ 1 →
        δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (↑s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      ∀ η : ℕ → ℝ, 0 ≤ η 0 → (∀ k < N, η k ≤ ε * η (k + 1)) → η N ≤ ε →
      ConvexSpaceBody.frostmanConstant s (fibreBodies T δ) ConvexSpaceBody.closedUnitBall
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
      ∃ (S : Finset ℕ) (m L : ℕ) (Ct : NNReal) (tL : Finset ι),
        m < N ∧ L ≤ N + 1 ∧ L ≤ Mgrid + 1 ∧ 1 ≤ Ct ∧
        Ct ≤ (C₁ ^ (Mgrid + 1)
                * Real.toNNReal ((1 - Real.log (δ : ℝ))
                    ^ (K₁ * ((Mgrid + 2) * (Mgrid + 1))))) ^ L ∧
        tL ⊆ s ∧
        (s.card : ℝ)
            ≤ (2 * ((Mgrid : ℝ) + 1) * A ^ (Mgrid + 1)
                * (1 - Real.log (δ : ℝ)) ^ (K * ((Mgrid + 2) * (Mgrid + 1)))) ^ L
              * (tL.card : ℝ) ∧
        Nonempty (GridUniform tL T Mgrid Cv) ∧
        ComparableFibreCounts tL T (gridScales δ Mgrid) Cv ∧
        ComparableFibreCountsInflated tL T (gridScales δ Mgrid) Cv ∧
        (∃ (𝒢 : GridUniform tL T Mgrid Cv) (Φ : ℕ → ℕ → ENNReal),
          PairBandOn tL 𝒢 2 Φ Mgrid ∧
            BandedSuper tL T Mgrid (gridUniformBandConst (E := E) Cv 2)
              (Apass ^ (Mgrid + 1)
                * (1 - Real.log (δ : ℝ)) ^ (Kpass * ((Mgrid + 2) * (Mgrid + 1))))) ∧
        0 ∈ S ∧ Mgrid ∈ S ∧ S ⊆ Finset.range (Mgrid + 1) ∧ S.card = m + 2 ∧
        (∀ i₀ ∈ tL,
          ConvexSpaceBody.frostmanConstant (fibreIndex tL T δ 1 i₀) (fibreBodies T δ)
              ((T i₀).rescale 1).toConvexSpaceBody
            ≤ (Ct : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(η m)))) ∧
        ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
          BlockFrostman tL T Mgrid Ct (η m) a b ∧
            (¬ IsLongBlock Mgrid ε a b ∨
              ¬ (tL.card ≤ 2 * (passingNodes tL T Mgrid Ct ε (η (m + 1)) a b).card)) := by
  classical
  obtain ⟨Apass, Kpass, Cu0, d0, hApass, hCu0, hd0pos, hd0le1, hband⟩ :=
    exists_banded_pass_gridUniform_selfBand (E := E) hn
  obtain ⟨A, K, K1, Cv, hA, hCu0Cv, hrest⟩ :=
    exists_maximal_cuts_state_instance_hoisted_blocks_quad.{u, _} (E := E) Cu0 hCu0 Apass hApass
      Kpass Kpass
  obtain ⟨Cp, hCp1, hpassdata⟩ := hband Cv hCu0Cv
  have hApassNN : (1 : NNReal) ≤ Real.toNNReal Apass := by
    simpa using Real.toNNReal_le_toNNReal hApass
  set Cpe : NNReal := Cp * Real.toNNReal Apass with hCpe
  have hCpe1 : (1 : NNReal) ≤ Cpe := one_le_mul hCp1 hApassNN
  obtain ⟨C1, hC1, hengine⟩ := hrest Cpe hCpe1
  refine ⟨A, Apass, K, K1, Kpass, Cv, C1, d0, hA, hApass, le_trans hCu0 hCu0Cv, hC1, hd0pos,
    hd0le1, ?_⟩
  intro N hN eps heps Mgrid hMgrid iota delta hd hdd0 hd1 hd16 s T hball hED eta heta0 hetagap
    hetaN hfrost
  refine hengine N hN heps Mgrid hMgrid hd hd1 hd16 s T hball hED
    (fun _ t => ∃ (G : GridUniform t T Mgrid Cv) (Ph : ℕ → ℕ → ENNReal), PairBandOn t G 2 Ph Mgrid ∧
      BandedSuper t T Mgrid (gridUniformBandConst (E := E) Cv 2)
        (Apass ^ (Mgrid + 1)
          * (1 - Real.log (delta : ℝ)) ^ (Kpass * ((Mgrid + 2) * (Mgrid + 1)))))
    ?_ eta heta0 hetagap hetaN hfrost
  intro l t hts hGt hCt hCIt
  obtain ⟨Gt⟩ := hGt
  obtain ⟨t2, ht2t, hloss, hC2, hCI2, ⟨G2, Ph2, hPBO, hpar, hBS⟩, hfib⟩ :=
    hpassdata Mgrid (by omega : 0 < Mgrid) hd hdd0 hd1 hd16 s T hball hED t hts Gt
  refine ⟨t2, ht2t, hloss, ⟨G2⟩, hC2, hCI2, ⟨G2, Ph2, hPBO, hBS⟩, ?_⟩
  intro i0 hi0 a ha
  set Wq : ℝ := (1 - Real.log (delta : ℝ)) ^ (Kpass * ((Mgrid + 2) * (Mgrid + 1))) with hWq
  have hcoef : (Cp : ENNReal) * ENNReal.ofReal (Apass ^ (Mgrid + 1) * Wq)
      ≤ ((Cpe ^ (Mgrid + 1) * Real.toNNReal Wq : NNReal) : ENNReal) := by
    rw [show (Cp : ENNReal) * ENNReal.ofReal (Apass ^ (Mgrid + 1) * Wq)
        = ((Cp * Real.toNNReal (Apass ^ (Mgrid + 1) * Wq) : NNReal) : ENNReal) by
      rw [ENNReal.coe_mul]; rfl]
    refine ENNReal.coe_le_coe.mpr ?_
    rw [hCpe]
    exact passRatio_const_le hCp1 hApass Mgrid
  exact (hfib i0 hi0 a ha).trans (mul_le_mul_left hcoef _)

end MultiScaleFac
end Kakeya

end
