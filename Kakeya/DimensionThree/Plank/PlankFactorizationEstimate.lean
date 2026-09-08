/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.KatzTaoPlankInputs
public import Kakeya.DimensionThree.Plank.DilatedParentCount
public import Kakeya.DimensionThree.Plank.FrostmanPlankEstimate
public import Kakeya.DimensionThree.Plank.LocalFactorizationGeometry
public import Kakeya.DimensionThree.Plank.Section6PartAProp51
public import Kakeya.DimensionThree.Plank.SlabMultiplicityEstimate

/-!
# GWZ Proposition 6.6(A): local plank factorisation

This module contains the local half of GWZ Proposition 6.6, its coarse-slab fallbacks, the shared
`ℝ≥0`/`ENNReal` real-power algebra, and the master-scale interfaces. The global Part (B) lives in
`GlobalPlankFactorizationEstimate.lean`.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal Classical

noncomputable section

namespace Kakeya

universe u_section6Estimate

/-- **The plank-window mass constant.**

For a nonempty family of `a × b × 1` planks inside the plank window which is Frostman there with
constant `C · C_F`, the total plank mass `|s| · 8 a b` is at least `|window| / (C · C_F)`; since
`b ≤ 1` this gives the absolute lower bound `C_F · (|s| · a) ≥ |window| / (8 C)`.

The constant is quantified *before* the configuration, which is what
`Kakeya.combineLocalFactorFallback` needs: its `Cm` enters the final loss constant, so it may not
depend on `δ`, `a`, `b` or the family.  Positivity is positivity of the volume of a ball of radius
`Kakeya.plankWindowRadius`. -/
theorem exists_plankWindowMassConst (C : ℝ≥0) (hC1 : 1 ≤ C) :
    ∃ Cm : ℝ≥0, 0 < Cm ∧
      ∀ {ι : Type*} {s : Finset ι} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (V : ι → ShadedPlank a b hab hb1), 0 < a → s.Nonempty →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
        ∀ {CF : ENNReal},
          IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow ((C : ENNReal) * CF) →
          (Cm : ENNReal) ≤ CF * ((s.card : ENNReal) * (a : ENNReal)) := by
  set Vb : ENNReal := volume (plankWindow).carrier with hVb_def
  have hVb0 : Vb ≠ 0 := by
    rw [hVb_def]
    exact (Metric.measure_closedBall_pos volume 0
      (by norm_num [plankWindowRadius] : (0 : ℝ) < (plankWindowRadius : ℝ))).ne'
  have hVbtop : Vb ≠ ⊤ := (plankWindow).isCompact.measure_ne_top
  set Cm : ℝ≥0 := Vb.toNNReal / (8 * C) with hCm_def
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hC1
  have h8C : (8 : ℝ≥0) * C ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hCpos)
  have hCm_pos : 0 < Cm := by
    rw [hCm_def]
    exact div_pos (ENNReal.toNNReal_pos hVb0 hVbtop) (by positivity)
  refine ⟨Cm, hCm_pos, ?_⟩
  intro ι s a b hab hb1 V ha hs hVball CF hFrost
  have hvol : Vb ≤ ((C : ENNReal) * CF)
      * ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) := by
    rw [hVb_def]
    exact volume_plankWindow_le_of_isFrostmanIn V ha hs hVball (CF := (C : ENNReal) * CF) hFrost
  have hb1enn : (b : ENNReal) ≤ (1 : ENNReal) := by exact_mod_cast hb1
  have hmain : Vb ≤ (8 * (C : ENNReal)) * (CF * ((s.card : ENNReal) * (a : ENNReal))) := by
    calc
      Vb ≤ ((C : ENNReal) * CF) * ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) := hvol
      _ ≤ ((C : ENNReal) * CF) * ((s.card : ENNReal) * (8 * (a : ENNReal) * (1 : ENNReal))) := by
        gcongr
      _ = (8 * (C : ENNReal)) * (CF * ((s.card : ENNReal) * (a : ENNReal))) := by
        ring
  rw [hCm_def]
  rw [ENNReal.coe_div h8C, ENNReal.coe_toNNReal hVbtop]
  have hmain' : Vb ≤ (CF * (↑s.card * ↑a)) * (↑(8 * C : ℝ≥0) : ENNReal) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
  rw [ENNReal.div_le_iff]
  · exact hmain'
  · exact ENNReal.coe_ne_zero.mpr h8C
  · exact ENNReal.coe_ne_top

/-- **Pooling parentwise Katz--Tao over the occupied parents of a coarse system.**

The global maximal density of an outer plank family whose cells are labelled by coarse parents, each
label occupied by a fine leaf, is at most the number of *occupied* parents times the parentwise
Katz--Tao constant.  The two inputs are `Kakeya.maxDensity_le_sum_of_parentwise` (the pooling, whose
cost is the number of contributing parents) and
`Kakeya.ExternalParentSystem.card_occupiedParents_le` (the count, finite because `2 ≤ 4 N ρ` bounds
the coarse scale below).  No parent fibre is merged: Katz--Tao is used one fibre at a time. -/
theorem maxDensity_le_of_parentwise_of_occupied
    {ι : Type*} {q : Finset ι} {δ ρ Cu : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (PS : ExternalParentSystem q (fun i => (T i).toTube) ρ Cu)
    (hδ0 : 0 < δ) (hδρ : δ ≤ ρ)
    (hball : ∀ i ∈ q, ((fun i => (T i).toTube) i).carrier ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {N : ℕ} (hN1 : 1 ≤ N) (hNρ : (2 : ℝ) ≤ 4 * (N : ℝ) * (ρ : ℝ))
    {κ' : Type*} {ts : Finset κ'} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : κ' → ShadedPlank a b hab hb1) (par : κ' → PS.Parent)
    (hpar_mem : ∀ x ∈ ts, par x ∈ PS.parents)
    (hocc : ∀ x ∈ ts, ∃ i ∈ q, PS.assign i = par x)
    {C : ℝ≥0}
    (hKTpar : ∀ k ∈ PS.parents,
      IsKatzTao (ts.filter fun x => par x = k) (fun x => (W x).toConvexSpaceBody) (C : ENNReal)) :
    maxDensity ts (fun x => (W x).toConvexSpaceBody)
      ≤ ((tubeParamPackingConstOf N * Cu * C : ℝ≥0) : ENNReal) := by
  classical
  let A : Finset PS.Parent :=
    PS.parents.filter fun k : PS.Parent => ∃ i : ι, i ∈ q ∧ PS.assign i = k
  have hpar : ∀ x ∈ ts, par x ∈ A := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hpar_mem x hx, hocc x hx⟩
  have hAcard : (A.card : ℝ≥0) ≤ tubeParamPackingConstOf N * Cu := by
    dsimp [A]
    convert PS.card_occupiedParents_le hδ0 hδρ hball hN1 hNρ using 1
  calc
    maxDensity ts (fun x => (W x).toConvexSpaceBody)
        ≤ (A.card : ENNReal) * (C : ENNReal) :=
      maxDensity_le_sum_of_parentwise (s := ts) (V := fun x => (W x).toConvexSpaceBody)
        (par := par) (P := A) hpar (Δ := (C : ENNReal))
        (fun k hk => hKTpar k (Finset.mem_filter.mp hk).1)
    _ ≤ ((tubeParamPackingConstOf N * Cu : ℝ≥0) : ENNReal) * (C : ENNReal) := by
      gcongr
      exact_mod_cast hAcard
    _ = ((tubeParamPackingConstOf N * Cu * C : ℝ≥0) : ENNReal) := by
      simp [ENNReal.coe_mul, mul_assoc]

/-- **The outer factor of the large-`b` branch, as `δ`-powers.**

Bookkeeping step between GWZ Lemma 6.9 and `Kakeya.combineLocalFactorFallback`: the outer bound
produced by `Kakeya.ShadedPlank.multiplicity_le_of_maxDensity_of_large` carries `a ^ (-2ε/9)` and
the sub-polynomial overlap constant `Cu ≤ δ ^ (-η)`; both are absorbed into `δ ^ (-ε/3)` using
`δ ≤ a ≤ 1` and `η ≤ ε/9`.  The absolute constants `Cdiv`, `Cpack`, `Csplit` are untouched. -/
theorem outerFallbackDeltaBound {ε η : ℝ} (hε : 0 < ε) {δ a : ℝ≥0} (hδ0 : 0 < δ) (hδa : δ ≤ a)
    (ha1 : a ≤ 1) {Cdiv Cpack Cu Csplit : ℝ≥0} (hηε : η ≤ ε / 9) (hCuδ : Cu ≤ δ ^ (-η))
    {μW : ENNReal}
    (h : μW ≤ (Cdiv : ENNReal) * (a : ENNReal) ^ (-(ε / 9 + ε / 9))
      * ((Cpack * Cu * Csplit : ℝ≥0) : ENNReal)) :
    μW ≤ ((Cdiv * Cpack * Csplit : ℝ≥0) : ENNReal) * (δ : ENNReal) ^ (-(ε / 3)) := by
  have h_a_δ : (a : ENNReal) ^ (-(ε / 9 + ε / 9)) ≤ (δ : ENNReal) ^ (-(ε / 9 + ε / 9)) := by
    have hδa_enn : (δ : ENNReal) ≤ (a : ENNReal) := by exact_mod_cast hδa
    have he9 : (0 : ℝ) < ε / 9 := by positivity
    have h_nonneg' : 0 ≤ ε / 9 + ε / 9 := by nlinarith
    calc
      (a : ENNReal) ^ (-(ε / 9 + ε / 9)) = (a : ENNReal)⁻¹ ^ (ε / 9 + ε / 9) := by
        rw [ENNReal.rpow_neg, ENNReal.inv_rpow]
      _ ≤ (δ : ENNReal)⁻¹ ^ (ε / 9 + ε / 9) := by
        refine ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.mpr hδa_enn) h_nonneg'
      _ = (δ : ENNReal) ^ (-(ε / 9 + ε / 9)) := by
        rw [ENNReal.rpow_neg, ENNReal.inv_rpow]
  have hCuδ' : (Cu : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 9)) := by
    have hδnz : (δ : ℝ≥0) ≠ 0 := hδ0.ne'
    have hδ1 : δ ≤ (1 : ℝ≥0) := hδa.trans ha1
    have h_exp : -(ε / 9) ≤ -η := by linarith
    have hCu59 : Cu ≤ δ ^ (-(ε / 9)) :=
      hCuδ.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 h_exp)
    rw [← ENNReal.coe_rpow_of_ne_zero hδnz (-(ε / 9))]
    exact_mod_cast hCu59
  have hδe0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδetop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hdd : (δ : ENNReal) ^ (-(ε / 9 + ε / 9)) * (δ : ENNReal) ^ (-(ε / 9))
      = (δ : ENNReal) ^ (-(ε / 3)) := by
    calc
      (δ : ENNReal) ^ (-(ε / 9 + ε / 9)) * (δ : ENNReal) ^ (-(ε / 9))
          = (δ : ENNReal) ^ (-(ε / 9 + ε / 9) + (-(ε / 9))) := by
            rw [ENNReal.rpow_add (-(ε / 9 + ε / 9)) (-(ε / 9)) hδe0 hδetop]
      _ = (δ : ENNReal) ^ (-(ε / 3)) := by
            congr 1
            ring
  calc
    μW ≤ (Cdiv : ENNReal) * (a : ENNReal) ^ (-(ε / 9 + ε / 9))
        * ((Cpack * Cu * Csplit : ℝ≥0) : ENNReal) := h
    _ ≤ (Cdiv : ENNReal) * (δ : ENNReal) ^ (-(ε / 9 + ε / 9))
        * ((Cpack * Cu * Csplit : ℝ≥0) : ENNReal) := by
      gcongr
    _ = (Cdiv : ENNReal) * (δ : ENNReal) ^ (-(ε / 9 + ε / 9))
        * (Cpack : ENNReal) * (Cu : ENNReal) * (Csplit : ENNReal) := by
      simp [ENNReal.coe_mul, mul_assoc]
    _ ≤ (Cdiv : ENNReal) * (δ : ENNReal) ^ (-(ε / 9 + ε / 9))
        * (Cpack : ENNReal) * (δ : ENNReal) ^ (-(ε / 9)) * (Csplit : ENNReal) := by
      gcongr
    _ = (Cdiv : ENNReal) * (Cpack : ENNReal) * (Csplit : ENNReal)
        * (δ : ENNReal) ^ (-(ε / 3)) := by
      rw [← hdd]
      ring
    _ = ((Cdiv * Cpack * Csplit : ℝ≥0) : ENNReal) * (δ : ENNReal) ^ (-(ε / 3)) := by
      simp [ENNReal.coe_mul, mul_assoc]

/-- Lemma 6.9 plus the standard `a`-to-`δ` conversion, in the exact strength needed by the
large-`b` call to `combineLocalFactorFallback`.  The maximal-density constant remains in the
fixed coefficient; it is not incorrectly treated as a power of the thin scale. -/
theorem outerMultiplicityLargeOfMaxDensity
    {ε : ℝ} (hε : 0 < ε) {δ a b bSmall Kang Δ : NNReal}
    (hδ0 : 0 < δ) (hδa : δ ≤ a) (ha1 : a ≤ 1) (hbSmall0 : 0 < bSmall)
    (hKang : ∀ δ' : NNReal, 0 < δ' → δ' ≤ 1 →
      ((ShadedSlab.numAngleWindows δ' : ℕ) : ENNReal) ≤
        (Kang : ENNReal) * (δ' : ENNReal) ^ (-((ε / 2) / 9)))
    {κ' : Type*} (q : Finset κ') {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : κ' → ShadedPlank a b hab hb1) (hbLarge : bSmall ≤ b) (hq : q.Nonempty)
    (hDensity : maxDensity q (fun j ↦ (P j).toConvexSpaceBody) ≤ (Δ : ENNReal))
    (hfull : a ^ ((ε / 2) / 9) ≤
      ShadedBody.fullness q (fun j ↦ (P j).toShadedBody)) :
    ShadedBody.multiplicity q (fun j ↦ (P j).toShadedBody) ≤
      ((196520 * Kang * (8 * bSmall ^ 2)⁻¹ * Δ : NNReal) : ENNReal) *
        (δ : ENNReal) ^ (-(ε / 6)) := by
  let Cdiv : NNReal := 196520 * Kang * (8 * bSmall ^ 2)⁻¹
  have ha0 : 0 < a := hδ0.trans_le hδa
  have h69 : ShadedBody.multiplicity q (fun j ↦ (P j).toShadedBody) ≤
      (Cdiv : ENNReal) * (a : ENNReal) ^ (-((ε / 2) / 9 + (ε / 2) / 9)) *
        (Δ : ENNReal) := by
    simpa only [Cdiv] using
      ShadedPlank.multiplicity_le_of_maxDensity_of_large hbSmall0 hKang q P ha0 hbLarge hq
        (η := (ε / 2) / 9) (by positivity) hDensity hfull
  have hout := outerFallbackDeltaBound (ε := ε / 2) (η := 0) (by positivity)
    hδ0 hδa ha1 (Cdiv := Cdiv) (Cpack := Δ) (Cu := 1) (Csplit := 1)
    (by positivity) (by simp) (by simpa only [mul_one] using h69)
  change ShadedBody.multiplicity q (fun j ↦ (P j).toShadedBody) ≤
    ((Cdiv * Δ : NNReal) : ENNReal) * (δ : ENNReal) ^ (-(ε / 6))
  simpa only [mul_one, show -(ε / 2 / 3) = -(ε / 6) by ring] using hout

/-- Absorb one `δ ^ (-ε/12)` split coefficient, enlarge the inner loss to `δ ^ (-ε/6)`,
and replace the retained outer-cardinality denominator by that of a subfamily. -/
theorem absorbSplitAndRestrictCard
    {ε β : ℝ} (hβ : β ≤ 1)
    {δ a b : NNReal} (hδ0 : 0 < δ)
    {n n' : ℕ} (hn : n' ≤ n) {N C μT μW : ENNReal}
    (hC : C ≤ (δ : ENNReal) ^ (-(ε / 12)))
    (hsplit : μT ≤ C * μW *
      ((δ : ENNReal) ^ (-(ε / 12)) *
        ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
        ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β) *
        (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 *
          (N / (n : ENNReal))) ^ (1 - β / 2))) :
    μT ≤ (1 : ENNReal) * μW *
      ((δ : ENNReal) ^ (-(ε / 6)) *
        ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
        ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β) *
        (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 *
          (N / (n' : ENNReal))) ^ (1 - β / 2)) := by
  have hpow : C * (δ : ENNReal) ^ (-(ε / 12)) ≤
      (δ : ENNReal) ^ (-(ε / 6)) := by
    calc
      C * (δ : ENNReal) ^ (-(ε / 12)) ≤
          (δ : ENNReal) ^ (-(ε / 12)) * (δ : ENNReal) ^ (-(ε / 12)) := by gcongr
      _ = (δ : ENNReal) ^ (-(ε / 6)) := by
        rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hδ0.ne') ENNReal.coe_ne_top]
        congr 1
        ring
  have hcardE : (n' : ENNReal) ≤ (n : ENNReal) := by exact_mod_cast hn
  have hdiv : N / (n : ENNReal) ≤ N / (n' : ENNReal) :=
    ENNReal.div_le_div_left hcardE N
  have hp : 0 ≤ 1 - β / 2 := by linarith
  have hcard :
      (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * (N / (n : ENNReal))) ^
          (1 - β / 2) ≤
        (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * (N / (n' : ENNReal))) ^
          (1 - β / 2) := by
    apply ENNReal.rpow_le_rpow _ hp
    gcongr
  calc
    μT ≤ C * μW *
        ((δ : ENNReal) ^ (-(ε / 12)) *
          ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
          ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β) *
          (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 *
            (N / (n : ENNReal))) ^ (1 - β / 2)) := hsplit
    _ = μW * (C * (δ : ENNReal) ^ (-(ε / 12))) *
        (((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
          ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)) *
        (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 *
          (N / (n : ENNReal))) ^ (1 - β / 2) := by ring
    _ ≤ μW * (δ : ENNReal) ^ (-(ε / 6)) *
        (((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
          ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)) *
        (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 *
          (N / (n' : ENNReal))) ^ (1 - β / 2) := by gcongr
    _ = _ := by ring

/-- The final large-`b` algebraic combination.  All genuinely fixed losses are exposed in the
single hypothesis `habsorb`; the Frostman restriction loss `Cfr` is charged with its correct
power, rather than being silently identified with the original Frostman constant. -/
theorem combineLargeAndAbsorb
    {β ε : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hε : 0 < ε)
    {δ a b bSmall Cm Cout Cfr : NNReal}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ha0 : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hbSmall0 : 0 < bSmall) (hbLarge : bSmall ≤ b) (hCm : 0 < Cm) (hCfr : 1 ≤ Cfr)
    {CF : ENNReal} (hCF1 : 1 ≤ CF) (hCFtop : CF ≠ ⊤)
    {nq nts : ℕ} (hnts : nts ≠ 0) (hnq : nq ≠ 0) {μT μW : ENNReal}
    (hmass : (Cm : ENNReal) ≤ ((Cfr : ENNReal) * CF) *
      ((nts : ENNReal) * (a : ENNReal)))
    (hW : μW ≤ (Cout : ENNReal) * (δ : ENNReal) ^ (-(ε / 6)))
    (hsplit : μT ≤ (1 : ENNReal) * μW *
      ((δ : ENNReal) ^ (-(ε / 6)) *
        ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
        ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β) *
        (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 *
          ((nq : ENNReal) / (nts : ENNReal))) ^ (1 - β / 2)))
    (habsorb :
      ((Cout * Cm⁻¹ ^ (1 - β / 2) *
        max 1 (bSmall ^ (5 * β / 2 - 1)) : NNReal) : ENNReal) *
          (Cfr : ENNReal) ^ (1 - β / 2) ≤
        (δ : ENNReal) ^ (-(ε / 2))) :
    μT ≤ (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) *
      ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) *
      (δ : ENNReal) ^ (-2 * β) *
      ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2) := by
  have hCFlarge1 : 1 ≤ (Cfr : ENNReal) * CF := one_le_mul (by exact_mod_cast hCfr) hCF1
  have hCFlargeTop : (Cfr : ENNReal) * CF ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hCFtop
  have hcomb := combineLocalFactorFallback hβ0 hβ1 (show 0 < ε / 2 by positivity)
    hδ0 hδ1 ha0 hab hb1 hbSmall0 hbLarge hCm le_rfl hCFlarge1 hCFlargeTop
    hnts hnq hmass (Cout := Cout) (Csplit := 1) (by
      simpa only [show -((ε / 2) / 3) = -(ε / 6) by ring] using hW) (by
      simpa only [ENNReal.coe_one, show -((ε / 2) / 3) = -(ε / 6) by ring] using hsplit)
  have hp : 0 ≤ 1 - β / 2 := by linarith
  have hδpow : (δ : ENNReal) ^ (-(ε / 2)) * (δ : ENNReal) ^ (-(ε / 2)) =
      (δ : ENNReal) ^ (-ε) := by
    rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hδ0.ne') ENNReal.coe_ne_top]
    congr 1
    ring
  refine hcomb.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
  calc
    ((1 * Cout * Cm⁻¹ ^ (1 - β / 2) *
          max 1 (bSmall ^ (5 * β / 2 - 1)) : NNReal) : ENNReal) *
          ((δ : ENNReal) ^ (-(ε / 2)) *
            ((Cfr : ENNReal) ^ (1 - β / 2) * CF ^ (1 - β / 2)) *
            ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) *
            (δ : ENNReal) ^ (-2 * β) *
            ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2)) =
        ((((Cout * Cm⁻¹ ^ (1 - β / 2) *
            max 1 (bSmall ^ (5 * β / 2 - 1)) : NNReal) : ENNReal) *
          (Cfr : ENNReal) ^ (1 - β / 2)) * (δ : ENNReal) ^ (-(ε / 2))) *
          (CF ^ (1 - β / 2) *
            ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) *
            (δ : ENNReal) ^ (-2 * β) *
            ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2)) := by ring
    _ ≤ ((δ : ENNReal) ^ (-(ε / 2)) * (δ : ENNReal) ^ (-(ε / 2))) *
          (CF ^ (1 - β / 2) *
            ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) *
            (δ : ENNReal) ^ (-2 * β) *
            ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2)) := by gcongr
    _ = _ := by rw [hδpow]; ring

/-- **Coarse-slab fallback for GWZ 6.6(A) in the large-`b` regime** (blueprint
`lem:geometryCoarseSlabMaxMultiplicity`, `lem:geometryCoarseSlabFrostmanUnion`; the precise
Lean-facing form of the `slab1` fallback). It covers the case where the outer
plank width `b` is too large for the small-scale application of GWZ Lemma 6.4, and concludes the
6.6(A) bound under the largeness hypothesis `b₀ < b`.

**Proved**, from GWZ Lemma 6.9 (`Kakeya.ShadedPlank.multiplicity_le_of_maxDensity_of_large`) and the
Proposition 5.1 μ-split, with no new non-concentration hypothesis.  The route, and why the earlier
check below is superseded, is recorded after the signature.

The threshold `b₀` is now quantified **before** the loss constant `Ccoarse`, and the conclusion
carries that loss. In the previous signature `b₀` was an ordinary argument appearing only in
`b₀ < b`, so the statement asserted a constant-free `δ ^ (-ε)` bound for *every* positive `b₀` —
vacuously strong. The consumer must absorb `Ccoarse` into `δ ^ (-ε)` at a genuine small-scale
threshold, e.g. via `Kakeya.rpowConstAbsorb`.

The factorisation hypothesis is a `Kakeya.ComparableBodyFactorization`, matching Proposition 6.6(A).
The exact `parts_are_planks` equality of `Kakeya.PlankFactorization` forced `1/2 ≤ ρ` and so made
these hypotheses unsatisfiable at small scales; the largeness criterion for this branch is `b₀ < b`,
never a lower bound on `ρ`.

**The scale hypothesis `δ ≤ a`.**  Without it the statement is refutable: `a` would occur
only in `hab : a ≤ b` and in the conclusion, and `a = 0` makes
`((a : ENNReal) / b) ^ (3 * β / 2) = 0`, hence the whole right-hand side `0`, while
`ShadedBody.multiplicity` of a family with positive fullness is at least `1`.  The paper's
`a` is the smallest dimension of planks that *contain* `δ`-tubes, so `δ ≤ a` is the intended
relation; the caller obtains it from `Kakeya.factoringAndMultPropCombined`, where it is
*derived* from occupancy (`T i ≤ H x`), the comparable representative (`H x ≤ W x`) and
`Kakeya.le_thinWidth_of_tube_le_plank`.  The overlap hypotheses `1 ≤ Cu`, `Cu ≤ δ ^ (-η)`
are likewise needed and likewise already available to the caller: with `Cu` unconstrained
the parent system carries no quantitative information at all.

**The route.**  GWZ (page 22, the remark after eq. (45)): Lemma 6.9 replaces the *outer* application
of Lemma 6.4 to the `a × b × 1` plank family `𝒲`, while the inner factor still comes from the
Proposition 5.1 μ-split.  Concretely, in this branch

1. the μ-split, the outer family `𝒲 = (W j)_{j ∈ ts}`, its fullness `a ^ ηOuter ≤ λ(𝒲)`, its
   Frostman constant `Csplit · C_F` and the *parentwise* Katz--Tao bound
   `Δ_max(𝒲 ∩ par⁻¹ k) ≤ Csplit` are the corresponding clauses of the explicit Part-(A)
   analytic package;
2. `b₀ < b ≤ 2 ρ` — the second half derived by
   `Kakeya.b_le_two_mul_of_comparableBodyFactorization` — bounds the coarse scale from below,
   `b₀ / 2 < ρ`.  So the unit ball is covered *leafwise* by `O_{b₀}(1)` radius-`8 ρ` test tubes
   (`Kakeya.exists_leafwise_cover_of_ball`), and the structure's own bounded overlap union-bounds
   over that cover: at most `tubeParamPackingConstOf N · Cu` parents own a leaf at all
   (`Kakeya.ExternalParentSystem.card_occupiedParents_le`).  Every cell of `𝒲` is occupied, so only
   that many parents contribute;
3. pooling the parentwise bounds over those parents (`Kakeya.maxDensity_le_sum_of_parentwise`, no
   fibre merged and no Katz--Tao estimate run on a union of classes) gives the *global*
   `Δ_max(𝒲) ≤ tubeParamPackingConstOf N · Cu · Csplit`, sub-polynomial since `Cu ≤ δ ^ (-η)`;
4. `ShadedPlank.multiplicity_le_of_maxDensity_of_large` — Lemma 6.9 applied to the `a × 1 × 1`
   widening of `𝒲`, at an arbitrary maximal density — turns that into
   `μ(𝒲, Y_𝒲) ≤ Cout · δ ^ (-ε/3)`;
5. `Kakeya.combineLocalFactorFallback` combines it with the μ-split, the plank-window mass bound
   (`Kakeya.exists_plankWindowMassConst`) paying for the target's `C_F ^ (1 - β/2)`, and the
   `b ≥ b₀` widening losses.

Any dependence of `Ccoarse` on `b₀` is harmless: `b₀` is a fixed threshold chosen before the
configuration, which is why it is quantified before `Ccoarse` here.

None of the five steps uses `K_KT(β)` or `K_F(β)`: Lemma 6.9 is unconditional and Proposition 5.1
does not consume the partial estimates either, so this branch of 6.6(A) holds outright.  `hKKT` and
`hKF` are kept only so that the two branches of `Kakeya.tubeMultiplicityOfLocalPlankFactorisation`
take the same data.

**What the earlier check of this leaf got wrong.**  It recorded as "the decisive obstruction"
a missing *slab-shaped* non-concentration bound for the pooled outer family, on the grounds
that `Kakeya.ExternalParentSystem.boundedOverlapThroughLeaves` controls only tube-shaped test
bodies while Lemma 6.9 tests against slab-shaped ones.  That conflated two different uses of
the parent system.  Lemma 6.9 is fed a `Δ_max` bound, and `Δ_max` is *inherited by pooling*
from the parentwise Katz--Tao bound on the representative planks, which the interface does
provide; the only thing the parent system has to supply is a *count of contributing parents*,
which is exactly what its tube-shaped bounded overlap gives.  What made the count look
unavailable was pooling at a fixed test body: in the large-`b` regime that is not needed,
because `ρ ≳ b₀` makes the *total* number of occupied parents finite.  No new
non-concentration axiom is introduced, and nothing is assumed about
`Kakeya.ComparableBodyFactorization.isKatzTao`, which indeed concerns the actual factor bodies
rather than the representative planks. -/
/- The inner factor in the Part-(A) multiplicity split, after the Section-6 master-scale estimate
and normalization have been applied. -/
noncomputable def section6PartAInnerTarget (β εI : ℝ)
    {ι : Type u_section6Estimate} (q : Finset ι) {δ ρ a b : ℝ≥0}
    {hab : a ≤ b} {hb1 : b ≤ 1}
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) {Cpar : ℝ≥0}
    (PS : ExternalParentSystem q (fun i => (T i).toTube) ρ Cpar)
    {CFib : ENNReal} {C₀ Cmass Cdim B : ℝ≥0}
    (D : Section6PartAFactorData a b hab hb1 q T PS CFib C₀ Cmass Cdim B) : ENNReal :=
  (δ : ENNReal) ^ (-εI) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
    ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β) *
    (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 *
      ((q.card : ENNReal) / (D.thickOutput.outerSet.card : ENNReal))) ^ (1 - β / 2)

/-- The genuinely residual inner estimate in the Part-(A) adapter.

The scale-selection and Proposition-5.1 product constants occur on the left.  Consequently this
contract cannot supply the final multiplicity split without consuming the proved Item 5 output. -/
def Section6PartAInnerAnalyticBound (β εI : ℝ)
    {ι : Type u_section6Estimate} (q : Finset ι) {δ ρ a b : ℝ≥0}
    {hab : a ≤ b} {hb1 : b ≤ 1}
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) {Cpar : ℝ≥0}
    (PS : ExternalParentSystem q (fun i => (T i).toTube) ρ Cpar)
    {CFib : ENNReal} {C₀ Cmass Cdim B Csplit : ℝ≥0}
    (D : Section6PartAFactorData a b hab hb1 q T PS CFib C₀ Cmass Cdim B) : Prop :=
  ∀ x ∈ D.thickOutput.outerSet,
    ((Section6PartAFactorData.selectionConstant δ B * D.productConstant : NNReal) : ENNReal) *
        ShadedBody.multiplicity (D.thickOutput.fiber x) D.thickOutput.innerBody ≤
      (Csplit : ENNReal) * section6PartAInnerTarget β εI q T PS D

/-- The residual Section-6 normalization of Proposition 5.1's aggregate outer fullness.

The corrected Proposition 5.1 supplies fullness on the enlarged actual carriers.  This contract is
only the later representative-plank and master-scale conversion, and therefore takes the proved
Proposition-5.1 output as an explicit argument. -/
def Section6PartAOuterFullnessNormalization (ηOuter : ℝ)
    {ι : Type u_section6Estimate} (q : Finset ι) {δ ρ a b : ℝ≥0}
    {hab : a ≤ b} {hb1 : b ≤ 1}
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) {Cpar : ℝ≥0}
    (PS : ExternalParentSystem q (fun i => (T i).toTube) ρ Cpar)
    {CFib : ENNReal} {C₀ Cmass Cdim B : ℝ≥0}
    (D : Section6PartAFactorData a b hab hb1 q T PS CFib C₀ Cmass Cdim B) : Prop :=
  ∀ _P : D.Prop51Output,
    (a : ℝ≥0) ^ ηOuter ≤ ShadedBody.fullness D.thickOutput.outerSet
      (fun x => (D.outerPlank x).toShadedBody)

/-- The analytic and representative-geometry data still needed after the corrected Proposition 5.1
call. Unlike the former presentation shell, this contract must construct an actual
`Section6PartAFactorData`; all structural conclusions are then obtained from the proved
`CoreSelectScale` interface. -/
def Section6PartAAnalyticAssembly (β : ℝ) : Prop :=
    ∃ Csplit : ℝ≥0, 1 ≤ Csplit ∧
      ∀ (εI : ℝ), 0 < εI → ∀ (ηOuter : ℝ), 0 < ηOuter →
      ∃ ηFine : ℝ, 0 < ηFine ∧
      ∀ {ι : Type u_section6Estimate} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        ∀ (Cu : ℝ≥0), 1 ≤ Cu → Cu ≤ δ ^ (-ηFine) →
        ∀ (𝒰 : ShadedTube.ShadedUniformTubeSet q T (Tube.ssfGridLen δ) Cu),
        (δ : ℝ≥0) ^ ηFine ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1) (Cpar : ℝ≥0)
          (PS : ExternalParentSystem q (fun i => (T i).toTube) ρ Cpar),
          δ ≤ ρ → ρ ≤ 1 → b ≤ 2 * ρ →
          ∀ (C₀ : ℝ≥0), C₀ ≤ δ ^ (-ηFine) →
            ∀ (Fz : ∀ k ∈ PS.parents, ComparableBodyFactorization b
              {i ∈ q | PS.assign i = k} (fun i => (T i).toConvexSpaceBody) C₀),
          ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
            IsFrostmanIn q (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall CF →
            ∃ (CFib : ENNReal) (Cmass Cdim B : ℝ≥0),
              ∃ A : Section6PartAConstructionData a b hab hb1 q T PS CFib C₀ Cmass Cdim B Fz,
                C₀ ≤ Csplit ∧
                Section6PartAOuterFullnessNormalization ηOuter q T PS A.toFactorData ∧
                IsFrostmanIn A.toFactorData.thickOutput.outerSet
                  (fun x => (A.toFactorData.outerPlank x).toConvexSpaceBody)
                  plankWindow ((Csplit : ENNReal) * CF) ∧
                Section6PartAInnerAnalyticBound (Csplit := Csplit) β εI q T PS A.toFactorData

/-- Combine the real Proposition 5.1 output with the explicitly residual Section-6 analytic data.
The factor `C_NC^3` is only the parentwise dilated-test-body count. -/
theorem section6PartAAnalyticAssembly {β : ℝ} (_hβpos : 0 < β) (_hβle : β ≤ 1)
    (C_NC : ℝ≥0) (hC_NC : 1 ≤ C_NC)
    (hAnalytic : Section6PartAAnalyticAssembly.{u_section6Estimate} β) :
    ∃ Csplit : ℝ≥0, 1 ≤ Csplit ∧
      ∀ (εI : ℝ), 0 < εI → ∀ (ηOuter : ℝ), 0 < ηOuter →
      ∃ ηFine : ℝ, 0 < ηFine ∧
      ∀ {ι : Type u_section6Estimate} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        ∀ (Cu : ℝ≥0), 1 ≤ Cu → Cu ≤ δ ^ (-ηFine) →
        ∀ (𝒰 : ShadedTube.ShadedUniformTubeSet q T (Tube.ssfGridLen δ) Cu),
        (δ : ℝ≥0) ^ ηFine ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1) (Cpar : ℝ≥0)
          (PS : ExternalParentSystem q (fun i => (T i).toTube) ρ Cpar),
          δ ≤ ρ → ρ ≤ 1 → b ≤ 2 * ρ →
          ∀ (C₀ : ℝ≥0), C₀ ≤ δ ^ (-ηFine) →
            ∀ (Fz : ∀ k ∈ PS.parents, ComparableBodyFactorization b
              {i ∈ q | PS.assign i = k} (fun i => (T i).toConvexSpaceBody) C₀),
          ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
            IsFrostmanIn q (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall CF →
            0 < a ∧ δ ≤ a ∧
            ∃ (κ' : Type) (ts : Finset κ') (W : κ' → ShadedPlank a b hab hb1),
              ts.Nonempty ∧
              (∀ j ∈ ts, (W j).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
              (ts : Set κ').Pairwise
                (fun i j => _root_.IsEssentiallyDistinct (W i).carrier (W j).carrier) ∧
              (a : ℝ≥0) ^ ηOuter ≤ ShadedBody.fullness ts
                (fun j => (W j).toShadedBody) ∧
              (∃ (par : κ' → PS.Parent) (H : κ' → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))),
                  (∀ x ∈ ts, par x ∈ PS.parents) ∧
                  (∀ x ∈ ts, ∃ i ∈ q, PS.assign i = par x ∧
                        ((T i).toTube).toConvexSpaceBody ≤ H x) ∧
                  (∀ x ∈ ts, H x ≤ (W x).toConvexSpaceBody) ∧
                  (∀ k ∈ PS.parents,
                    IsKatzTao (ts.filter fun x => par x = k)
                      (fun x => (W x).toConvexSpaceBody) (Csplit : ENNReal)) ∧
                  (∀ j ∈ ts, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
                      ∀ k ∈ PS.parents,
                        (({x ∈ ts | ((W x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
                            (((Plank.thickened (W j).toPrism3D θ hθ1).toPrismNDim.dilation
                              C_NC).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∧
                            par x = k}.card : ℝ≥0))
                          ≤ (Csplit * (b / a)) * θ)) ∧
              IsFrostmanIn ts (fun j => (W j).toConvexSpaceBody)
                plankWindow ((Csplit : ENNReal) * CF) ∧
              ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
                (Csplit : ENNReal) *
                  ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) *
                  ((δ : ENNReal) ^ (-εI) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
                    * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)
                    * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2
                        * ((q.card : ENNReal) / (ts.card : ENNReal))) ^ (1 - β / 2)) := by
  obtain ⟨Csplit₀, hCs₀, hadapt⟩ := hAnalytic
  refine ⟨Csplit₀ * C_NC ^ 3, one_le_mul hCs₀ (one_le_pow₀ hC_NC), ?_⟩
  intro εI hεI ηOuter hηOuter
  obtain ⟨ηFine, hηFine, hcfg⟩ := hadapt εI hεI ηOuter hηOuter
  refine ⟨ηFine, hηFine, ?_⟩
  intro ι q δ hδ0 T hball Cu hCu1 hCuδ 𝒰 hfull ρ a b hab hb1 Cpar PS hδρ hρ1 hbρ
    C₀ hC₀ Fz CF hCF1 hCFtop hFrost
  obtain ⟨CFib, Cmass, Cdim, B, A, hC₀split, hfullNorm, hWfrost, hinner⟩ :=
    hcfg q hδ0 T hball Cu hCu1 hCuδ 𝒰 hfull ρ a b hab hb1 Cpar PS hδρ hρ1 hbρ C₀ hC₀ Fz
      CF hCF1 hCFtop hFrost
  let D := A.toFactorData
  let P := D.factoringAndMultPropCombined C_NC hC_NC
  have hWfull : (a : ℝ≥0) ^ ηOuter ≤ ShadedBody.fullness D.thickOutput.outerSet
      (fun x => (D.outerPlank x).toShadedBody) := hfullNorm P.toProp51Output
  have ha : 0 < a := hδ0.trans_le P.delta_le_thinWidth
  have hCle : (Csplit₀ : ENNReal) ≤ ((Csplit₀ * C_NC ^ 3 : ℝ≥0) : ENNReal) := by
    exact_mod_cast le_mul_of_one_le_right zero_le (one_le_pow₀ hC_NC)
  have hWfrost' : IsFrostmanIn D.thickOutput.outerSet
      (fun x => (D.outerPlank x).toConvexSpaceBody) plankWindow
      (((Csplit₀ * C_NC ^ 3 : ℝ≥0) : ENNReal) * CF) := by
    intro K' hK'
    refine (hWfrost K' hK').trans ?_
    gcongr
  obtain ⟨x, hx⟩ := P.outerSet_nonempty
  have hsplitineq₀ : ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
      (Csplit₀ : ENNReal) *
        ShadedBody.multiplicity D.thickOutput.outerSet
          (fun y => (D.outerPlank y).toShadedBody) *
        section6PartAInnerTarget β εI q T PS D := by
    calc
      ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
          (Section6PartAFactorData.selectionConstant δ B : ENNReal) *
            (D.productConstant : ENNReal) *
            ShadedBody.multiplicity D.thickOutput.outerSet
              (fun y => (D.outerPlank y).toShadedBody) *
            ShadedBody.multiplicity (D.thickOutput.fiber x) D.thickOutput.innerBody :=
        Section6PartAFactorData.Prop51Output.multiplicity_product_original
          (D := D) P.toProp51Output x hx
      _ = ShadedBody.multiplicity D.thickOutput.outerSet
            (fun y => (D.outerPlank y).toShadedBody) *
          (((Section6PartAFactorData.selectionConstant δ B * D.productConstant : NNReal) :
              ENNReal) *
            ShadedBody.multiplicity (D.thickOutput.fiber x) D.thickOutput.innerBody) := by
        simp only [ENNReal.coe_mul]
        ring
      _ ≤ ShadedBody.multiplicity D.thickOutput.outerSet
            (fun y => (D.outerPlank y).toShadedBody) *
          ((Csplit₀ : ENNReal) * section6PartAInnerTarget β εI q T PS D) := by
        exact mul_le_mul_right (hinner x hx) _
      _ = (Csplit₀ : ENNReal) *
          ShadedBody.multiplicity D.thickOutput.outerSet
            (fun y => (D.outerPlank y).toShadedBody) *
          section6PartAInnerTarget β εI q T PS D := by ring
  have hsplitineq' : ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
      ((Csplit₀ * C_NC ^ 3 : ℝ≥0) : ENNReal) *
        ShadedBody.multiplicity D.thickOutput.outerSet
          (fun x => (D.outerPlank x).toShadedBody) *
        ((δ : ENNReal) ^ (-εI) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
          * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)
          * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2
              * ((q.card : ENNReal) /
                (D.thickOutput.outerSet.card : ENNReal))) ^ (1 - β / 2)) := by
    refine hsplitineq₀.trans ?_
    change (Csplit₀ : ENNReal) *
        ShadedBody.multiplicity D.thickOutput.outerSet
          (fun x => (D.outerPlank x).toShadedBody) *
        section6PartAInnerTarget β εI q T PS D ≤ _
    simp only [section6PartAInnerTarget]
    gcongr
  refine ⟨ha, P.delta_le_thinWidth, D.core.Cell, D.thickOutput.outerSet, D.outerPlank,
    P.outerSet_nonempty, ?_, P.outer_pairwise, hWfull,
    ⟨D.parent, D.core.body, P.parent_mem, P.occupancy, P.body_le_outerPlank, ?_, ?_⟩,
    hWfrost', hsplitineq'⟩
  · intro x hx
    rw [← plankWindow_carrier]
    exact P.outer_window x hx
  · intro k hk
    exact (P.parent_katzTao k hk).mono (by
      exact_mod_cast hC₀split.trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hC_NC)))
  · intro j hj θ hθab hθ1 k hk
    have hlocal := P.parentwise_dilated_count j hj θ hθab hθ1 k hk
    calc
      (({x ∈ D.thickOutput.outerSet |
          ((D.outerPlank x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
            (((Plank.thickened (D.outerPlank j).toPrism3D θ hθ1).toPrismNDim.dilation
              C_NC).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∧
          D.parent x = k}.card : ℝ≥0))
          = (D.dilatedParentCells C_NC j θ hθ1 k).card := by rfl
      _ ≤ C₀ * C_NC ^ 3 * (b / a) * θ := hlocal
      _ ≤ (Csplit₀ * C_NC ^ 3 * (b / a)) * θ := by gcongr

theorem coarseSlabFallback {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hAnalytic : Section6PartAAnalyticAssembly.{u_section6Estimate} β)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ b₀ : ℝ≥0, 0 < b₀ →
      ∃ Ccoarse : ℝ≥0, 1 ≤ Ccoarse ∧ ∃ η > (0 : ℝ),
        ∀ {ι : Type u_section6Estimate} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ)
          (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
          (∃ C : ℝ≥0, 1 ≤ C ∧ C ≤ δ ^ (-η) ∧
            Nonempty (ShadedTube.ShadedUniformTubeSet q T
              (Tube.ssfGridLen δ) C)) →
          (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
          ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1) (hδa : δ ≤ a) (Cu : ℝ≥0),
            1 ≤ Cu → Cu ≤ δ ^ (-η) →
            ∀ (PS : ExternalParentSystem q (fun i => (T i).toTube) ρ Cu),
            δ ≤ ρ → ρ ≤ 1 →
            ∀ (C₀ : ℝ≥0), C₀ ≤ δ ^ (-η) →
              ∀ (Fz : ∀ k ∈ PS.parents, ComparableBodyFactorization b
                {i ∈ q | PS.assign i = k} (fun i => (T i).toConvexSpaceBody) C₀),
            ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
              IsFrostmanIn q (fun i => (T i).toConvexSpaceBody)
                ConvexSpaceBody.closedUnitBall CF →
              b₀ < b →
              ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
                (Ccoarse : ENNReal) *
                  ((δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
                    * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
                    * (δ : ENNReal) ^ (-2 * β)
                    * ((δ : ENNReal) ^ 2 * (q.card : ENNReal)) ^ (1 - β / 2)) := by
  intro b₀ hb₀
  obtain ⟨K, hK⟩ := ShadedSlab.exists_numAngleWindows_le (ε := ε / 9) (by positivity)
  obtain ⟨Csplit, hCs1, hadapt⟩ :=
    section6PartAAnalyticAssembly hβpos hβle 1 le_rfl hAnalytic
  obtain ⟨ηFine, hηFine, hcfg⟩ := hadapt (ε / 3) (by positivity) (ε / 9) (by positivity)
  obtain ⟨Cm, hCm0, hmassfun⟩ := exists_plankWindowMassConst Csplit hCs1
  set N : ℕ := ⌈((b₀ : ℝ))⁻¹⌉₊ + 1 with hN_def
  set Cpack : ℝ≥0 := tubeParamPackingConstOf N with hCpack_def
  set Cdiv : ℝ≥0 := 196520 * K * (8 * b₀ ^ 2)⁻¹ with hCdiv_def
  set Cout : ℝ≥0 := Cdiv * Cpack * Csplit with hCout_def
  refine ⟨max 1 (Csplit * Cout * (Cm⁻¹) ^ (1 - β / 2) * max 1 (b₀ ^ (5 * β / 2 - 1))),
    le_max_left _ _, min ηFine (ε / 9), ?_, ?_⟩
  · have hε9 : (0 : ℝ) < ε / 9 := by positivity
    by_cases hle : (ηFine : ℝ) ≤ ε / 9
    · rw [min_eq_left hle]
      exact hηFine
    · rw [min_eq_right (le_of_lt (lt_of_not_ge hle))]
      exact hε9
  · intro ι q δ hδ0 T hball huniform hfull ρ a b hab hb1 hδa Cu hCu1 hCuδ PS hδρ hρ1 C₀ hC₀η Fz CF
      hCF1 hCFtop hFrost hbb₀
    rcases q.eq_empty_or_nonempty with rfl | hq
    · simp
    have hδ1 : δ ≤ 1 := hδρ.trans hρ1
    have ha0 : 0 < a := lt_of_lt_of_le hδ0 hδa
    have ha1 : a ≤ 1 := hab.trans hb1
    have hassign : ∀ i ∈ q, PS.assign i ∈ PS.parents ∧
        (T i).toConvexSpaceBody ≤ (PS.parentTube (PS.assign i)).toConvexSpaceBody :=
      fun i hi => ⟨PS.assign_mem i hi, PS.leaf_le_parent i hi⟩
    have hbρ : b ≤ 2 * ρ := b_le_two_mul_of_comparableBodyFactorization hb1 hq hassign Fz
    have hball' : ∀ i ∈ q, ((fun i => (T i).toTube) i).carrier ⊆
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := fun i hi => by simpa using hball i hi
    have hη_le_ηFine : min ηFine (ε / 9) ≤ ηFine := min_le_left ηFine (ε / 9)
    have hfull' : (δ : ℝ≥0) ^ ηFine ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) :=
      (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hη_le_ηFine).trans hfull
    have hC₀η' : C₀ ≤ δ ^ (-ηFine) := by
      have h_neg : -ηFine ≤ -(min ηFine (ε / 9)) := by linarith [hη_le_ηFine]
      calc
        C₀ ≤ δ ^ (-(min ηFine (ε / 9))) := hC₀η
        _ ≤ δ ^ (-ηFine) := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 h_neg
    obtain ⟨Cunif, hCunif1, hCunifδ, ⟨𝒰⟩⟩ := huniform
    have hCunifδ' : Cunif ≤ δ ^ (-ηFine) := by
      have h_neg : -ηFine ≤ -(min ηFine (ε / 9)) := by linarith [hη_le_ηFine]
      calc
        Cunif ≤ δ ^ (-(min ηFine (ε / 9))) := hCunifδ
        _ ≤ δ ^ (-ηFine) := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 h_neg
    obtain ⟨-, -, κ', ts, W, hts_ne, hWball, hWed, hWfull,
        ⟨par, H, hpar_mem, hocc, hbodyW, hKTpar, -⟩, hWfrost, hsplitineq⟩ :=
      hcfg q hδ0 T hball Cunif hCunif1 hCunifδ' 𝒰 hfull' ρ a b hab hb1 Cu PS hδρ hρ1 hbρ C₀ hC₀η' Fz
        CF hCF1 hCFtop hFrost
    -- STEP 1: occupied parents
    let A : Finset PS.Parent := PS.parents.filter fun k => ∃ i ∈ q, PS.assign i = k
    have hb₀R : (0 : ℝ) < (b₀ : ℝ) := by exact_mod_cast hb₀
    have hb₀lt2ρR : (b₀ : ℝ) < 2 * (ρ : ℝ) := by
      exact lt_of_lt_of_le (by exact_mod_cast hbb₀) (by exact_mod_cast hbρ)
    have hNge : ((b₀ : ℝ))⁻¹ ≤ (N : ℝ) := by
      dsimp [N]
      push_cast
      linarith [Nat.le_ceil ((b₀ : ℝ))⁻¹]
    have hNρ : (2 : ℝ) ≤ 4 * (N : ℝ) * (ρ : ℝ) := by
      have hρR : (0 : ℝ) < (ρ : ℝ) :=
        lt_of_lt_of_le (by exact_mod_cast hδ0) (by exact_mod_cast hδρ)
      have hinv : ((b₀ : ℝ))⁻¹ * (b₀ : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hb₀R)
      have h_inv_pos : 0 < ((b₀ : ℝ))⁻¹ := inv_pos.mpr hb₀R
      nlinarith
    have hAcard : ((A.card : ℝ≥0)) ≤ Cpack * Cu := by
      dsimp [A, Cpack]
      exact PS.card_occupiedParents_le hδ0 hδρ hball' (Nat.le_add_left 1 ⌈((b₀ : ℝ))⁻¹⌉₊) hNρ
    -- STEP 2: pool parentwise Katz--Tao over the occupied parents
    have hpar : ∀ x ∈ ts, par x ∈ A := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨hpar_mem x hx,
        (hocc x hx).imp (fun i hi => ⟨hi.1, hi.2.1⟩)⟩
    have hmd : maxDensity ts (fun x => (W x).toConvexSpaceBody) ≤
        (A.card : ENNReal) * (Csplit : ENNReal) :=
      maxDensity_le_sum_of_parentwise (s := ts) (V := fun x => (W x).toConvexSpaceBody)
        (par := par) (P := A) hpar (Δ := (Csplit : ENNReal))
        (fun k hk => hKTpar k (Finset.mem_filter.mp hk).1)
    have hΔ : maxDensity ts (fun x => (W x).toConvexSpaceBody) ≤
        ((Cpack * Cu * Csplit : ℝ≥0) : ENNReal) := by
      calc
        maxDensity ts (fun x => (W x).toConvexSpaceBody) ≤
            (A.card : ENNReal) * (Csplit : ENNReal) := hmd
        _ ≤ ((Cpack * Cu : ℝ≥0) : ENNReal) * (Csplit : ENNReal) := by
          gcongr
          exact_mod_cast hAcard
        _ = ((Cpack * Cu * Csplit : ℝ≥0) : ENNReal) := by
          simp [ENNReal.coe_mul, mul_assoc]
    -- STEP 3: Lemma 6.9
    let μW : ENNReal := ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
    have hW69 : μW ≤ (Cdiv : ENNReal) * (a : ENNReal) ^ (-(ε / 9 + ε / 9))
        * ((Cpack * Cu * Csplit : ℝ≥0) : ENNReal) := by
      simpa [Cdiv] using
        ShadedPlank.multiplicity_le_of_maxDensity_of_large hb₀ hK ts W ha0 hbb₀.le hts_ne
          (η := ε / 9) (by positivity) hΔ hWfull
    have hW : μW ≤ (Cout : ENNReal) * (δ : ENNReal) ^ (-(ε / 3)) := by
      rw [hCout_def]
      exact outerFallbackDeltaBound hε hδ0 hδa ha1 (η := min ηFine (ε / 9))
        (min_le_right _ _) hCuδ hW69
    -- STEP 4
    have hmass : (Cm : ENNReal) ≤ CF * ((ts.card : ENNReal) * (a : ENNReal)) :=
      hmassfun W ha0 hts_ne hWball hWfrost
    -- STEP 5
    have hcomb := combineLocalFactorFallback hβpos hβle hε hδ0 hδ1 ha0 hab hb1 hb₀ hbb₀.le
      hCm0 hCs1 hCF1 hCFtop (Finset.card_ne_zero.mpr hts_ne) (Finset.card_ne_zero.mpr hq)
      hmass hW hsplitineq
    refine hcomb.trans ?_
    gcongr
    exact_mod_cast le_max_right _ _

/-- **rpow constant absorption threshold** (choice of `δ₀`). For an absolute constant `C ≥ 1`,
nonnegative power `p` and positive exponent `e`, there is `δ₀ > 0` so that `C^p ≤ δ^(-e)` for all
`0 < δ ≤ δ₀` (take `δ₀ = C^(-p/e)`). Used to absorb the fixed factoring losses into `δ^(-ε)`. -/
theorem rpowConstAbsorb (C : ℝ≥0) (hC : 1 ≤ C) {p e : ℝ} (hp : 0 ≤ p) (he : 0 < e) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ →
      (C : ENNReal) ^ p ≤ (δ : ENNReal) ^ (-e) := by
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hC
  have hC0_ne : C ≠ 0 := hC0.ne'
  have he_ne : e ≠ 0 := by linarith
  set δ₀ : ℝ≥0 := C ^ (-p / e) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := NNReal.rpow_pos hC0
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro δ hδ hδle
  -- lift δ ≤ δ₀ to ENNReal
  have hδle_coe : (δ : ENNReal) ≤ (δ₀ : ENNReal) := by exact mod_cast hδle
  have hδ0_ne : (δ : ENNReal) ≠ 0 := by exact mod_cast hδ.ne'
  have hδ_top_ne : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ₀_top_ne : (δ₀ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ₀_0_ne : (δ₀ : ENNReal) ≠ 0 := by exact mod_cast hδ₀_pos.ne'
  have hC_enn_ne0 : (C : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hC0_ne
  have hC_enn_ne_top : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- Step 1: show that (δ₀ : ENNReal)^(-e) = (C : ENNReal)^p
  have h_eq : (δ₀ : ENNReal) ^ (-e) = (C : ENNReal) ^ p := by
    calc
      (δ₀ : ENNReal) ^ (-e) = ((C : ENNReal) ^ (-p / e)) ^ (-e) := by
        rw [← ENNReal.coe_rpow_of_ne_zero hC0_ne (-p / e)]
      _ = (C : ENNReal) ^ ((-p / e) * (-e)) := by rw [ENNReal.rpow_mul]
      _ = (C : ENNReal) ^ p := by
        field_simp [he_ne]
  -- Step 2: use monotonicity of x ↦ x^e for e > 0, then invert
  have h_e_nonneg : 0 ≤ e := by linarith
  have h_pow_e : (δ : ENNReal) ^ e ≤ (δ₀ : ENNReal) ^ e :=
    ENNReal.rpow_le_rpow hδle_coe h_e_nonneg
  have h_inv : ((δ₀ : ENNReal) ^ e)⁻¹ ≤ ((δ : ENNReal) ^ e)⁻¹ :=
    (ENNReal.inv_le_inv.mpr h_pow_e)
  calc
    (C : ENNReal) ^ p = (δ₀ : ENNReal) ^ (-e) := by rw [h_eq]
    _ = ((δ₀ : ENNReal) ^ e)⁻¹ := by rw [ENNReal.rpow_neg]
    _ ≤ ((δ : ENNReal) ^ e)⁻¹ := h_inv
    _ = (δ : ENNReal) ^ (-e) := by rw [ENNReal.rpow_neg]

/-- Sub-identity for `combineLocalFactor_rpow`: extract the `Csplit` and `(a/b)` powers from
`(Csplit·(b/a))^(β/2)`. -/
theorem splitConstant_aspectRatio_rpow {β : ℝ} (Csplit a b : ℝ≥0) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Csplit * (b / a)) ^ (β / 2) = Csplit ^ (β / 2) * (a / b) ^ (-(β / 2)) := by
  rw [NNReal.mul_rpow]
  congr 1
  calc
    (b / a) ^ (β / 2) = ((a / b)⁻¹) ^ (β / 2) := by rw [← inv_div a b]
    _ = ((a / b) ^ (β / 2))⁻¹ := by rw [NNReal.inv_rpow]
    _ = (a / b) ^ (-(β / 2)) := by rw [← NNReal.rpow_neg (a / b) (β / 2)]

/-- Sub-identity for `combineLocalFactor_rpow`: `b^(-2β)·(a⁻¹δ)^(-2β) = (a/b)^(2β)·δ^(-2β)`. -/
theorem transverseScale_rpow {β : ℝ} (a b δ : ℝ≥0) (ha : a ≠ 0) (hb : b ≠ 0) (hδ : δ ≠ 0) :
    b ^ (-2 * β) * (a⁻¹ * δ) ^ (-2 * β) = (a / b) ^ (2 * β) * δ ^ (-2 * β) := by
  have h_inv_pow : (a⁻¹) ^ (-2 * β) = a ^ (2 * β) := by
    calc
      (a⁻¹) ^ (-2 * β) = (a ^ (-2 * β))⁻¹ := by rw [NNReal.inv_rpow]
      _ = (a ^ (-(2 * β)))⁻¹ := by ring
      _ = ((a ^ (2 * β))⁻¹)⁻¹ := by rw [NNReal.rpow_neg a (2 * β)]
      _ = a ^ (2 * β) := by simp
  have h_div_pow : (a / b) ^ (2 * β) = b ^ (-2 * β) * a ^ (2 * β) := by
    calc
      (a / b) ^ (2 * β) = a ^ (2 * β) / b ^ (2 * β) := by rw [NNReal.div_rpow]
      _ = a ^ (2 * β) * (b ^ (2 * β))⁻¹ := by rw [div_eq_mul_inv]
      _ = a ^ (2 * β) * b ^ (-(2 * β)) := by rw [NNReal.rpow_neg b (2 * β)]
      _ = a ^ (2 * β) * b ^ (-2 * β) := by ring
      _ = b ^ (-2 * β) * a ^ (2 * β) := mul_comm _ _
  calc
    b ^ (-2 * β) * (a⁻¹ * δ) ^ (-2 * β) = b ^ (-2 * β) * ((a⁻¹) ^ (-2 * β) * δ ^ (-2 * β)) := by
      rw [NNReal.mul_rpow]
    _ = (b ^ (-2 * β) * (a⁻¹) ^ (-2 * β)) * δ ^ (-2 * β) := by
      simp [mul_assoc]
    _ = (b ^ (-2 * β) * a ^ (2 * β)) * δ ^ (-2 * β) := by rw [h_inv_pow]
    _ = (a / b) ^ (2 * β) * δ ^ (-2 * β) := by rw [h_div_pow]

/-- Sub-identity for `combineLocalFactor_rpow`: the cardinality product; `|ts|` cancels and
`b²·a⁻²` becomes `(a/b)^(β-2)`. -/
theorem fibreCardinality_rpow {β : ℝ} (a b δ : ℝ≥0) (nq nts : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hδ : δ ≠ 0)
    (hnts : nts ≠ 0) :
    (b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2)
        * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)
      = (a / b) ^ (β - 2) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2) := by
  have hnts' : (nts : ℝ≥0) ≠ 0 := by exact_mod_cast hnts
  -- Write (nq/nts) as nq * (nts)⁻¹
  have hdiv : ((nq : ℝ≥0) / (nts : ℝ≥0)) = (nq : ℝ≥0) * ((nts : ℝ≥0)⁻¹) := div_eq_mul_inv _ _
  rw [hdiv]
  -- Combine the two ^(1-β/2) factors
  rw [← NNReal.mul_rpow (z := 1 - β / 2)]
  -- Inside: simplify the base product
  have hbase : b ^ 2 * (nts : ℝ≥0) * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) * ((nts : ℝ≥0)⁻¹))) =
    (a ^ 2)⁻¹ * b ^ 2 * (δ ^ 2 * (nq : ℝ≥0)) := by
    calc
      b ^ 2 * (nts : ℝ≥0) * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) * ((nts : ℝ≥0)⁻¹)))
          = b ^ 2 * ((a ^ 2)⁻¹ * δ ^ 2 * (nq : ℝ≥0)) * ((nts : ℝ≥0) * ((nts : ℝ≥0)⁻¹)) := by ring
      _ = b ^ 2 * ((a ^ 2)⁻¹ * δ ^ 2 * (nq : ℝ≥0)) * (1 : ℝ≥0) := by
        simp [hnts']
      _ = (a ^ 2)⁻¹ * b ^ 2 * (δ ^ 2 * (nq : ℝ≥0)) := by ring
  rw [hbase]
  -- Split back into product of two rpows
  rw [NNReal.mul_rpow (z := 1 - β / 2)]
  -- Now we have ((a^2)⁻¹ * b^2)^(1-β/2) * (δ^2 * (nq:ℝ≥0))^(1-β/2)
  congr 1
  · -- Show ((a^2)⁻¹ * b^2)^(1-β/2) = (a/b)^(β-2)
    have h_exponent : (-(2 : ℝ)) * (1 - β / 2) = β - 2 := by ring
    have h_factor : (a ^ 2)⁻¹ * b ^ 2 = (a / b) ^ (-(2 : ℝ)) := by
      calc
        (a ^ 2)⁻¹ * b ^ 2 = b ^ 2 / a ^ 2 := by field_simp [ha]
        _ = (b / a) ^ 2 := by simp [div_pow]
        _ = ((a / b)⁻¹) ^ 2 := by field_simp [ha, hb]
        _ = ((a / b)⁻¹) ^ (2 : ℝ) := by norm_cast
        _ = ((a / b) ^ (2 : ℝ))⁻¹ := by rw [NNReal.inv_rpow]
        _ = (a / b) ^ (-(2 : ℝ)) := by rw [NNReal.rpow_neg]
    calc
      ((a ^ 2)⁻¹ * b ^ 2) ^ (1 - β / 2) = ((a / b) ^ (-(2 : ℝ))) ^ (1 - β / 2) := by rw [h_factor]
      _ = (a / b) ^ ((-(2 : ℝ)) * (1 - β / 2)) := by
        rw [← NNReal.rpow_mul (a / b) (-(2 : ℝ)) (1 - β / 2)]
      _ = (a / b) ^ (β - 2) := by rw [h_exponent]

/-- Sub-identity for `combineLocalFactor_rpow`: the five `(a/b)` powers collapse to `(a/b)^(3β/2)`. -/
theorem aspectRatio_rpow_collect {β : ℝ} (x : ℝ≥0) (hx : x ≠ 0) :
    x ^ (-(β / 2)) * x * x ^ (1 - β) * x ^ (2 * β) * x ^ (β - 2) = x ^ (3 * β / 2) := by
  calc
    x ^ (-(β / 2)) * x * x ^ (1 - β) * x ^ (2 * β) * x ^ (β - 2)
        = (x ^ (-(β / 2)) * x ^ (1 : ℝ) * x ^ (1 - β) * x ^ (2 * β) * x ^ (β - 2)) := by
      nth_rw 2 [← NNReal.rpow_one x]
    _ = x ^ (-(β / 2) + (1 : ℝ) + (1 - β) + (2 * β) + (β - 2)) := by
      repeat' rw [← NNReal.rpow_add hx]
    _ = x ^ (3 * β / 2) := by
      congr 1
      ring

set_option maxHeartbeats 1000000 in
/-- **Factor-combination rpow identity, `ℝ≥0` form** (for GWZ 6.6(A)). The Frostman-constant-free
core of `combineLocalFactor`: the product of the μ-split factor, the outer 6.4 bound (without its
`CF^(1-β/2)`), and the inner factor collapses, after all rpow cancellations (the `|ts|` cancels,
`b²·a⁻²` folds into `(a/b)^(3β/2)`), to
`Csplit^(1+β/2)·a^(-ε/3)·δ^(-ε/3)·(a/b)^(3β/2)·δ^(-2β)·(δ²·nq)^(1-β/2)`.
Stated over `ℝ≥0` where rpow is unconditional. -/
theorem combineLocalFactor_rpow {β ε : ℝ} {a b δ Csplit : ℝ≥0} {nq nts : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hδ : δ ≠ 0) (hCs : Csplit ≠ 0) (hnts : nts ≠ 0) :
    Csplit * (a ^ (-(ε / 3)) * (Csplit * (b / a)) ^ (β / 2) * (a / b) * b ^ (-2 * β)
        * (b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
      * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
        * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2))
      = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3)) * δ ^ (-(ε / 3)) * (a / b) ^ (3 * β / 2)
        * δ ^ (-2 * β) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2) := by
  set AB := a / b with hAB
  have ha_div_b_ne_zero : AB ≠ 0 := div_ne_zero ha hb
  have hCs' : Csplit * Csplit ^ (β / 2) = Csplit ^ (1 + β / 2) := by
    calc
      Csplit * Csplit ^ (β / 2) = Csplit ^ (1 : ℝ) * Csplit ^ (β / 2) := by simp
      _ = Csplit ^ ((1 : ℝ) + β / 2) := by rw [← NNReal.rpow_add hCs (1 : ℝ) (β / 2)]
      _ = Csplit ^ (1 + β / 2) := by norm_num
  calc
    Csplit * (a ^ (-(ε / 3)) * (Csplit * (b / a)) ^ (β / 2) * (a / b) * b ^ (-2 * β)
        * (b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
      * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
        * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2))
    = Csplit * a ^ (-(ε / 3))
        * ((Csplit * (b / a)) ^ (β / 2))
        * (a / b) * b ^ (-2 * β)
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by ring
    _ = Csplit * a ^ (-(ε / 3))
        * (Csplit ^ (β / 2) * (a / b) ^ (-(β / 2)))
        * (a / b) * b ^ (-2 * β)
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by
      rw [splitConstant_aspectRatio_rpow Csplit a b ha hb]
    _ = Csplit * a ^ (-(ε / 3))
        * Csplit ^ (β / 2)
        * ((a / b) ^ (-(β / 2)) * (a / b))
        * b ^ (-2 * β)
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by ring
    _ = (Csplit * Csplit ^ (β / 2)) * a ^ (-(ε / 3))
        * ((a / b) ^ (-(β / 2)) * (a / b))
        * b ^ (-2 * β)
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by ring
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3))
        * ((a / b) ^ (-(β / 2)) * (a / b))
        * b ^ (-2 * β)
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by
      rw [hCs']
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3))
        * ((a / b) ^ (-(β / 2)) * (a / b))
        * (b ^ (-2 * β) * (a⁻¹ * δ) ^ (-2 * β))
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by ring
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3))
        * ((a / b) ^ (-(β / 2)) * (a / b))
        * ((a / b) ^ (2 * β) * δ ^ (-2 * β))
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by
      rw [transverseScale_rpow a b δ ha hb hδ]
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3))
        * ((a / b) ^ (-(β / 2)) * (a / b))
        * ((a / b) ^ (2 * β) * δ ^ (-2 * β))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β))
        * ((b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2)
          * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2)) := by ring
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3))
        * ((a / b) ^ (-(β / 2)) * (a / b))
        * ((a / b) ^ (2 * β) * δ ^ (-2 * β))
        * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β))
        * ((a / b) ^ (β - 2) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2)) := by
      rw [fibreCardinality_rpow a b δ nq nts ha hb hδ hnts]
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3)) * δ ^ (-(ε / 3))
        * ((a / b) ^ (-(β / 2)) * (a / b) * (a / b) ^ (1 - β) * (a / b) ^ (2 * β) * (a / b) ^ (β - 2))
        * δ ^ (-2 * β)
        * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2) := by
      ring
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3)) * δ ^ (-(ε / 3))
        * ((a / b) ^ (3 * β / 2))
        * δ ^ (-2 * β)
        * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2) := by
      rw [aspectRatio_rpow_collect (a / b) ha_div_b_ne_zero]
    _ = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3)) * δ ^ (-(ε / 3)) * (a / b) ^ (3 * β / 2)
        * δ ^ (-2 * β) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2) := rfl

set_option maxHeartbeats 1000000 in
/-- **Combination of the outer/inner factor bounds for GWZ 6.6(A)** (pure `ENNReal`/rpow algebra).
Given the multiplicity split `μqT ≤ Csplit · μW · INNER`, the outer-plank bound `h64out` for `μW`
coming from GWZ Lemma 6.4 with `M = Csplit·(b/a)`, the scale relation `δ ≤ a`, and the
constant-absorption threshold `Csplit^(1+β/2) ≤ δ^(-ε/3)`, the two factors combine (the `|ts|`
cardinalities cancel, and `b²·a⁻²` folds into `(a/b)^(3β/2)`) into the 6.6(A) bound. Not geometry. -/
theorem combineLocalFactor {β ε : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) (hε : 0 < ε)
    {a b δ : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (hδ0 : 0 < δ) (hδa : δ ≤ a)
    {Csplit : ℝ≥0} (hCs1 : 1 ≤ Csplit) {CF : ENNReal} (hCF1 : 1 ≤ CF) (hCFtop : CF ≠ ⊤)
    {nq nts : ℕ} (hnts : nts ≠ 0)
    {μqT μW : ENNReal}
    (h64out : μW ≤ (a : ENNReal) ^ (-(ε / 3)) * CF ^ (1 - β / 2)
        * ((Csplit * (b / a) : ℝ≥0) : ENNReal) ^ (β / 2) * ((a : ENNReal) / (b : ENNReal))
        * (b : ENNReal) ^ (-2 * β) * ((b : ENNReal) ^ 2 * (nts : ENNReal)) ^ (1 - β / 2))
    (hsplit : μqT ≤ (Csplit : ENNReal) * μW
        * ((δ : ENNReal) ^ (-(ε / 3)) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
          * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)
          * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * ((nq : ENNReal) / (nts : ENNReal)))
              ^ (1 - β / 2)))
    (hthr : (Csplit : ENNReal) ^ ((1 : ℝ) + β / 2) ≤ (δ : ENNReal) ^ (-(ε / 3))) :
    μqT ≤ (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
        * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
        * (δ : ENNReal) ^ (-2 * β)
        * ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2) := by
  -- Nonzero facts
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := (ha.trans_le hab).ne'
  have hδ0' : δ ≠ 0 := hδ0.ne'
  have hCs0 : Csplit ≠ 0 := by
    have hpos : (0 : ℝ≥0) < 1 := by norm_num
    have hpos' : 0 < Csplit := hpos.trans_le hCs1
    exact hpos'.ne'
  have hnts0 : (nts : ℝ≥0) ≠ 0 := by exact_mod_cast hnts
  -- Step 1: combine hsplit and h64out into a single bound
  have hstep : μqT ≤ (Csplit : ENNReal) * ((a : ENNReal) ^ (-(ε / 3)) * CF ^ (1 - β / 2)
      * ((Csplit * (b / a) : ℝ≥0) : ENNReal) ^ (β / 2) * ((a : ENNReal) / (b : ENNReal))
      * (b : ENNReal) ^ (-2 * β) * ((b : ENNReal) ^ 2 * (nts : ENNReal)) ^ (1 - β / 2))
      * ((δ : ENNReal) ^ (-(ε / 3)) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
        * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)
        * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * ((nq : ENNReal) / (nts : ENNReal)))
            ^ (1 - β / 2)) := by
    calc
      μqT ≤ (Csplit : ENNReal) * μW
          * ((δ : ENNReal) ^ (-(ε / 3)) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
            * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)
            * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * ((nq : ENNReal) / (nts : ENNReal)))
                ^ (1 - β / 2)) := hsplit
      _ ≤ (Csplit : ENNReal) * ((a : ENNReal) ^ (-(ε / 3)) * CF ^ (1 - β / 2)
          * ((Csplit * (b / a) : ℝ≥0) : ENNReal) ^ (β / 2) * ((a : ENNReal) / (b : ENNReal))
          * (b : ENNReal) ^ (-2 * β) * ((b : ENNReal) ^ 2 * (nts : ENNReal)) ^ (1 - β / 2))
          * ((δ : ENNReal) ^ (-(ε / 3)) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
            * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)
            * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * ((nq : ENNReal) / (nts : ENNReal)))
                ^ (1 - β / 2)) := by
        gcongr
  -- Step 2: the NNReal identity
  have hNN : Csplit * (a ^ (-(ε / 3)) * (Csplit * (b / a)) ^ (β / 2) * (a / b) * b ^ (-2 * β)
        * (b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2))
      * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β)
        * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2))
      = Csplit ^ (1 + β / 2) * a ^ (-(ε / 3)) * δ ^ (-(ε / 3)) * (a / b) ^ (3 * β / 2)
        * δ ^ (-2 * β) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2) :=
    combineLocalFactor_rpow ha0 hb0 hδ0' hCs0 hnts
  -- Step 3: rewrite the hstep RHS into the target form (without the Frostman constant factor)
  set hstepRHS := (Csplit : ENNReal) * ((a : ENNReal) ^ (-(ε / 3)) * CF ^ (1 - β / 2)
    * ((Csplit * (b / a) : ℝ≥0) : ENNReal) ^ (β / 2) * ((a : ENNReal) / (b : ENNReal))
    * (b : ENNReal) ^ (-2 * β) * ((b : ENNReal) ^ 2 * (nts : ENNReal)) ^ (1 - β / 2))
    * ((δ : ENNReal) ^ (-(ε / 3)) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
      * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)
      * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * ((nq : ENNReal) / (nts : ENNReal)))
          ^ (1 - β / 2)) with hhstepRHS
  have h_identity : hstepRHS = CF ^ (1 - β / 2)
      * ((Csplit : ENNReal) ^ ((1 : ℝ) + β / 2) * (a : ENNReal) ^ (-(ε / 3))
        * (δ : ENNReal) ^ (-(ε / 3)) * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
        * (δ : ENNReal) ^ (-2 * β) * ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2)) := by
    have hnn2 : (0 : ℝ) ≤ 1 - β / 2 := by linarith
    have hcoe_lhs : (((Csplit * (a ^ (-(ε / 3)) * (Csplit * (b / a)) ^ (β / 2) * (a / b) * b ^ (-2 * β) * (b ^ 2 * (nts : ℝ≥0)) ^ (1 - β / 2)) * (δ ^ (-(ε / 3)) * (a / b) ^ (1 - β) * (a⁻¹ * δ) ^ (-2 * β) * ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) ^ (1 - β / 2))) : ℝ≥0) : ENNReal)
        = (Csplit : ENNReal) * ((a : ENNReal) ^ (-(ε / 3)) * ((Csplit * (b / a) : ℝ≥0) : ENNReal) ^ (β / 2) * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β) * ((b : ENNReal) ^ 2 * (nts : ENNReal)) ^ (1 - β / 2)) * ((δ : ENNReal) ^ (-(ε / 3)) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β) * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * ((nq : ENNReal) / (nts : ENNReal))) ^ (1 - β / 2)) := by
      have ha_sq0 : (a : ℝ≥0) ^ 2 ≠ 0 := pow_ne_zero 2 ha0
      simp [ENNReal.coe_mul, ENNReal.coe_div hb0, ENNReal.coe_div hnts0,
        ENNReal.coe_inv ha0, ENNReal.coe_inv hb0, ENNReal.coe_inv hnts0, ENNReal.coe_inv ha_sq0,
        ENNReal.coe_rpow_of_ne_zero ha0, ENNReal.coe_rpow_of_ne_zero hb0,
        ENNReal.coe_rpow_of_ne_zero hδ0', ENNReal.coe_rpow_of_ne_zero hCs0,
        ENNReal.coe_rpow_of_ne_zero (div_ne_zero ha0 hb0),
        ENNReal.coe_rpow_of_ne_zero (mul_ne_zero (inv_ne_zero ha0) hδ0'),
        ENNReal.coe_rpow_of_ne_zero (mul_ne_zero hCs0 (div_ne_zero hb0 ha0)),
        ENNReal.coe_rpow_of_ne_zero (mul_ne_zero (pow_ne_zero 2 hb0) hnts0),
        ENNReal.coe_rpow_of_nonneg ((a ^ 2)⁻¹ * δ ^ 2 * ((nq : ℝ≥0) / (nts : ℝ≥0))) hnn2]
    have hcoe_rhs : (((Csplit ^ (1 + β / 2) * a ^ (-(ε / 3)) * δ ^ (-(ε / 3)) * (a / b) ^ (3 * β / 2) * δ ^ (-2 * β) * (δ ^ 2 * (nq : ℝ≥0)) ^ (1 - β / 2)) : ℝ≥0) : ENNReal)
        = (Csplit : ENNReal) ^ ((1 : ℝ) + β / 2) * (a : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)) * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) * (δ : ENNReal) ^ (-2 * β) * ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2) := by
      simp [ENNReal.coe_mul, ENNReal.coe_div hb0, ENNReal.coe_inv ha0, ENNReal.coe_inv hb0,
        ENNReal.coe_rpow_of_ne_zero ha0, ENNReal.coe_rpow_of_ne_zero hb0,
        ENNReal.coe_rpow_of_ne_zero hδ0', ENNReal.coe_rpow_of_ne_zero hCs0,
        ENNReal.coe_rpow_of_ne_zero (div_ne_zero ha0 hb0),
        ENNReal.coe_rpow_of_nonneg (δ ^ 2 * (nq : ℝ≥0)) hnn2]
    rw [hhstepRHS, ← hcoe_rhs, ← hNN, hcoe_lhs]
    ring
  -- Now hstep gives μqT ≤ hstepRHS = CF^(1-β/2) * (Csplit^(1+β/2) * a^(-(ε/3)) * δ^(-(ε/3)) *...)
  have hstep' : μqT ≤ CF ^ (1 - β / 2)
      * ((Csplit : ENNReal) ^ ((1 : ℝ) + β / 2) * (a : ENNReal) ^ (-(ε / 3))
        * (δ : ENNReal) ^ (-(ε / 3)) * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
        * (δ : ENNReal) ^ (-2 * β) * ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2)) :=
    hstep.trans h_identity.le
  -- Step 4: the δ ≤ a implies a^(-(ε/3)) ≤ δ^(-(ε/3))
  have h_a_pow_inv : (a : ENNReal) ^ (-(ε / 3)) ≤ (δ : ENNReal) ^ (-(ε / 3)) := by
    have hδa_enn : (δ : ENNReal) ≤ (a : ENNReal) := by exact mod_cast hδa
    have h_nonneg : 0 ≤ ε / 3 := by nlinarith
    calc
      (a : ENNReal) ^ (-(ε / 3)) = ((a : ENNReal)⁻¹) ^ (ε / 3) := by
        rw [ENNReal.rpow_neg, ENNReal.inv_rpow]
      _ ≤ ((δ : ENNReal)⁻¹) ^ (ε / 3) := by
        refine ENNReal.rpow_le_rpow ?_ h_nonneg
        exact (ENNReal.inv_le_inv.mpr hδa_enn)
      _ = (δ : ENNReal) ^ (-(ε / 3)) := by
        rw [ENNReal.rpow_neg, ENNReal.inv_rpow]
  -- Step 5: δ^(-ε) splits into three factors
  have h_delta_pow_split : (δ : ENNReal) ^ (-ε)
      = (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)) := by
    have hδ_nonzero : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0'
    have hδ_not_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    calc
      (δ : ENNReal) ^ (-ε) = (δ : ENNReal) ^ (-(ε / 3) + (-(ε / 3)) + (-(ε / 3))) := by ring
      _ = ((δ : ENNReal) ^ (-(ε / 3) + (-(ε / 3)))) * (δ : ENNReal) ^ (-(ε / 3)) := by
        rw [ENNReal.rpow_add (-(ε / 3) + (-(ε / 3))) (-(ε / 3)) hδ_nonzero hδ_not_top]
      _ = ((δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3))) * (δ : ENNReal) ^ (-(ε / 3)) := by
        rw [ENNReal.rpow_add (-(ε / 3)) (-(ε / 3)) hδ_nonzero hδ_not_top]
      _ = (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)) := by ring
  -- Step 6: key inequality using hthr and h_a_pow_inv
  have h_key_ineq : (Csplit : ENNReal) ^ ((1 : ℝ) + β / 2) * (a : ENNReal) ^ (-(ε / 3))
      * (δ : ENNReal) ^ (-(ε / 3)) ≤ (δ : ENNReal) ^ (-ε) := by
    calc
      (Csplit : ENNReal) ^ ((1 : ℝ) + β / 2) * (a : ENNReal) ^ (-(ε / 3))
          * (δ : ENNReal) ^ (-(ε / 3))
        ≤ (δ : ENNReal) ^ (-(ε / 3)) * (a : ENNReal) ^ (-(ε / 3))
          * (δ : ENNReal) ^ (-(ε / 3)) := by
          gcongr
        _ = ((a : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)))
          * (δ : ENNReal) ^ (-(ε / 3)) := by ring
        _ ≤ ((δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)))
          * (δ : ENNReal) ^ (-(ε / 3)) := by
          gcongr
        _ = (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)) := by ring
        _ = (δ : ENNReal) ^ (-ε) := by rw [h_delta_pow_split]
  -- Step 7: final inequality
  calc
    μqT ≤ CF ^ (1 - β / 2)
        * ((Csplit : ENNReal) ^ ((1 : ℝ) + β / 2) * (a : ENNReal) ^ (-(ε / 3))
          * (δ : ENNReal) ^ (-(ε / 3)) * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
          * (δ : ENNReal) ^ (-2 * β) * ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2)) :=
      hstep'
    _ = CF ^ (1 - β / 2) * ((Csplit : ENNReal) ^ ((1 : ℝ) + β / 2) * (a : ENNReal) ^ (-(ε / 3))
        * (δ : ENNReal) ^ (-(ε / 3))) * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
        * (δ : ENNReal) ^ (-2 * β) * ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2) := by
      ring
    _ ≤ CF ^ (1 - β / 2) * (δ : ENNReal) ^ (-ε) * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
        * (δ : ENNReal) ^ (-2 * β) * ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2) := by
      gcongr
    _ = (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
        * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
        * (δ : ENNReal) ^ (-2 * β)
        * ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2) := by ring

/-- **Absorbing the Frostman-transfer constant, high branch of GWZ Proposition 6.6(A).**

The `μ`-split hands Lemma 6.4 the transferred Frostman constant `Csplit · C_F` rather than `C_F`, so
after `Kakeya.combineLocalFactor` the bound carries `(Csplit · C_F) ^ (1 - β/2)` and a `δ ^ (-3ε/4)`.
Splitting the power and absorbing `Csplit ^ (1 - β/2)` into the remaining `δ ^ (-ε/4)` restores the
target shape.

The three trailing factors are abstract: in the application `Q = (a/b) ^ (3β/2)`,
`R = δ ^ (-2β)`, `S = (δ² |𝒯|) ^ (1 - β/2)`. Keeping them opaque is deliberate — it makes visible
that this step cannot disturb the eccentricity exponent `3β/2`. -/
theorem absorbSplitFrostmanConstant {β ε : ℝ} (hβle : β ≤ 1) {δ : ℝ≥0} (hδ0 : 0 < δ)
    {Csplit : ℝ≥0} {CF Q R S μ : ENNReal}
    (hthr2 : (Csplit : ENNReal) ^ (1 - β / 2) ≤ (δ : ENNReal) ^ (-(ε / 4)))
    (h : μ ≤ (δ : ENNReal) ^ (-(3 * ε / 4)) * ((Csplit : ENNReal) * CF) ^ (1 - β / 2)
          * Q * R * S) :
    μ ≤ (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * Q * R * S := by
  have hδ_nonzero : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδ_not_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h_δ_split : (δ : ENNReal) ^ (-ε) =
      (δ : ENNReal) ^ (-(3 * ε / 4)) * (δ : ENNReal) ^ (-(ε / 4)) := by
    calc
      (δ : ENNReal) ^ (-ε) = (δ : ENNReal) ^ ((-(3 * ε / 4)) + (-(ε / 4))) := by
        rw [show -ε = -(3 * ε / 4) + -(ε / 4) by ring]
      _ = (δ : ENNReal) ^ (-(3 * ε / 4)) * (δ : ENNReal) ^ (-(ε / 4)) :=
        ENNReal.rpow_add (-(3 * ε / 4)) (-(ε / 4)) hδ_nonzero hδ_not_top
  have h_CF_split : ((Csplit : ENNReal) * CF) ^ (1 - β / 2) =
      (Csplit : ENNReal) ^ (1 - β / 2) * CF ^ (1 - β / 2) := by
    have h_nonneg : 0 ≤ 1 - β / 2 := by linarith
    rw [ENNReal.mul_rpow_of_nonneg _ _ h_nonneg]
  calc
    μ ≤ (δ : ENNReal) ^ (-(3 * ε / 4)) * ((Csplit : ENNReal) * CF) ^ (1 - β / 2)
        * Q * R * S := h
    _ = ((Csplit : ENNReal) * CF) ^ (1 - β / 2) * (δ : ENNReal) ^ (-(3 * ε / 4))
        * Q * R * S := by ring
    _ = (CF ^ (1 - β / 2) * (Csplit : ENNReal) ^ (1 - β / 2)) * (δ : ENNReal) ^ (-(3 * ε / 4))
        * Q * R * S := by
      rw [h_CF_split]
      ring
    _ = CF ^ (1 - β / 2) * ((Csplit : ENNReal) ^ (1 - β / 2) * (δ : ENNReal) ^ (-(3 * ε / 4)))
        * Q * R * S := by ring
    _ ≤ CF ^ (1 - β / 2) * ((δ : ENNReal) ^ (-(ε / 4)) * (δ : ENNReal) ^ (-(3 * ε / 4)))
        * Q * R * S := by
      gcongr
    _ = CF ^ (1 - β / 2) * (δ : ENNReal) ^ (-ε) * Q * R * S := by
      calc
        CF ^ (1 - β / 2) * ((δ : ENNReal) ^ (-(ε / 4)) * (δ : ENNReal) ^ (-(3 * ε / 4)))
            * Q * R * S
        = CF ^ (1 - β / 2) * ((δ : ENNReal) ^ (-(3 * ε / 4)) * (δ : ENNReal) ^ (-(ε / 4)))
            * Q * R * S := by ring
        _ = CF ^ (1 - β / 2) * ((δ : ENNReal) ^ ((-(3 * ε / 4)) + (-(ε / 4))))
            * Q * R * S := by
          rw [ENNReal.rpow_add (-(3 * ε / 4)) (-(ε / 4)) hδ_nonzero hδ_not_top]
        _ = CF ^ (1 - β / 2) * (δ : ENNReal) ^ (-ε) * Q * R * S := by
          rw [show -(3 * ε / 4) + -(ε / 4) = -ε by ring]
    _ = (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * Q * R * S := by ring

/-- **Absorbing the coarse-slab loss, low branch of GWZ Proposition 6.6(A).**

In the large-`b` regime `Kakeya.coarseSlabFallback` returns the target bound premultiplied by a fixed
loss `Ccoarse`; below a threshold that loss is at most `δ ^ (-ε/2)`, and the two half-powers of `δ`
combine. As above the trailing factors are opaque, so the eccentricity exponent cannot be
disturbed. -/
theorem absorbCoarseConstant {ε : ℝ} {δ : ℝ≥0} (hδ0 : 0 < δ)
    {Ccoarse : ℝ≥0} {P Q R S μ : ENNReal}
    (hco : (Ccoarse : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 2)))
    (h : μ ≤ (Ccoarse : ENNReal) * ((δ : ENNReal) ^ (-(ε / 2)) * P * Q * R * S)) :
    μ ≤ (δ : ENNReal) ^ (-ε) * P * Q * R * S := by
  have hδ_nonzero : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδ_not_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h_δ_split : (δ : ENNReal) ^ (-ε)
      = (δ : ENNReal) ^ (-(ε / 2)) * (δ : ENNReal) ^ (-(ε / 2)) := by
    rw [← ENNReal.rpow_add _ _ hδ_nonzero hδ_not_top]; ring_nf
  calc
    μ ≤ (Ccoarse : ENNReal) * ((δ : ENNReal) ^ (-(ε / 2)) * P * Q * R * S) := h
    _ = ((Ccoarse : ENNReal) * (δ : ENNReal) ^ (-(ε / 2))) * P * Q * R * S := by ring
    _ ≤ ((δ : ENNReal) ^ (-(ε / 2)) * (δ : ENNReal) ^ (-(ε / 2))) * P * Q * R * S := by gcongr
    _ = (δ : ENNReal) ^ (-ε) * P * Q * R * S := by rw [h_δ_split]

/-- **The whole small-`b` branch of GWZ Proposition 6.6(A), as scalar algebra.**

Everything geometric has already happened: `h64out` is the corrected Lemma 6.4 output for the outer
plank family, with concentration parameter `M = Cbig · (b/a)` where `Cbig = Cgeom · Cu · Csplit` is
the cross-parent loss, and Frostman constant the transferred `Csplit · C_F`; `hsplitineq` is the
Proposition 5.1 `μ`-split with its inner rescaled-tube factor.

Two constants have to be absorbed, and they are absorbed separately, which is the point of stating
this as its own lemma:

* `hthrBig` absorbs `Cbig ^ (1 + β/2)` — the `Cbig` that `Kakeya.combineLocalFactor` pays once for
  the split and once more as `M ^ (β/2)`.  This is the *only* new contribution of the cross-parent
  repair, and `Kakeya.crossParentThreshold` supplies it.
* `hthr2` absorbs `Csplit ^ (1 - β/2)`, the pre-existing Frostman-transfer loss.

The eccentricity factor `(a/b) ^ (3β/2)` in the conclusion is produced by
`Kakeya.combineLocalFactor` from `(a/b) ^ (-(β/2)) · (a/b) · (a/b) ^ (1-β)` and is untouched by
either absorption step (both go through `Kakeya.absorbSplitFrostmanConstant`, whose trailing factors
are opaque). -/
theorem localHighBranchBound {β ε : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) (hε : 0 < ε)
    {δ a b : ℝ≥0} (hδ0 : 0 < δ) (ha_pos : 0 < a) (hab : a ≤ b) (hδa : δ ≤ a)
    {Csplit Cbig : ℝ≥0} (hCs1 : 1 ≤ Csplit) (hCsb : Csplit ≤ Cbig) (hCb1 : 1 ≤ Cbig)
    {CF : ENNReal} (hCF1 : 1 ≤ CF) (hCFtop : CF ≠ ⊤)
    {nq nts : ℕ} (hnts : nts ≠ 0)
    {μqT μW : ENNReal}
    (h64out : μW ≤ (a : ENNReal) ^ (-(ε / 4)) * ((Csplit : ENNReal) * CF) ^ (1 - β / 2)
        * ((Cbig * (b / a) : ℝ≥0) : ENNReal) ^ (β / 2) * ((a : ENNReal) / (b : ENNReal))
        * (b : ENNReal) ^ (-2 * β) * ((b : ENNReal) ^ 2 * (nts : ENNReal)) ^ (1 - β / 2))
    (hsplitineq : μqT ≤ (Csplit : ENNReal) * μW
        * ((δ : ENNReal) ^ (-(ε / 4)) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
          * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)
          * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * ((nq : ENNReal) / (nts : ENNReal)))
              ^ (1 - β / 2)))
    (hthrBig : (Cbig : ENNReal) ^ ((1 : ℝ) + β / 2) ≤ (δ : ENNReal) ^ (-(ε / 4)))
    (hthr2 : (Csplit : ENNReal) ^ (1 - β / 2) ≤ (δ : ENNReal) ^ (-(ε / 4))) :
    μqT ≤ (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
        * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
        * (δ : ENNReal) ^ (-2 * β)
        * ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2) := by
  -- Step 1: combineLocalFactor wants the same constant in `hsplitineq` as in `h64out`'s
  -- `(Cbig * (b/a))^(β/2)` concentration factor, so weaken the split constant `Csplit` to `Cbig`.
  have hsplitBig : μqT ≤ (Cbig : ENNReal) * μW
      * ((δ : ENNReal) ^ (-(ε / 4)) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
        * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)
        * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * ((nq : ENNReal) / (nts : ENNReal)))
            ^ (1 - β / 2)) := by
    calc
      μqT ≤ (Csplit : ENNReal) * μW
          * ((δ : ENNReal) ^ (-(ε / 4)) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
            * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)
            * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * ((nq : ENNReal) / (nts : ENNReal)))
                ^ (1 - β / 2)) := hsplitineq
      _ ≤ (Cbig : ENNReal) * μW
          * ((δ : ENNReal) ^ (-(ε / 4)) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
            * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)
            * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * ((nq : ENNReal) / (nts : ENNReal)))
                ^ (1 - β / 2)) := by
        gcongr
  -- Step 2: rewrite the exponents so that `combineLocalFactor` applies with `ε' = 3ε/4`
  have h_eq : (3 * ε / 4) / 3 = ε / 4 := by ring
  have h64out' : μW ≤ (a : ENNReal) ^ (-((3 * ε / 4) / 3)) * ((Csplit : ENNReal) * CF) ^ (1 - β / 2)
      * ((Cbig * (b / a) : ℝ≥0) : ENNReal) ^ (β / 2) * ((a : ENNReal) / (b : ENNReal))
      * (b : ENNReal) ^ (-2 * β) * ((b : ENNReal) ^ 2 * (nts : ENNReal)) ^ (1 - β / 2) := by
    simpa [h_eq] using h64out
  have hsplitineq' : μqT ≤ (Cbig : ENNReal) * μW
      * ((δ : ENNReal) ^ (-((3 * ε / 4) / 3)) * ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
        * ((a : ENNReal)⁻¹ * (δ : ENNReal)) ^ (-2 * β)
        * (((a : ENNReal) ^ 2)⁻¹ * (δ : ENNReal) ^ 2 * ((nq : ENNReal) / (nts : ENNReal)))
            ^ (1 - β / 2)) := by
    simpa [h_eq] using hsplitBig
  have hthr_combined : (Cbig : ENNReal) ^ ((1 : ℝ) + β / 2)
      ≤ (δ : ENNReal) ^ (-((3 * ε / 4) / 3)) := by
    simpa [h_eq] using hthrBig
  -- Step 3: apply `combineLocalFactor` with `ε' = 3ε/4` and the transferred Frostman constant
  have hε'pos : 0 < 3 * ε / 4 := by nlinarith
  have hCsplit_enn : 1 ≤ (Csplit : ENNReal) := by exact_mod_cast hCs1
  have hCFsplit1 : 1 ≤ (Csplit : ENNReal) * CF := by
    calc
      (1 : ENNReal) ≤ (Csplit : ENNReal) := hCsplit_enn
      _ = (Csplit : ENNReal) * (1 : ENNReal) := by simp
      _ ≤ (Csplit : ENNReal) * CF := mul_le_mul_of_nonneg_left hCF1 (by positivity)
  have hCFsplit_top : (Csplit : ENNReal) * CF ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hCFtop
  have h_combined : μqT ≤ (δ : ENNReal) ^ (-(3 * ε / 4)) * ((Csplit : ENNReal) * CF) ^ (1 - β / 2)
      * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
      * (δ : ENNReal) ^ (-2 * β)
      * ((δ : ENNReal) ^ 2 * (nq : ENNReal)) ^ (1 - β / 2) :=
    combineLocalFactor hβpos hβle hε'pos ha_pos hab hδ0 hδa (Csplit := Cbig) hCb1
      (CF := (Csplit : ENNReal) * CF) hCFsplit1 hCFsplit_top hnts
      (h64out := h64out') (hsplit := hsplitineq') (hthr := hthr_combined)
  -- Step 4: absorb the Frostman-transfer constant `Csplit ^ (1 - β/2)` into `δ ^ (-ε/4)`
  exact absorbSplitFrostmanConstant hβle hδ0 hthr2 h_combined

/-! ### Conditional analytic assembly

The following implication takes `Section6PartAAnalyticAssembly β` as an explicit
hypothesis. It also assumes `ParentOverlapAtDilatedPlanks`, which does not follow
from the parent system's bounded overlap alone. These assumptions describe the
analytic and geometric inputs of the implication.
-/
/-- **GWZ Proposition 6.6(A).**
Suppose the partial estimates `K_KT(β)` and `K_F(β)` hold. For every `ε > 0` there are `η > 0`
and `δ₀ > 0` with the following property. Let `0 < δ ≤ δ₀`, and let `𝒯 = (T i)_{i ∈ q}` be a uniform
family of `δ`-tubes with shading in `B₁` satisfying `λ(𝒯, Y) ≥ δ ^ η`. Suppose there is a coarse
scale `ρ` with a family of `ρ`-tubes `(R k)_{k ∈ r}` such that each fine tube lies in a coarse tube
(via `assign`), and for every coarse index `k` the fine tubes assigned to `R k` admit a
factorization (`Fz k`) whose outer bodies are `a × b × 1` planks. Then
`μ(𝒯, Y) ≤ δ ^ (-ε) · C_F(𝒯) ^ (1 - β/2) · (a/b) ^ (3β/2) · δ ^ (-2β) · (δ² |𝒯|) ^ (1 - β/2)`,
where `C_F(𝒯)` is carried by `CF`.

The plank factorisation is modelled through `Kakeya.PlankFactorization`, one per coarse `ρ`-tube
(the *local* case), which bundles a `ConvexSpaceBody.Factorization` with the requirement that each
part's outer convex body is an `a × b × 1` plank.

**Scale hypotheses.**  The former hypothesis `ρ ≤ a` has been deleted: it is *false* for this
configuration.  The outer bodies of `Fz k` are convex hulls of subfamilies of the fine tubes
assigned to `R k`, hence are contained in the convex set `R k`, and a body of transverse half-width
`b` inside a `ρ`-tube has `b ≲ ρ`.  Together with `ρ ≤ a ≤ b` that would force `a ≍ b ≍ ρ` and make
the conclusion's `(a/b) ^ (3β/2)` gain vacuous.  No replacement hypothesis is added: `b ≤ 2 * ρ` is
*derived* inside the proof by `Kakeya.b_le_two_mul_of_comparableBodyFactorization` from the factorisation
and the parent containment `hassign`, and handed to `Kakeya.factoringAndMultPropCombined`.

**The factorisation datum.**  `Fz` is a `Kakeya.ComparableBodyFactorization`, not a
`Kakeya.PlankFactorization`.  The latter's exact `parts_are_planks` equality made each outer body an
exact `Prism3D a b 1`, of longitudinal extent `2` because `Prism3D` records half-widths; a `Tube ρ`
has diameter at most `1 + 2ρ`, so an outer body inside its coarse parent forced `1/2 ≤ ρ`
(`Kakeya.Plank.half_le_of_le_tube`) and the hypotheses of this proposition were *unsatisfiable* at
every small scale.  `ComparableBodyFactorization` keeps the hull structure and the Katz--Tao property but
replaces that equality by the transverse lower bound `Kakeya.ContainsFlatDisc`, which is all the
Scale comparison consumes.  The representative plank family `(W j)` handed to GWZ Lemma 6.4 and the actual
factor bodies `H` are now distinct objects, related only by fixed-constant comparability; conflating
them was the normalisation bug.

Proposition 6.6(B) keeps its `ρ ≤ a`: there the `ρ`-tubes themselves are the inner bodies of a
single factorisation by the outer planks, so the containment runs the other way.

**Cross-parent overlap at the exact dilated test bodies.**  The cross-parent count is a hypothesis
of this proposition, supplied once for all as `Kakeya.ParentOverlapAtDilatedPlanks PS hab hb1 C Cu'`:
for the `C`-dilation of the thickened plank-shaped test body `P` and every `θ ≥ a / b`, at most
`Cu'` parents own a fine leaf meeting it.  This datum is strictly stronger than the parent system's
own `Kakeya.ExternalParentSystem.boundedOverlapThroughLeaves` (which counts leaves at a
`Kakeya.crossParentTestConst C _ * ρ`-test-tube radius) and is *not* implied by it —
`Kakeya.not_isThickeningNonconcentrated_of_testTubeOverlap` exhibits parent overlap `1` at every
test-tube radius for which this proposition's non-concentration step then fails.  The parent scale
stays `ρ`: `PS.parentTube` is still a `Tube ρ`, `Fz` is still indexed by the original `PS.parents`,
and `par x` is still the original external label. -/
theorem tubeMultiplicityOfLocalPlankFactorisation_of_analyticAssembly {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hAnalytic : Section6PartAAnalyticAssembly.{u_section6Estimate} β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
      ∀ {ι : Type u_section6Estimate} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        δ ≤ δ₀ →
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∃ C : ℝ≥0, 1 ≤ C ∧ C ≤ δ ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet q T
            (Tube.ssfGridLen δ) C)) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1),
          δ ≤ ρ → ρ ≤ 1 →
          ∀ (Cu : ℝ≥0), 1 ≤ Cu → Cu ≤ δ ^ (-η) →
            ∀ (PS : ExternalParentSystem q (fun i => (T i).toTube) ρ Cu),
            (∀ C : ℝ≥0, 1 ≤ C → ∃ Cu' : ℝ≥0, 1 ≤ Cu' ∧ Cu' ≤ δ ^ (-η) ∧
              ParentOverlapAtDilatedPlanks PS hab hb1 C Cu') →
          ∀ (C₀ : ℝ≥0), C₀ ≤ δ ^ (-η) →
            ∀ (Fz : ∀ k ∈ PS.parents, ComparableBodyFactorization b
              {i ∈ q | PS.assign i = k} (fun i => (T i).toConvexSpaceBody) C₀),
          ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
            IsFrostmanIn q (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall CF →
            ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
              (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
                * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
                * (δ : ENNReal) ^ (-2 * β)
                * ((δ : ENNReal) ^ 2 * (q.card : ENNReal)) ^ (1 - β / 2) := by
  obtain ⟨C_NC, hC_NC, h64All⟩ := FrostmanEstimate.plankEstimate hβpos hβle hKF
  intro ε hε
  obtain ⟨η6, hη6, b₀₆, hb₀₆, h64⟩ := h64All (ε/4) (by positivity)
  obtain ⟨Csplit, hCs1, hsplit⟩ :=
    section6PartAAnalyticAssembly hβpos hβle C_NC hC_NC hAnalytic
  obtain ⟨ηFine, hηFine, hcfg⟩ := hsplit (ε/4) (by positivity) η6 hη6
  obtain ⟨δ₀cp, hδ₀cp, hcpthr⟩ := crossParentThreshold hβpos hβle hε 1 Csplit le_rfl hCs1
  obtain ⟨δ₀thr2, hδ₀thr2, hthrfun2⟩ :=
    rpowConstAbsorb Csplit hCs1 (show (0 : ℝ) ≤ 1 - β / 2 by linarith)
      (show (0 : ℝ) < ε/4 by positivity)
  obtain ⟨Ccoarse, hCcoarse, ηfall, hηfall, hfall⟩ :=
    coarseSlabFallback hβpos hβle hKKT hKF hAnalytic
      (show (0 : ℝ) < ε/2 by positivity) b₀₆ hb₀₆
  obtain ⟨δ₀co, hδ₀co, hcofun⟩ :=
    rpowConstAbsorb Ccoarse hCcoarse (show (0 : ℝ) ≤ 1 by norm_num)
      (show (0 : ℝ) < ε/2 by positivity)
  let η₀ : ℝ := min (min (min ηFine η6) ηfall) (ε / 12)
  have hη₀pos : 0 < η₀ := by
    dsimp [η₀]
    exact lt_min (lt_min (lt_min hηFine hη6) hηfall) (by positivity)
  have hη₀le : η₀ ≤ ε / 12 := by
    dsimp [η₀]
    exact min_le_right _ _
  let δ₀ : ℝ≥0 := min (min δ₀cp δ₀thr2) (min δ₀co 1)
  have hδ₀pos : 0 < δ₀ := by
    dsimp [δ₀]
    exact lt_min (lt_min hδ₀cp hδ₀thr2) (lt_min hδ₀co (by norm_num))
  refine ⟨η₀, hη₀pos, δ₀, hδ₀pos, ?_⟩
  intro ι q δ hδ0 T hδδ₀ hball huniform hfull ρ a b hab hb1 hδρ hρ1
    Cu hCu1 hCuδ PS hparOv C₀ hC₀η Fz CF hCF1 hCFtop hFrost
  obtain ⟨Cu', hCu'1, hCu'δ, hoverP⟩ := hparOv C_NC hC_NC
  rcases q.eq_empty_or_nonempty with rfl | hq
  · simp
  have hassign : ∀ i ∈ q, PS.assign i ∈ PS.parents ∧
      (T i).toConvexSpaceBody ≤ (PS.parentTube (PS.assign i)).toConvexSpaceBody :=
    fun i hi => ⟨PS.assign_mem i hi, PS.leaf_le_parent i hi⟩
  have hbρ : b ≤ 2 * ρ := b_le_two_mul_of_comparableBodyFactorization hb1 hq hassign Fz
  have hδ1 : δ ≤ 1 := hδρ.trans hρ1
  have hδδ₀cp : δ ≤ δ₀cp :=
    hδδ₀.trans ((min_le_left (min δ₀cp δ₀thr2) (min δ₀co 1)).trans (min_le_left δ₀cp δ₀thr2))
  have hδδ₀thr2 : δ ≤ δ₀thr2 :=
    hδδ₀.trans ((min_le_left (min δ₀cp δ₀thr2) (min δ₀co 1)).trans (min_le_right δ₀cp δ₀thr2))
  have hδδ₀co : δ ≤ δ₀co :=
    hδδ₀.trans ((min_le_right (min δ₀cp δ₀thr2) (min δ₀co 1)).trans (min_le_left δ₀co 1))
  have hmin_le : min (min (min ηFine η6) ηfall) (ε / 12) ≤ ηFine :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left ηFine η6))
  have hmin_le_fall : min (min (min ηFine η6) ηfall) (ε / 12) ≤ ηfall :=
    (min_le_left _ _).trans (min_le_right _ _)
  -- the same hypotheses read at the fallback's exponent `ηfall`
  have hfullF : (δ : ℝ≥0) ^ ηfall ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) :=
    (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hmin_le_fall).trans hfull
  have huniformF : ∃ C : ℝ≥0, 1 ≤ C ∧ C ≤ δ ^ (-ηfall) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet q T (Tube.ssfGridLen δ) C) := by
    rcases huniform with ⟨C, hC1, hC, huni⟩
    exact ⟨C, hC1, hC.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1
      (by linarith [hmin_le_fall])), huni⟩
  have hC₀ηF : C₀ ≤ δ ^ (-ηfall) :=
    hC₀η.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith [hmin_le_fall]))
  have hfull' : (δ : ℝ≥0) ^ ηFine ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) :=
    (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hmin_le).trans hfull
  have huniform' : ∃ C : ℝ≥0, 1 ≤ C ∧ C ≤ δ ^ (-ηFine) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet q T (Tube.ssfGridLen δ) C) := by
    rcases huniform with ⟨C, hC1, hC, huni⟩
    refine ⟨C, hC1, ?_, huni⟩
    have h_neg : -ηFine ≤ -(min (min (min ηFine η6) ηfall) (ε / 12)) := by
      linarith [hmin_le]
    calc
      C ≤ δ ^ (-(min (min (min ηFine η6) ηfall) (ε / 12))) := hC
      _ ≤ δ ^ (-ηFine) := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 h_neg
  have hC₀η' : C₀ ≤ δ ^ (-ηFine) := by
    have h_neg : -ηFine ≤ -(min (min (min ηFine η6) ηfall) (ε / 12)) := by
      linarith [hmin_le]
    calc
      C₀ ≤ δ ^ (-(min (min (min ηFine η6) ηfall) (ε / 12))) := hC₀η
      _ ≤ δ ^ (-ηFine) := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 h_neg
  by_cases hbcase : b ≤ b₀₆
  · obtain ⟨Cunif, hCunif1, hCunifδ, ⟨𝒱⟩⟩ := huniform
    have hCunifδ' : Cunif ≤ δ ^ (-ηFine) := by
      have h_neg : -ηFine ≤ -(min (min (min ηFine η6) ηfall) (ε / 12)) := by
        linarith [hmin_le]
      calc
        Cunif ≤ δ ^ (-(min (min (min ηFine η6) ηfall) (ε / 12))) := hCunifδ
        _ ≤ δ ^ (-ηFine) := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 h_neg
    obtain ⟨ha_pos, hδa, hrest⟩ := hcfg q hδ0 T hball Cunif hCunif1 hCunifδ' 𝒱 hfull'
        ρ a b hab hb1 Cu PS hδρ hρ1 hbρ C₀ hC₀η' Fz CF hCF1 hCFtop hFrost
    rcases hrest with ⟨κ', ts, W, hts_ne, hWball, hWed, hWfull,
      ⟨par, H, hpar_mem, hocc, hbodyW, -, hloc⟩, hWfrost, hsplitineq⟩
    have hba1 : (1 : ℝ≥0) ≤ b / a := by
      have ha' : (a : ℝ) > 0 := by exact_mod_cast ha_pos
      have hineq : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      have hcalc : (1 : ℝ) ≤ (b : ℝ) / (a : ℝ) := by
        calc
          (1 : ℝ) = (a : ℝ)⁻¹ * (a : ℝ) := by field_simp [ha'.ne']
          _ ≤ (a : ℝ)⁻¹ * (b : ℝ) := mul_le_mul_of_nonneg_left hineq (by positivity)
          _ = (b : ℝ) / (a : ℝ) := by ring
      exact_mod_cast hcalc
    let Cbig : ℝ≥0 := Cu' * Csplit
    have hCbig1 : (1 : ℝ≥0) ≤ Cbig := by
      dsimp [Cbig]
      exact one_le_mul hCu'1 hCs1
    have hCsb : Csplit ≤ Cbig := by
      dsimp [Cbig]
      exact le_mul_of_one_le_left (by positivity) hCu'1
    have hM1 : (1 : ℝ≥0) ≤ Cbig * (b / a) := one_le_mul hCbig1 hba1
    have hCFsplit1 : 1 ≤ (Csplit : ENNReal) * CF := by
      have hCsplit_enn : 1 ≤ (Csplit : ENNReal) := by exact mod_cast hCs1
      calc
        (1 : ENNReal) ≤ (Csplit : ENNReal) := hCsplit_enn
        _ = (Csplit : ENNReal) * (1 : ENNReal) := by simp
        _ ≤ (Csplit : ENNReal) * CF := mul_le_mul_of_nonneg_left hCF1 (by positivity)
    have hCFsplit_top : (Csplit : ENNReal) * CF ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top hCFtop
    have hWnonc : Plank.IsThickeningNonconcentrated ts (fun x => (W x).toPrism3D) C_NC
        ((Cu' * Csplit) * (b / a)) :=
      isThickeningNonconcentrated_of_parentOverlapAtDilatedPlanks PS hoverP hpar_mem hocc hbodyW
        (fun j hj θ hθ1 hθab k hk => hloc j hj θ hθab hθ1 k hk)
    have h64out := (h64 ts hab hb1 W ha_pos hbcase hWball hWed hWfull
      (Cbig * (b / a)) hM1 hWnonc ((Csplit : ENNReal) * CF) hCFsplit1 hCFsplit_top hWfrost).2
    have hnts : ts.card ≠ 0 := Finset.card_ne_zero.mpr hts_ne
    have hthrBig : (Cbig : ENNReal) ^ ((1 : ℝ) + β / 2) ≤ (δ : ENNReal) ^ (-(ε / 4)) := by
      dsimp [Cbig]
      simpa using hcpthr (η := η₀) hη₀pos hη₀le δ Cu' hδ0 hδδ₀cp hδ1 hCu'δ
    exact localHighBranchBound hβpos hβle hε hδ0 ha_pos hab hδa hCs1 hCsb hCbig1 hCF1 hCFtop
      hnts h64out hsplitineq hthrBig (hthrfun2 δ hδ0 hδδ₀thr2)
  · -- Large-`b` branch: `Kakeya.coarseSlabFallback`, whose scale hypothesis `δ ≤ a` and overlap
    -- hypotheses `1 ≤ Cu`, `Cu ≤ δ ^ (-ηfall)` are supplied here; `δ ≤ a` comes from the same
    -- Proposition 5.1 adapter call the small-`b` branch makes.
    obtain ⟨Cunif, hCunif1, hCunifδ, ⟨𝒱⟩⟩ := huniform
    have hCunifδ' : Cunif ≤ δ ^ (-ηFine) := by
      have h_neg : -ηFine ≤ -(min (min (min ηFine η6) ηfall) (ε / 12)) := by
        linarith [hmin_le]
      calc
        Cunif ≤ δ ^ (-(min (min (min ηFine η6) ηfall) (ε / 12))) := hCunifδ
        _ ≤ δ ^ (-ηFine) := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 h_neg
    obtain ⟨ha_pos, hδa, -⟩ := hcfg q hδ0 T hball Cunif hCunif1 hCunifδ' 𝒱 hfull'
        ρ a b hab hb1 Cu PS hδρ hρ1 hbρ C₀ hC₀η' Fz CF hCF1 hCFtop hFrost
    have hco := hfall q hδ0 T hball huniformF hfullF ρ a b hab hb1 hδa Cu hCu1
        (hCuδ.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith [hmin_le_fall])))
        PS hδρ hρ1 C₀ hC₀ηF Fz CF hCF1 hCFtop hFrost (not_le.mp hbcase)
    exact absorbCoarseConstant hδ0 (by simpa using hcofun δ hδ0 hδδ₀co) hco

/-- **Absorbing a fixed constant into `δ ^ (-η)`, in `ℝ≥0`.**

For an absolute `C ≥ 1` and `η > 0` there is a threshold below which `C ≤ δ ^ (-η)`; take
`δ₀ = C ^ (-1/η)`.  This is the `ℝ≥0` companion of `Kakeya.rpowConstAbsorb` (which lives in
`ENNReal` and carries an extra power), and it is what lets the paper-facing wrapper feed the
*absolute* overlap constant of the constructed parent system into the internal theorem's
`Cu ≤ δ ^ (-η)` slot. -/
theorem exists_threshold_le_rpow_neg (C : ℝ≥0) (hC : 1 ≤ C) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ → C ≤ δ ^ (-η) := by
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hC
  have hη_ne : η ≠ 0 := by linarith
  set δ₀ : ℝ≥0 := C ^ (-1 / η) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by
    rw [hδ₀_def]
    exact NNReal.rpow_pos hC0
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro δ hδ hδle
  have hscalar : (-1 / η) * (-η) = (1 : ℝ) := by
    field_simp [hη_ne]
  have hδ₀_neg : δ₀ ^ (-η) = C := by
    rw [hδ₀_def]
    calc
      (C ^ (-1 / η)) ^ (-η) = C ^ ((-1 / η) * (-η)) := by rw [NNReal.rpow_mul]
      _ = C := by simp [hscalar]
  have hη_nonneg : 0 ≤ η := le_of_lt hη
  have h_pow_e : δ ^ η ≤ δ₀ ^ η := NNReal.rpow_le_rpow hδle hη_nonneg
  have hδrpow_pos : 0 < δ ^ η := NNReal.rpow_pos hδ
  have hδ₀rpow_pos : 0 < δ₀ ^ η := NNReal.rpow_pos hδ₀_pos
  have h_inv : (δ₀ ^ η)⁻¹ ≤ (δ ^ η)⁻¹ := (inv_le_inv₀ hδ₀rpow_pos hδrpow_pos).mpr h_pow_e
  calc
    C = δ₀ ^ (-η) := by rw [hδ₀_neg]
    _ = (δ₀ ^ η)⁻¹ := by rw [NNReal.rpow_neg]
    _ ≤ (δ ^ η)⁻¹ := h_inv
    _ = δ ^ (-η) := by rw [NNReal.rpow_neg]

/-- A single majorant for three fixed nonnegative losses. -/
def fixedLossMajorant (C₁ C₂ C₃ : ℝ≥0) : ℝ≥0 := max 1 (max C₁ (max C₂ C₃))

theorem one_le_fixedLossMajorant (C₁ C₂ C₃ : ℝ≥0) :
    1 ≤ fixedLossMajorant C₁ C₂ C₃ := le_max_left _ _

theorem le_fixedLossMajorant_left (C₁ C₂ C₃ : ℝ≥0) :
    C₁ ≤ fixedLossMajorant C₁ C₂ C₃ :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem le_fixedLossMajorant_middle (C₁ C₂ C₃ : ℝ≥0) :
    C₂ ≤ fixedLossMajorant C₁ C₂ C₃ :=
  le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

theorem le_fixedLossMajorant_right (C₁ C₂ C₃ : ℝ≥0) :
    C₃ ≤ fixedLossMajorant C₁ C₂ C₃ :=
  le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

/-- A loss below a common majorant inherits every weaker negative-power bound. -/
theorem fixedLoss_le_rpow_neg_of_majorant {C Cs δ : ℝ≥0} {gap target : ℝ}
    (hC : C ≤ Cs) (hCs : Cs ≤ δ ^ (-gap)) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hgap : gap ≤ target) : C ≤ δ ^ (-target) :=
  hC.trans <| hCs.trans <|
    NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)

/-- Absorb a fixed multiplicative loss across a positive real-power exponent gap. -/
theorem rpow_le_of_le_mul_of_loss_le {δ C F G : ℝ≥0} {small large : ℝ}
    (hδ0 : 0 < δ) (hC : C ≤ δ ^ (-(large - small)))
    (hF : δ ^ small ≤ F) (hFG : F ≤ C * G) : δ ^ large ≤ G := by
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hle : δ ^ small ≤ δ ^ (-(large - small)) * G :=
    hF.trans <| hFG.trans <| mul_le_mul_of_nonneg_right hC (by positivity)
  have hmul : δ ^ (large - small) * δ ^ small ≤
      δ ^ (large - small) * (δ ^ (-(large - small)) * G) := by
    gcongr
  calc
    δ ^ large = δ ^ (large - small) * δ ^ small := by
      rw [← NNReal.rpow_add hδne]
      congr 1
      ring
    _ ≤ δ ^ (large - small) * (δ ^ (-(large - small)) * G) := hmul
    _ = G := by
      rw [← mul_assoc, ← NNReal.rpow_add hδne]
      simp

/-- **GWZ Lemma 6.1 (Katz--Tao case) read at the master scale, as an interface.**

The repository's Lemma 6.1 (`Kakeya.KatzTaoEstimate.plankEstimate`,
`Kakeya.KatzTaoEstimate.plankEstimate_of_isKatzTao`) states the fullness hypothesis, the
Katz--Tao hypothesis and the sub-polynomial loss all at the *plank* scale `a`:
`a ^ η ≤ λ(𝒫, Y)`, `Δ_max(𝒫) ≤ a ^ (-η)` and `μ ≤ a ^ (-ε) · (a/b) ^ (γβ) · |s| ^ β`.

Section 6 cannot feed it the outer plank family produced by GWZ Proposition 5.1.  Proposition 5.1
item 2 gives only `λ(𝒲, Y_𝒲) ⪆ λ(𝒯, Y) ^ 2`, hence — with the master-scale fullness hypothesis
`λ(𝒯, Y) ≥ δ ^ η` of Proposition 6.6 — only `λ(𝒲, Y_𝒲) ⪆ δ ^ (2η)`.  Writing `a = δ ^ t` with
`t ∈ [0, 1]`, the plank-scale hypothesis `a ^ ηₒ ≤ λ(𝒲, Y_𝒲)` needs `t · ηₒ ≥ 2η`, which fails for
every fixed `η > 0` as soon as `a` stays above a fixed constant (`t → 0`); and `a` is only known to
satisfy `δ ≤ ρ ≤ a ≤ b ≤ b₀`.  So the plank-scale reading is *not* available to Proposition 6.6(B),
while the master-scale reading below is: `δ ^ (2η) ≥ δ ^ ηₒ` as soon as the fine exponent is chosen
with `2η ≤ ηₒ`, which is exactly what the Proposition 5.1 leaf is free to do.

This declaration is therefore the master-scale (`δ`-scale) reading of GWZ Lemma 6.1 in the
Katz--Tao case: fullness `δ ^ η ≤ λ`, density `Δ_max ≤ δ ^ (-η)`, slab non-concentration with
`δ ^ (-η)`, and the correspondingly weaker loss `δ ^ (-ε)` in place of `a ^ (-ε)` (weaker because
`δ ≤ a`).  It is GWZ's own reading — in the paper every `⪅` and every fullness exponent in
Section 6 is at the master scale `δ` — and it is *not* derivable from the plank-scale version in the
repository, whose hypotheses are strictly stronger.  It is passed as an explicit hypothesis, in the
style of `Kakeya.KatzTaoEstimate` and `Kakeya.FrostmanEstimate`, rather than silently assumed;
proving it (by rerunning the Lemma 6.1 argument with all losses measured at `δ`) is the one item of
migration debt this interface repair creates. -/
def PlankEstimateAtMasterScale (β : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0),
    ∀ {ι : Type*} (s : Finset ι) {δ a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
      (V : ι → ShadedPlank a b hab hb1),
      0 < δ → δ ≤ a → b ≤ b₀ →
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
      (s : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) →
      δ ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) →
      IsKatzTao s (fun i => (V i).toConvexSpaceBody) (δ ^ (-η)) →
      ∀ (γ : ℝ), 0 ≤ γ → γ ≤ 1 →
      (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
          ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
          ((Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card : ℝ≥0)
            ≤ δ ^ (-η) * φ ^ γ * (s.card : ℝ≥0)) →
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
          (δ : ENNReal) ^ (-ε) * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β)
            * (s.card : ENNReal) ^ β

/-- **GWZ Lemma 6.1 at the master scale, density form.**

`Kakeya.PlankEstimateAtMasterScale` is the master-scale reading of
`Kakeya.KatzTaoEstimate.plankEstimate_of_isKatzTao`: it *consumes* a Katz--Tao bound and its
conclusion carries no `Δ_max` factor.  The inner (`γ = 1`) application in Proposition 6.6(B) needs
the other shape — the master-scale reading of `Kakeya.KatzTaoEstimate.plankEstimate` itself, whose
conclusion retains the factor `Δ_max(𝒫) ^ (1 - β)`.  That factor is not decoration: it is what
carries the fine family's maximal density through the split into the final bound of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`, via the inner density transfer
`Δ_max(inner) ≤ Cinner · Δ_max(𝒯)` supplied by `Kakeya.factoringAndMultPropGlobal`.

Why the master scale is forced here.  After the interface repair, the inner family produced by
Proposition 5.1 carries its fullness and slab non-concentration data at `δ`, not at the inner plank
scale `a'`: Proposition 5.1 controls the *fine* family at the master scale, and the normalisation
that produces the inner planks cannot manufacture a bound at `a'` out of one at `δ`.  Since
`δ ≤ a' ≤ 1`, the `δ`-scale forms `δ ^ ηᵢ ≤ λ` and `count ≤ δ ^ (-ηᵢ) · φ ^ γ · |qj|` are strictly
weaker than the `a'`-scale forms the plank-scale Lemma 6.1 demands, so the plank-scale reading is
simply not applicable to the inner family.

Essential distinctness is retained as a hypothesis, exactly as in the plank-scale original: it is
what prevents a family from repeating one plank arbitrarily often, and no reading of Lemma 6.1 in
this repository dispenses with it.

Like `Kakeya.PlankEstimateAtMasterScale`, this is passed as an explicit hypothesis rather than
silently assumed; proving it (by rerunning the Lemma 6.1 argument with every loss measured at `δ`)
is migration debt, not a gap that is hidden anywhere. -/
def PlankEstimateAtMasterScaleWithDensity (β : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0),
    ∀ {ι : Type*} (s : Finset ι) {δ a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
      (V : ι → ShadedPlank a b hab hb1),
      0 < δ → δ ≤ a → b ≤ b₀ →
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
      (s : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) →
      δ ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) →
      ∀ (γ : ℝ), 0 ≤ γ → γ ≤ 1 →
      (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
          ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
          ((Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card : ℝ≥0)
            ≤ δ ^ (-η) * φ ^ γ * (s.card : ℝ≥0)) →
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
          (δ : ENNReal) ^ (-ε)
            * (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
            * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β

end Kakeya

end
