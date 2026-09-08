/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Kakeya.BallDense
public import Kakeya.DimensionThree.MainLemma1.TubeAxis

/-!
# Counting essentially distinct `δ`-tubes in the unit ball of `ℝ³`

This file contains the sharp count `Kakeya.ml1Boot.card_le` (blueprint `lem:ml1bootCardBound`):
a family of pairwise essentially distinct `δ`-tubes contained in `B₁ ⊆ ℝ³` has at most
`C δ ^ (-4)` members.  This is strictly sharper than the general packing bound
`Tube.card_le_of_EssDistinct`, which only gives `δ ^ (-2n) = δ ^ (-6)`.

The statement is elementary and dimension-three specific, but it is not tied to Main Lemma 1,
so it lives in its own module rather than inside
`Kakeya.DimensionThree.MainLemma1.Setup`, which merely re-exports it.

## Structure of the proof

All the geometry is in `Kakeya.DimensionThree.MainLemma1.TubeAxis`, which parametrises a tube
by its axis parameter `(ω(T), p(T)) ∈ WithLp 2 (E × E)` and supplies

* `Kakeya.ml1Boot.card_axisCell_le`: at most `8 n + 1 = 25` pairwise essentially distinct tubes
  share one `c_* δ / 6`-cell of the axis parameter space;
* `Kakeya.ml1Boot.volume_cthickening_axisParamSet_le`: the `r`-thickening of the axis parameter
  set has volume `O(r ^ 2)`, the two saved powers coming from its codimension two.

What is left here is the assembly: a maximal `ρ`-separated subset of the axis parameters, with
`ρ = δ / 72 = c_* δ / 6`, is counted by `Tube.card_le_of_separated_parameterSpace` against that
thickening volume, and each of its cells carries at most `25` tubes.  The remaining work is
arithmetic, isolated into the lemmas of the section *The numerical endgame* below.
-/

@[expose] public section

open MeasureTheory Metric

namespace Kakeya.ml1Boot

/-! ### The constant -/

/-- **The constant `C_{lem:ml1bootCardBound}`** of `Kakeya.ml1Boot.card_le` (blueprint
`def:ml1bootCardBoundConstant`): the absolute constant in the count of essentially distinct
`δ`-tubes in the unit ball of `ℝ³`.  It depends on nothing, the ambient dimension being
fixed to `3`.

The value is a deliberately generous explicit choice, in the style of `Tube.normalization.C`.
It must however exceed what the axis-parametrisation route actually produces, namely
`C(3) = 25 · C_cov(6)⁻¹ · axisThickening.C 3 · 72⁴ = 25 · 331776 · 72⁴ / π ≈ 7.1 · 10¹³`
(`Kakeya.ml1Boot.cardBound_numeral_le`, blueprint `lem:ml1bootCardBoundNumeral`).  The earlier
value `2 ^ 12` did not, and no proof could be closed with it; `2 ^ 60 ≈ 1.15 · 10¹⁸` leaves
four orders of magnitude of slack.
Only `Kakeya.ml1Boot.cardBound.one_le_C` and absoluteness are consumed downstream, so the
numeral itself is free. -/
abbrev cardBound.C : NNReal := 2 ^ 60

/-- The constant `Kakeya.ml1Boot.cardBound.C` is at least `1`, as every `⪆`-style constant of
this development is; the value being a power of two makes this a numerical triviality. -/
theorem cardBound.one_le_C : 1 ≤ cardBound.C := by norm_num

/-! ### The numerical endgame

The lemmas of this section carry out the arithmetic that turns the geometric input into
the stated bound.  They are separated out because they mix three different coercion regimes
(`NNReal`, `ℝ` and `ENNReal`) with the closed forms of several `Γ`-function constants, and are
best attacked one at a time. -/

/-- The dimension-six covering constant of
`Metric.coveringNumber_mul_pow_le_volume_cthickening` in closed form: since
`C_cov d = (1/2) ^ d · √π ^ d / Γ(d/2 + 1)` and `Γ(4) = 6`, the value at `d = 6` is `π³ / 384`.
This is the constant that the packing bound `Tube.card_le_of_separated_parameterSpace` divides
by, so its positivity and its size are both used in `Kakeya.ml1Boot.card_le`. -/
theorem coveringConst_six_eq :
    (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : ℝ) = Real.pi ^ 3 / 384 := by
  change (1 / 2 : ℝ) ^ 6 * (Real.sqrt Real.pi ^ 6 / Real.Gamma ((6 : ℕ) / 2 + 1))
    = Real.pi ^ 3 / 384
  norm_num
  have hsqrt : Real.sqrt Real.pi ^ 6 = Real.pi ^ 3 := by
    calc
      Real.sqrt Real.pi ^ 6 = (Real.sqrt Real.pi ^ 2) ^ 3 := by ring
      _ = Real.pi ^ 3 := by rw [Real.sq_sqrt Real.pi_pos.le]
  rw [hsqrt]
  ring

/-- The covering constant in dimension two: `C_cov 2 = π / 4`, equivalently `ω₂ = π`
through the bridge `ω_d = 2 ^ d · C_cov d` of
`Metric.volume_closedBall_eq_ccov_mul_pow`. -/
theorem coveringConst_two_eq :
    (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 2 : ℝ) = Real.pi / 4 := by
  change (1 / 2) ^ 2 * (Real.sqrt Real.pi ^ 2 / Real.Gamma (2 / 2 + 1)) = Real.pi / 4
  have hgam : Real.Gamma (2 : ℝ) = 1 := by
    rw [show (2 : ℝ) = ((1 : ℕ) + 1) by norm_num]
    rw [Real.Gamma_nat_eq_factorial]
    norm_num
  rw [show (2 / 2 + 1 : ℝ) = (2 : ℝ) by norm_num]
  rw [hgam]
  rw [Real.sq_sqrt Real.pi_pos.le]
  ring

/-- The covering constant in dimension three: `C_cov 3 = π / 6`, equivalently `ω₃ = 4π/3`.
The `Γ`-argument is the half-integer `5/2`, so this one goes through
`Real.Gamma_nat_add_half` rather than `Real.Gamma_nat_eq_factorial`. -/
theorem coveringConst_three_eq :
    (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : ℝ) = Real.pi / 6 := by
  have hGamma52 : Real.Gamma (5 / 2 : ℝ) = (3 / 4 : ℝ) * Real.sqrt Real.pi := by
    rw [show (5 / 2 : ℝ) = ((2 : ℕ) : ℝ) + 1 / 2 by norm_num]
    rw [Real.Gamma_nat_add_half (k := 2)]
    norm_num
    ring
  change (1 / 2 : ℝ) ^ 3 * (Real.sqrt Real.pi ^ 3 / Real.Gamma (3 / 2 + 1)) = Real.pi / 6
  rw [show (3 / 2 + 1 : ℝ) = (5 / 2 : ℝ) by norm_num]
  rw [hGamma52]
  have hsqrt : Real.sqrt Real.pi ^ 3 = Real.pi * Real.sqrt Real.pi := by
    rw [pow_succ, Real.sq_sqrt Real.pi_nonneg]
  rw [hsqrt]
  field_simp [ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)]
  ring

/-- The axis-thickening constant in dimension three in closed form:
`axisThickening.C 3 = 24 · 3 · 3² · ω₃ · ω₂ = 648 · (4π/3) · π = 864 π²`. -/
theorem axisThickening_C_three_eq :
    (axisThickening.C 3 : ℝ) = 864 * Real.pi ^ 2 := by
  have hGamma52 : Real.Gamma (5 / 2 : ℝ) = (3 / 4 : ℝ) * Real.sqrt Real.pi := by
    rw [show (5 / 2 : ℝ) = ((2 : ℕ) + 1 / 2) by norm_num]
    rw [Real.Gamma_nat_add_half 2]
    norm_num
    ring
  have hco : ∀ d : ℕ, (unitBallVolume d : ℝ)
      = (2 ^ d : ℝ) * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C d : ℝ) := by
    intro d
    simp [unitBallVolume, NNReal.coe_mul, NNReal.coe_pow]
  have hC3 : (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : ℝ)
      = (1 / 2 : ℝ) ^ 3 * (Real.sqrt Real.pi ^ 3 / Real.Gamma (3 / 2 + 1)) := by
    change (1 / 2 : ℝ) ^ 3 * (Real.sqrt Real.pi ^ 3 / Real.Gamma (3 / 2 + 1))
        = (1 / 2 : ℝ) ^ 3 * (Real.sqrt Real.pi ^ 3 / Real.Gamma (3 / 2 + 1))
    rfl
  have hu2 : (unitBallVolume 2 : ℝ) = Real.pi := by
    rw [hco 2, coveringConst_two_eq]
    norm_num
    ring
  have hu3 : (unitBallVolume 3 : ℝ) = (4 / 3 : ℝ) * Real.pi := by
    rw [hco 3, hC3]
    rw [show (3 / 2 + 1 : ℝ) = (5 / 2 : ℝ) by norm_num]
    rw [hGamma52]
    rw [show Real.sqrt Real.pi ^ 3 = (Real.sqrt Real.pi ^ 2) * Real.sqrt Real.pi by ring]
    rw [Real.sq_sqrt Real.pi_pos.le]
    have hsq0 : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
    field_simp [ne_of_gt hsq0]
  rw [show (axisThickening.C 3 : ℝ) =
      (24 * 3 * 3 ^ (3 - 1) : ℝ) * (unitBallVolume 3 : ℝ) * (unitBallVolume (3 - 1) : ℝ) by
    simp [axisThickening.C, NNReal.coe_mul, NNReal.coe_pow]]
  norm_num
  rw [hu3, hu2]
  ring

/-- The power bookkeeping of the endgame: the packing bound contributes `ρ⁻¹ ^ 6` and the
thickening volume contributes `ρ ^ 2`, and the two combine into the single real power
`ρ ^ (-4)` in which the conclusion of `Kakeya.ml1Boot.card_le` is phrased. -/
theorem inv_pow_six_mul_ofReal_sq {ρ : NNReal} (hρ : 0 < ρ) {c : ℝ} (hc : 0 ≤ c) :
    (ρ : ENNReal)⁻¹ ^ 6 * ENNReal.ofReal (c * (ρ : ℝ) ^ 2)
      = ENNReal.ofReal c * (ρ : ENNReal) ^ (-4 : ℝ) := by
  have h0 : (ρ : ENNReal) ≠ 0 := by simpa using hρ.ne'
  have htop : (ρ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h6 : (ρ : ENNReal) ^ (6 : ℕ) = (ρ : ENNReal) ^ (6 : ℝ) :=
    (ENNReal.rpow_natCast ρ 6).symm
  have e1 : (ρ : ENNReal)⁻¹ ^ (6 : ℕ) = (ρ : ENNReal) ^ (-6 : ℝ) := by
    rw [← ENNReal.inv_pow, ENNReal.rpow_neg]
    rw [← h6]
  have e2 : (ρ : ENNReal) ^ (2 : ℕ) = (ρ : ENNReal) ^ (2 : ℝ) := by
    exact (ENNReal.rpow_natCast ρ 2).symm
  have hmain : (ρ : ENNReal) ^ (-6 : ℝ) * (ρ : ENNReal) ^ (2 : ℝ) =
      (ρ : ENNReal) ^ (-4 : ℝ) := by
    rw [← ENNReal.rpow_add (-6) 2 h0 htop]
    congr 1
    norm_num
  rw [ENNReal.ofReal_mul hc]
  rw [ENNReal.ofReal_pow ρ.coe_nonneg 2]
  rw [ENNReal.ofReal_coe_nnreal]
  calc
    (ρ : ENNReal)⁻¹ ^ 6 * (ENNReal.ofReal c * (ρ : ENNReal) ^ (2 : ℕ))
        = ENNReal.ofReal c * ((ρ : ENNReal)⁻¹ ^ 6 * (ρ : ENNReal) ^ (2 : ℕ)) := by
          ring
    _ = ENNReal.ofReal c * ((ρ : ENNReal) ^ (-6 : ℝ) * (ρ : ENNReal) ^ (2 : ℝ)) := by
          rw [e1, e2]
    _ = ENNReal.ofReal c * (ρ : ENNReal) ^ (-4 : ℝ) := by
          rw [hmain]

/-- The change of scale from the separation radius `ρ = δ / 72` back to `δ`.  The factor `72`
is `6 / c_*` with `c_* = 1 / (4 · 3)` the slide constant of
`Tube.not_essDistinct_of_axial_slide` in dimension three. -/
theorem coe_div_rpow_neg_four {δ : NNReal} (hδ : 0 < δ) :
    ((δ / 72 : NNReal) : ENNReal) ^ (-4 : ℝ) = 72 ^ 4 * (δ : ENNReal) ^ (-4 : ℝ) := by
  have hδ_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hcoe : ((δ / 72 : NNReal) : ENNReal) = (δ : ENNReal) * (72 : ENNReal)⁻¹ := by
    rw [ENNReal.coe_div (by norm_num)]
    simp [div_eq_mul_inv]
  rw [hcoe]
  rw [ENNReal.mul_rpow_of_ne_top hδ_top (by simp)]
  have h72 : ((72 : ENNReal)⁻¹) ^ (-4 : ℝ) = 72 ^ 4 := by
    rw [ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]
    norm_num
  rw [h72]
  rw [mul_comm]

/-- The numerical inequality that fixes the numeral in `Kakeya.ml1Boot.cardBound.C`, in `ℝ`:
the constant produced by the axis-parametrisation route is
`25 · (384/π³) · 864 π² · 72⁴ = 25 · 331776 · 72⁴ / π ≈ 7.1 · 10¹³`, comfortably below
`2 ^ 60 ≈ 1.15 · 10¹⁸`.  Only a crude lower bound on `π` is needed. -/
theorem cardBound_numeral_le_real :
    25 * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : ℝ)⁻¹
        * (axisThickening.C 3 : ℝ) * 72 ^ 4
      ≤ 2 ^ 60 := by
  rw [coveringConst_six_eq, axisThickening_C_three_eq]
  have key : 25 * (Real.pi ^ 3 / 384 : ℝ)⁻¹ * (864 * Real.pi ^ 2) * 72 ^ 4
      = 8916100448256 * 25 / Real.pi := by
    field_simp
    ring
  rw [key]
  have hle13 : 8916100448256 * (25 : ℝ) / Real.pi
      ≤ 8916100448256 * (25 : ℝ) / 3 := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 3)
      (le_of_lt Real.pi_gt_three)
  calc
    8916100448256 * (25 : ℝ) / Real.pi ≤ 8916100448256 * (25 : ℝ) / 3 := hle13
    _ ≤ 2 ^ 60 := by norm_num

/-- The numerical inequality of `Kakeya.ml1Boot.cardBound_numeral_le_real`, transported into
`[0, ∞]`: this is the shape in which the assembly of `Kakeya.ml1Boot.card_le` meets the
constant. -/
theorem cardBound_numeral_le :
    25 * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : ENNReal)⁻¹
        * ENNReal.ofReal (axisThickening.C 3 : ℝ) * 72 ^ 4
      ≤ (cardBound.C : ENNReal) := by
  have h6pos : 0 < Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 :=
    Metric.coveringNumber_mul_pow_le_volume_cthickening.C_pos 6
  have h6ne : (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : NNReal) ≠ 0 :=
    ne_of_gt h6pos
  have hreal :
      25 * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : ℝ)⁻¹
          * (axisThickening.C 3 : ℝ) * 72 ^ 4 ≤ 2 ^ 60 := cardBound_numeral_le_real
  have hnn : (25 : NNReal) * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : NNReal)⁻¹
        * (axisThickening.C 3 : NNReal) * (72 : NNReal) ^ 4 ≤ cardBound.C := by
    exact NNReal.coe_le_coe.mp (by simpa [cardBound.C] using hreal)
  calc
    25 * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : ENNReal)⁻¹
        * ENNReal.ofReal (axisThickening.C 3 : ℝ) * 72 ^ 4
        = (↑((25 : NNReal) * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : NNReal)⁻¹
            * (axisThickening.C 3 : NNReal) * (72 : NNReal) ^ 4) : ENNReal) := by
          rw [← ENNReal.coe_inv h6ne, ENNReal.ofReal_coe_nnreal]
          simp
    _ ≤ (cardBound.C : ENNReal) := by
          exact ENNReal.coe_le_coe.2 hnn

/-! ### The count -/

section CardBound

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- The geometric half of `Kakeya.ml1Boot.card_le` (steps (1)–(4) of the blueprint proof of
`lem:ml1bootCardBound`): a maximal `ρ`-separated set of axis parameters, `ρ = δ / 72`, covers
`s` by cells of at most `25` tubes each (`Kakeya.ml1Boot.card_axisCell_le`), and is itself
counted by `Tube.card_le_of_separated_parameterSpace` against the thickening volume of
`Kakeya.ml1Boot.axisParamSet` (`Kakeya.ml1Boot.volume_cthickening_axisParamSet_le`).

The bound is left in the raw shape those three inputs produce; turning it into the stated
`C δ ^ (-4)` is the arithmetic of the *numerical endgame* lemmas above, carried out in
`Kakeya.ml1Boot.card_le`. -/
theorem card_le_geometric (hdim : Module.finrank ℝ E = 3) {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (s : Finset ι) (T : ι → Tube δ E)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set ι).Pairwise fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) :
    (s.card : ENNReal)
      ≤ 25 * ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : ENNReal)⁻¹
          * ((δ / 72 : NNReal) : ENNReal)⁻¹ ^ 6
          * ENNReal.ofReal ((axisThickening.C 3 : ℝ) * ((δ / 72 : NNReal) : ℝ) ^ 2)) := by
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; norm_num)
  let F : Type _ := WithLp 2 (E × E)
  let ρ : NNReal := δ / 72
  let Φ : ι → F := fun i => axisParam (T i)
  let 𝒜 : Set F := axisParamSet E
  have hρ0 : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ0R : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hρle : ρ ≤ 1 / 2 := by
    dsimp [ρ]
    rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_div]
    calc
      (δ : ℝ) / 72 = (δ : ℝ) * (1 / 72 : ℝ) := by ring
      _ ≤ 1 * (1 / 72 : ℝ) := mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hδ1) (by norm_num)
      _ ≤ 1 * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left (by norm_num) (by norm_num)
      _ = (1 / 2 : ℝ) := by ring
  have hρleR : (ρ : ℝ) ≤ 1 / 2 := by exact_mod_cast hρle
  have hρ_coe : (ρ : ℝ) = cStar E * (δ : ℝ) / 6 := by
    dsimp [ρ, cStar]
    rw [hdim]
    ring
  have hΦA : ∀ i ∈ s, Φ i ∈ 𝒜 := by
    intro i hi
    exact axisParam_mem_axisParamSet (T i) (hball i hi)
  have h𝒜bdd : Bornology.IsBounded 𝒜 := by
    exact isCompact_axisParamSet.isBounded
  by_cases hs_empty : s = ∅
  · subst hs_empty
    simp
  · -- nonempty case
    classical
    let img : Set F := Φ '' (↑s : Set ι)
    have hsnon : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs_empty
    have hAne : img.Nonempty := by
      obtain ⟨i, hi⟩ := hsnon
      exact ⟨Φ i, ⟨i, hi, rfl⟩⟩
    have himgA : img ⊆ 𝒜 := by
      rintro x ⟨i, hi, rfl⟩
      exact hΦA i hi
    have hAbdd : Bornology.IsBounded img := Bornology.IsBounded.subset h𝒜bdd himgA
    obtain ⟨G, hGsub, hGne, hGsep, hGcover⟩ :=
      Metric.exists_finset_separated_cover (X := F) hAne hAbdd (r := (ρ : ℝ)) hρ0R
    let sg : F → Finset ι := fun g => s.filter (fun i => dist (Φ i) g ≤ (ρ : ℝ))
    have hcell_le : ∀ g ∈ G, (sg g).card ≤ 25 := by
      intro g hg
      have hc := card_axisCell_le (E := E) (δ := δ) hδ hδ1 (sg g) T
        (by
          intro i hi
          exact hball i (Finset.mem_filter.mp hi).1)
        (by
          intro i hi j hj hij
          exact hED (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
            (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1 hij)
        g
        (by
          intro i hi
          have hid : dist (Φ i) g ≤ (ρ : ℝ) := (Finset.mem_filter.mp hi).2
          rw [hρ_coe] at hid
          simpa [Φ] using hid)
      have hfin : 8 * Module.finrank ℝ E + 1 = 25 := by norm_num [hdim]
      simpa [hfin] using hc
    have hcover_s : ↑s ⊆ ↑(G.biUnion (fun g => sg g)) := by
      intro i hi
      have hΦi : Φ i ∈ ⋃ g ∈ G, Metric.closedBall g (ρ : ℝ) := hGcover ⟨i, hi, rfl⟩
      rw [Set.mem_iUnion₂] at hΦi
      rcases hΦi with ⟨g, hg, hball_g⟩
      exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_filter.mpr ⟨hi, mem_closedBall.mp hball_g⟩⟩
    have hsGnat : s.card ≤ 25 * G.card := by
      calc
        s.card ≤ (G.biUnion (fun g => sg g)).card := Finset.card_le_card hcover_s
        _ ≤ ∑ g ∈ G, (sg g).card := Finset.card_biUnion_le
        _ ≤ ∑ g ∈ G, 25 := Finset.sum_le_sum (fun g hg => hcell_le g hg)
        _ = 25 * G.card := by simp [mul_comm]
    have hsG : (s.card : ENNReal) ≤ (25 : ENNReal) * (G.card : ENNReal) := by
      exact_mod_cast hsGnat
    have hfinF : Module.finrank ℝ F = 6 := by
      dsimp [F]
      rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (E × E))]
      rw [Module.finrank_prod]
      norm_num [hdim]
    let Cc : ENNReal := (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : ENNReal)
    have hGcard : (G.card : ENNReal) ≤
        Cc⁻¹ * (ρ : ENNReal)⁻¹ ^ 6 * volume (Metric.cthickening (ρ : ℝ) 𝒜) := by
      have hGA : ∀ g ∈ G, g ∈ 𝒜 := by
        intro g hg
        exact himgA (hGsub hg)
      have hsepG : (G : Set F).Pairwise fun i j => (ρ : ℝ) < dist i j := by
        intro i hi j hj hij
        exact hGsep i hi j hj hij
      have hb := Tube.card_le_of_separated_parameterSpace (F := F) (G := G)
        (Ψ := fun x : F => x) (A := 𝒜) (r := ρ) hρ0 hGA hsepG
      simpa [Cc, hfinF] using hb
    let cax : ℝ := (axisThickening.C 3 : ℝ)
    have hvol : volume (Metric.cthickening (ρ : ℝ) 𝒜) ≤ ENNReal.ofReal (cax * (ρ : ℝ) ^ 2) := by
      have hv := volume_cthickening_axisParamSet_le (E := E) (r := (ρ : ℝ)) hρ0R hρleR
      have hfin : Module.finrank ℝ E = 3 := hdim
      simpa [cax, hfin, 𝒜] using hv
    calc
      (s.card : ENNReal) ≤ (25 : ENNReal) * (G.card : ENNReal) := hsG
      _ ≤ (25 : ENNReal) *
            (Cc⁻¹ * (ρ : ENNReal)⁻¹ ^ 6 * volume (Metric.cthickening (ρ : ℝ) 𝒜)) := by
        exact mul_le_mul_left' hGcard 25
      _ = (25 : ENNReal) * Cc⁻¹ * (ρ : ENNReal)⁻¹ ^ 6 * volume (Metric.cthickening (ρ : ℝ) 𝒜) := by
        ac_rfl
      _ ≤ (25 : ENNReal) * Cc⁻¹ * (ρ : ENNReal)⁻¹ ^ 6 * ENNReal.ofReal (cax * (ρ : ℝ) ^ 2) := by
        exact mul_le_mul_left' hvol ((25 : ENNReal) * Cc⁻¹ * (ρ : ENNReal)⁻¹ ^ 6)
      _ = (25 : ENNReal) * Cc⁻¹ * ((ρ : ENNReal)⁻¹ ^ 6 * ENNReal.ofReal (cax * (ρ : ℝ) ^ 2)) := by
        ac_rfl
      _ = (25 : ENNReal) * ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : ENNReal)⁻¹
            * ((δ / 72 : NNReal) : ENNReal)⁻¹ ^ 6
            * ENNReal.ofReal ((axisThickening.C 3 : ℝ) * ((δ / 72 : NNReal) : ℝ) ^ 2)) := by
        dsimp [ρ, Cc, cax]
        ac_rfl

/-- **Counting essentially distinct `δ`-tubes in `ℝ³`** (blueprint `lem:ml1bootCardBound`):
a family of pairwise essentially distinct `δ`-tubes contained in `B₁ ⊆ ℝ³` has at most
`C δ ^ (-4)` members.  This is sharper than the general bound
`Kakeya.card_familyIn_le` and is what Case (i) needs.

The count is stated in `ENNReal` rather than in `ℝ`, because every consumer —
`Kakeya.ml1Boot.maxDensity_coarse_le`,
`Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale` and
`Kakeya.ml1Boot.bracket_mem_Icc` — multiplies it with densities and multiplicities, which
live in `ENNReal`. -/
theorem card_le (hdim : Module.finrank ℝ E = 3) {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (s : Finset ι) (T : ι → Tube δ E)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set ι).Pairwise fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) :
    (s.card : ENNReal) ≤ (cardBound.C : ENNReal) * (δ : ENNReal) ^ (-4 : ℝ) := by
  have hδpos72 : 0 < (δ / 72 : NNReal) := by positivity
  have hcollapse :
      (((δ / 72 : NNReal) : ENNReal)⁻¹ ^ 6)
        * ENNReal.ofReal ((axisThickening.C 3 : ℝ) * ((δ / 72 : NNReal) : ℝ) ^ 2)
        = ENNReal.ofReal (axisThickening.C 3 : ℝ) * ((δ / 72 : NNReal) : ENNReal) ^ (-4 : ℝ) :=
    inv_pow_six_mul_ofReal_sq (ρ := δ / 72) hδpos72 (NNReal.coe_nonneg (axisThickening.C 3))
  have hscale : ((δ / 72 : NNReal) : ENNReal) ^ (-4 : ℝ) = 72 ^ 4 * (δ : ENNReal) ^ (-4 : ℝ) :=
    coe_div_rpow_neg_four hδ
  calc
    (s.card : ENNReal)
        ≤ 25 * ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : ENNReal)⁻¹
            * ((δ / 72 : NNReal) : ENNReal)⁻¹ ^ 6
            * ENNReal.ofReal ((axisThickening.C 3 : ℝ) * ((δ / 72 : NNReal) : ℝ) ^ 2)) :=
      card_le_geometric hdim hδ hδ1 s T hball hED
    _ = 25 * ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : ENNReal)⁻¹
            * (((δ / 72 : NNReal) : ENNReal)⁻¹ ^ 6
            * ENNReal.ofReal ((axisThickening.C 3 : ℝ) * ((δ / 72 : NNReal) : ℝ) ^ 2))) := by
          ac_rfl
    _ = 25 * ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : ENNReal)⁻¹
            * (ENNReal.ofReal (axisThickening.C 3 : ℝ)
                * ((δ / 72 : NNReal) : ENNReal) ^ (-4 : ℝ))) := by
          rw [hcollapse]
    _ = 25 * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : ENNReal)⁻¹
            * ENNReal.ofReal (axisThickening.C 3 : ℝ)
            * ((δ / 72 : NNReal) : ENNReal) ^ (-4 : ℝ) := by
          ac_rfl
    _ = 25 * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : ENNReal)⁻¹
            * ENNReal.ofReal (axisThickening.C 3 : ℝ) * (72 ^ 4 * (δ : ENNReal) ^ (-4 : ℝ)) := by
          rw [hscale]
    _ = 25 * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C 6 : ENNReal)⁻¹
            * ENNReal.ofReal (axisThickening.C 3 : ℝ) * 72 ^ 4 * (δ : ENNReal) ^ (-4 : ℝ) := by
          ac_rfl
    _ ≤ (cardBound.C : ENNReal) * (δ : ENNReal) ^ (-4 : ℝ) := by
          exact mul_le_mul_left cardBound_numeral_le ((δ : ENNReal) ^ (-4 : ℝ))

end CardBound

end Kakeya.ml1Boot
