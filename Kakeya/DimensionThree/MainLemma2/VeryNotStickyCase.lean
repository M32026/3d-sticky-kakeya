/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThickCase
public import Kakeya.DimensionThree.MainLemma2.DenseInBodyConstants
public import Kakeya.DimensionThree.MainLemma2.ThinCase
public import Kakeya.DimensionThree.MainLemma2.SlabCase
public import Kakeya.DimensionThree.MainLemma2.TransverseCase
public import Kakeya.DimensionThree.MainLemma2.NonSlabCase
public import Kakeya.PartialEstimates
public import Kakeya.ShadedUniform

/-!
# Very not sticky case of Main Lemma 2

In this file we prove [GWZ, Lemma 9.1] (Very not sticky case of Main Lemma 2), together with
the top-level dichotomy that feeds it: the thick/thin case split
`Kakeya.VeryNotSticky.exists_goalMult` (blueprint `lem:ml2casesplit`) and the exponent
`Kakeya.VeryNotSticky.casesplitExponent` it carries (blueprint `def:ml2casesplitExponent`).
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

universe u

/-! ### Assembling the thick and thin cases -/

/-- **Exponent in Lemma `lem:ml2casesplit`** (blueprint `def:ml2casesplitExponent`).

The blueprint value is
`ν_casesplit(β, ζ) = min(⅛ ϱ β τ, ν_thin(β, ζ))`,
where `⅛ ϱ β τ` is the gain supplied by the thick case (blueprint `lem:ml2thick`, Lean
`Kakeya.VeryNotSticky.goalMult_of_a_ge`) and `ν_thin` is the exponent of the thin case
(blueprint `def:ml2thinExponent`, Lean `Kakeya.VeryNotSticky.thinExponent`).

As for `thinExponent` and `nonslabExponent`, the blueprint writes the exponent as a function
of `β` and `ζ` alone, because the parameters `exscal`, `ϱ` (the blueprint's `\exfact`), `τ`,
`τ'`, `η` of Definition `hyp:ml2params` are fixed functions of `β` and `ζ`, chosen before `δ`
and `𝕋`. In Lean they are separate reals, so they appear as explicit arguments. -/
noncomputable def casesplitExponent (β ζ exscal τ τ' ϱ : ℝ) : ℝ :=
  min (ϱ * β * τ / 8) (thinExponent β ζ exscal τ')

lemma casesplitExponent_pos {β ζ exscal τ τ' ϱ : ℝ} (hβ : 0 < β) (hζ : 0 < ζ)
    (hexscal : 0 < exscal) (hτ : 0 < τ) (hτ' : 0 < τ') (hϱ : 0 < ϱ) :
    0 < casesplitExponent β ζ exscal τ τ' ϱ :=
  lt_min (by positivity) (thinExponent_pos hβ hζ hexscal hτ')

/-- The `slab` budget of `CaseParams`: `12η + 12exscal + 3τ` is bounded by `β/2`, from the `η`-upper-bound
`η ≤ (β/2 - 12exscal - 3τ)/24` and the elementary parameter bounds `exscal ≤ β/100`,
`τ ≤ exscal/2` (so `12 exscal + 3τ ≤ 13.5 exscal ≤ 0.135 β < β/2`). -/
private lemma slabBudget {β exscal τ η : ℝ} (hβ : 0 < β)
    (hη : η ≤ (β / 2 - 12 * exscal - 3 * τ) / 24)
    (hexscal : exscal ≤ β / 100) (hτ : τ ≤ exscal / 2) :
    12 * η + 12 * exscal + 3 * τ < β / 2 := by
  have h12η : 12 * η ≤ (β / 2 - 12 * exscal - 3 * τ) / 2 := by
    calc
      12 * η ≤ 12 * ((β / 2 - 12 * exscal - 3 * τ) / 24) := by
        gcongr
      _ = (β / 2 - 12 * exscal - 3 * τ) / 2 := by ring
  linarith [h12η, hexscal, hτ, hβ]

/-- The `smallMultiplicity` budget of `CaseParams` (blueprint `lem:ml2paramsExist`):
`17η + ϱ < exscal(1+ζ)β`.

Named `smallMultiplicityFieldBudget`, and not `smallMultiplicityBudget`, to keep it apart from
the theorem `Kakeya.VeryNotSticky.smallMultiplicityBudget` of
`MainLemma2/VeryNotSticky.lean` (blueprint `lem:ml2smallmultBudget`), which is a different
statement: that one is the exponent budget the small-multiplicity *leaf* spends, whereas this
one discharges the `smallMultiplicity` *field* of `CaseParams` from the elementary parameter
bounds of `lem:ml2paramsExist`. -/
private lemma smallMultiplicityFieldBudget {β ζ exscal ϱ η : ℝ} (hβ : 0 < β) (hζ : 0 < ζ)
    (hexscal : 0 < exscal) (hη : η ≤ (exscal * β - ϱ) / 36) (hϱ : ϱ < exscal * β) :
    17 * η + ϱ < exscal * (1 + ζ) * β := by
  have h2η : 17 * η ≤ (exscal * β - ϱ) / 2 := by
    calc
      17 * η ≤ 17 * ((exscal * β - ϱ) / 36) := by gcongr
      _ ≤ (exscal * β - ϱ) / 2 := by linarith [hϱ]
  have h2ηϱ : 17 * η + ϱ < exscal * β := by
    calc
      17 * η + ϱ ≤ (exscal * β - ϱ) / 2 + ϱ := by gcongr
      _ = exscal * β / 2 + ϱ / 2 := by ring
      _ < exscal * β / 2 + exscal * β / 2 := by linarith [hϱ]
      _ = exscal * β := by ring
  have hgrow : exscal * β < exscal * (1 + ζ) * β := by
    have hpos : 0 < exscal * β := by positivity
    have h1lt : (1 : ℝ) < 1 + ζ := by linarith [hζ]
    calc
      exscal * β = exscal * β * 1 := by ring
      _ < exscal * β * (1 + ζ) := mul_lt_mul_of_pos_left h1lt hpos
      _ = exscal * (1 + ζ) * β := by ring
  exact lt_trans h2ηϱ hgrow

/-- The `transverse` budget of `CaseParams` (blueprint `lem:ml2paramsExist`):
`3τ + 87η < τ'β`, from the `η`-upper-bound `η ≤ (τ'β - 3τ)/174` and `3τ < τ'β`.
The coefficient is `87` and the denominator `174 = 2·87` for the transverse chain at exponent `16η`. -/
private lemma transverseBudget {β τ τ' η : ℝ} (hη : η ≤ (τ' * β - 3 * τ) / 174)
    (h3τ : 3 * τ < τ' * β) :
    3 * τ + 87 * η < τ' * β := by
  have h12η : 87 * η ≤ (τ' * β - 3 * τ) / 2 := by
    calc
      87 * η ≤ 87 * ((τ' * β - 3 * τ) / 174) := by gcongr
      _ = (τ' * β - 3 * τ) / 2 := by ring
  calc
    3 * τ + 87 * η ≤ 3 * τ + (τ' * β - 3 * τ) / 2 := by gcongr
    _ = (τ' * β + 3 * τ) / 2 := by ring
    _ < τ' * β := by linarith [h3τ]

/-- The `tangential` budget of `CaseParams` (blueprint `lem:ml2paramsExist`):
`2^20 (ϱ + τ') < exscal β ζ / 2`. -/
private lemma tangentialBudget {β ζ exscal ϱ τ' : ℝ} (hϱ : ϱ ≤ τ')
    (hτ' : τ' ≤ exscal * β * ζ / 2 ^ 23) (hexscalβζ : 0 < exscal * β * ζ) :
    (2 : ℝ) ^ 20 * (ϱ + τ') < exscal * β * ζ / 2 := by
  have hle1 : (2 : ℝ) ^ 20 * (ϱ + τ') ≤ (2 : ℝ) ^ 21 * τ' := by
    calc
      (2 : ℝ) ^ 20 * (ϱ + τ') ≤ (2 : ℝ) ^ 20 * (2 * τ') := by
        have hnn : 0 ≤ (2 : ℝ) ^ 20 := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith [hϱ]) hnn
      _ = (2 : ℝ) ^ 21 * τ' := by ring
  have hle2 : (2 : ℝ) ^ 21 * τ' ≤ (2 : ℝ) ^ 21 * (exscal * β * ζ / 2 ^ 23) := by
    have hnn : 0 ≤ (2 : ℝ) ^ 21 := by positivity
    exact mul_le_mul_of_nonneg_left hτ' hnn
  have hcomb : (2 : ℝ) ^ 20 * (ϱ + τ') ≤ exscal * β * ζ / 4 := by
    calc
      (2 : ℝ) ^ 20 * (ϱ + τ') ≤ (2 : ℝ) ^ 21 * τ' := hle1
      _ ≤ (2 : ℝ) ^ 21 * (exscal * β * ζ / 2 ^ 23) := hle2
      _ = exscal * β * ζ / 4 := by ring
  exact lt_of_le_of_lt hcomb (by linarith [hexscalβζ])

set_option maxHeartbeats 400000 in
-- `η` is now the minimum of eight quantities rather than seven, the eighth being the exponent
-- budget of blueprint `plankF`; each of the twelve `CaseParams` fields unfolds that minimum
-- once, and the proof no longer fits in the default budget.
/-- **The parameter hierarchy is satisfiable** (blueprint `lem:ml2paramsExist`).

For every `β > 0` there is a coarse-scale exponent `exscal > 0`, depending on `β` alone, such
that for every `ζ > 0` the remaining parameters `τ`, `τ'`, `ϱ` (the blueprint's `\exfact`) and
`η` of Definition `hyp:ml2params` can be chosen positive and satisfying every budget of that
definition, i.e. `Kakeya.VeryNotSticky.CaseParams`. The quantifier order is the one of
`hyp:ml2params`(P1): `exscal` is produced before `ζ` is introduced, which is what blueprint
Lemma `lemmain2vns` requires.

The last conjunct, `η ≤ ν_casesplit / 2`, is an extra clause beyond `CaseParams`: the proof of
blueprint `lemmain2vns` has to absorb a refinement loss `δ^{-η}` into the case-split gain
`Kakeya.VeryNotSticky.casesplitExponent`, which is possible exactly when `η` is at most a fixed
fraction of that gain. Carrying it costs nothing, because every field of `CaseParams` bounds `η`
from above only, so `η` may always be shrunk further.

The final conjunct, `2η < τ η_{plankF}`, is the exponent budget of blueprint `plankF` — at the
factor `2` of R16-A, which is what the
`⪆ δ^η ↦ δ^{2η}` rendering of GWZ l.2121-2122 in (C5) (F8) demands of it — and is
the second clause beyond `CaseParams`. It is what makes the field
`Kakeya.VeryNotSticky.ThickDensityThresholds.plankF` satisfiable, and hence
`Kakeya.VeryNotSticky.exists_setup_caseSideData` true rather than merely unproved; see that
statement's binder `hplankF`. It is arranged here, and not carried as a field of `CaseParams`,
only because `CaseParams` is declared upstream of the Section 6 plank interface and cannot
mention `Kakeya.VeryNotSticky.plankFrostmanExponent`; mathematically it belongs with the other
budgets of blueprint `hyp:ml2params`, and it is discharged in the same way, as one more upper
bound on the `η` this proof chooses last. Note that it costs nothing to the existing budgets
for the same reason they cost nothing to each other, and that
`Kakeya.VeryNotSticky.plankFrostmanExponent` is positive unconditionally, so this conjunct is
available without assuming `K_F(β)` — which matters, since the consumer
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge` fixes `η` before assuming it. -/
theorem exists_caseParams {β : ℝ} (hβ : 0 < β) :
    ∃ exscal > (0 : ℝ), ∀ ζ > (0 : ℝ), ∃ τ τ' ϱ η : ℝ,
      0 < τ ∧ 0 < τ' ∧ 0 < ϱ ∧ 0 < η ∧
      CaseParams β ζ exscal ϱ η τ τ' ∧
      η ≤ casesplitExponent β ζ exscal τ τ' ϱ / 2 ∧
      2 * η < τ * plankFrostmanExponent.{u} β (ϱ * β * τ / 8) := by
  let exscal : ℝ := min (β / 100) ((1 : ℝ) / 100)
  have hexscal_pos : 0 < exscal := by
    dsimp [exscal]
    exact lt_min (by positivity) (by positivity)
  have hexscal_le_β100 : exscal ≤ β / 100 := by
    dsimp [exscal]
    exact min_le_left _ _
  have hexscal_le_100 : exscal ≤ (1 : ℝ) / 100 := by
    dsimp [exscal]
    exact min_le_right _ _
  refine ⟨exscal, hexscal_pos, ?_⟩
  intro ζ hζ
  let τ' : ℝ := min (exscal * β * ζ / 2 ^ 23) (exscal / 2)
  let τ : ℝ := min (exscal / 2) (τ' * min β 1 / 2 ^ 10)
  let ϱ : ℝ := min (min τ' (exscal * min β 1 / 2 ^ 21)) τ
  let η0 : ℝ :=
    min (ϱ / 2 ^ 21)
      (min (exscal / 8)
        (min (ϱ * β * τ / 2 ^ 21)
          (min ((β / 2 - 12 * exscal - 3 * τ) / 24)
            (min ((exscal * β - ϱ) / 36)
              (min ((τ' * β - 3 * τ) / 174)
                (casesplitExponent β ζ exscal τ τ' ϱ / 2))))))
  let pf : ℝ := plankFrostmanExponent β (ϱ * β * τ / 8)
  let η : ℝ := min η0 (τ * pf / 4)
  have hexscal_lt_half : exscal < 1 / 2 := by
    nlinarith [hexscal_le_100]
  have hminβ1_le_β : min β 1 ≤ β := min_le_left _ _
  have hminβ1_le_1 : min β 1 ≤ 1 := min_le_right _ _
  have hτ'_pos : 0 < τ' := by
    dsimp [τ']
    exact lt_min (by positivity) (by positivity)
  have hτ'_le_gain : τ' ≤ exscal * β * ζ / 2 ^ 23 := by
    dsimp [τ']
    exact min_le_left _ _
  have hτ_pos : 0 < τ := by
    dsimp [τ]
    exact lt_min (by positivity) (by positivity)
  have hτ_le_exscal2 : τ ≤ exscal / 2 := by
    dsimp [τ]
    exact min_le_left _ _
  have hτ_le_fac : τ ≤ τ' * min β 1 / 2 ^ 10 := by
    dsimp [τ]
    exact min_le_right _ _
  have hmbin_lt : min β 1 / 2 ^ 10 < 1 := by
    calc
      min β 1 / 2 ^ 10 ≤ (1 : ℝ) / 2 ^ 10 :=
        div_le_div_of_nonneg_right hminβ1_le_1 (by norm_num : 0 ≤ (2 : ℝ) ^ 10)
      _ < 1 := by norm_num
  have hτ'fac_lt : τ' * min β 1 / 2 ^ 10 < τ' := by
    calc
      τ' * min β 1 / 2 ^ 10 = τ' * (min β 1 / 2 ^ 10) := by ring
      _ < τ' * 1 := mul_lt_mul_of_pos_left hmbin_lt hτ'_pos
      _ = τ' := by ring
  have hτ_lt_τ' : τ < τ' := lt_of_le_of_lt hτ_le_fac hτ'fac_lt
  have h3min_lt_β : 3 * min β 1 / 2 ^ 10 < β := by
    calc
      3 * min β 1 / 2 ^ 10 ≤ 3 * β / 2 ^ 10 := by
        gcongr
      _ < β := by nlinarith [hβ]
  have h3τ_le : 3 * τ ≤ 3 * τ' * min β 1 / 2 ^ 10 := by
    nlinarith [hτ_le_fac]
  have h3τ_lt_τ'β : 3 * τ < τ' * β := by
    calc
      3 * τ ≤ 3 * τ' * min β 1 / 2 ^ 10 := h3τ_le
      _ < τ' * β := by
        have hprod : 3 * τ' * min β 1 / 2 ^ 10 = τ' * (3 * min β 1 / 2 ^ 10) := by
          ring
        rw [hprod]
        exact mul_lt_mul_of_pos_left h3min_lt_β hτ'_pos
  have hϱ_pos : 0 < ϱ := by
    dsimp [ϱ]
    exact lt_min (lt_min (by positivity) (by positivity)) hτ_pos
  have hϱ_le_τ' : ϱ ≤ τ' := by
    dsimp [ϱ]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hϱ_le_fac : ϱ ≤ exscal * min β 1 / 2 ^ 21 := by
    dsimp [ϱ]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hϱ_le_τ : ϱ ≤ τ := by
    dsimp [ϱ]
    exact min_le_right _ _
  have h2p20ϱ_lt_exscal : (2 : ℝ) ^ 20 * ϱ < exscal := by
    have hle : (2 : ℝ) ^ 20 * ϱ ≤ (2 : ℝ) ^ 20 * (exscal * min β 1 / 2 ^ 21) :=
      mul_le_mul_of_nonneg_left hϱ_le_fac (by positivity)
    have hkey : (2 : ℝ) ^ 20 * (exscal * min β 1 / 2 ^ 21) ≤ exscal / 2 := by
      have hk : (2 : ℝ) ^ 20 * (exscal * min β 1 / 2 ^ 21) = exscal * min β 1 / 2 := by
        ring
      rw [hk]
      have hle : exscal * min β 1 ≤ exscal := by
        calc
          exscal * min β 1 ≤ exscal * 1 :=
            mul_le_mul_of_nonneg_left hminβ1_le_1 (le_of_lt hexscal_pos)
          _ = exscal := by ring
      exact div_le_div_of_nonneg_right hle (by norm_num : 0 ≤ (2 : ℝ))
    have hexscal2_lt : exscal / 2 < exscal := by
      nlinarith [hexscal_pos]
    exact lt_of_le_of_lt (le_trans hle hkey) hexscal2_lt
  have hϱ_lt_exscalβ : ϱ < exscal * β := by
    calc
      ϱ ≤ exscal * min β 1 / 2 ^ 21 := hϱ_le_fac
      _ = exscal * (min β 1 / 2 ^ 21) := by ring
      _ < exscal * β := by
        have hmb : min β 1 / 2 ^ 21 < β := by
          calc
            min β 1 / 2 ^ 21 ≤ β / 2 ^ 21 := by
              gcongr
            _ < β := by nlinarith [hβ]
        exact mul_lt_mul_of_pos_left hmb hexscal_pos
  have h1_pos : 0 < ϱ / 2 ^ 21 := by positivity
  have h2_pos : 0 < exscal / 8 := by positivity
  have h3_pos : 0 < ϱ * β * τ / 2 ^ 21 := by positivity
  have h4_pos : 0 < (β / 2 - 12 * exscal - 3 * τ) / 24 := by
    nlinarith [hβ, hexscal_le_β100, hτ_le_exscal2]
  have h5_pos : 0 < (exscal * β - ϱ) / 36 := by
    nlinarith [hϱ_lt_exscalβ]
  have h6_pos : 0 < (τ' * β - 3 * τ) / 174 := by
    nlinarith [h3τ_lt_τ'β]
  have hcs_pos : 0 < casesplitExponent β ζ exscal τ τ' ϱ :=
    casesplitExponent_pos hβ hζ hexscal_pos hτ_pos hτ'_pos hϱ_pos
  have h7_pos : 0 < casesplitExponent β ζ exscal τ τ' ϱ / 2 := by positivity
  have hplankF_pos : 0 < pf :=
    plankFrostmanExponent_pos β (ϱ * β * τ / 8)
  have h8_pos : 0 < τ * pf / 4 := by
    positivity
  have hη0_pos : 0 < η0 := by
    dsimp [η0]
    apply lt_min
    · exact h1_pos
    · apply lt_min
      · exact h2_pos
      · apply lt_min
        · exact h3_pos
        · apply lt_min
          · exact h4_pos
          · apply lt_min
            · exact h5_pos
            · apply lt_min
              · exact h6_pos
              · exact h7_pos
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min hη0_pos h8_pos
  have hη_le_1 : η ≤ ϱ / 2 ^ 21 := by
    dsimp [η]
    exact le_trans (min_le_left _ _) (by
      dsimp [η0]
      exact min_le_left _ _)
  have hη_le_2 : η ≤ exscal / 8 := by
    dsimp [η]
    exact le_trans (min_le_left _ _) (by
      dsimp [η0]
      exact le_trans (min_le_right _ _) (min_le_left _ _))
  have hη_le_3 : η ≤ ϱ * β * τ / 2 ^ 21 := by
    dsimp [η]
    exact le_trans (min_le_left _ _) (by
      dsimp [η0]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hη_le_4 : η ≤ (β / 2 - 12 * exscal - 3 * τ) / 24 := by
    dsimp [η]
    exact le_trans (min_le_left _ _) (by
      dsimp [η0]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hη_le_5 : η ≤ (exscal * β - ϱ) / 36 := by
    dsimp [η]
    exact le_trans (min_le_left _ _) (by
      dsimp [η0]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hη_le_6 : η ≤ (τ' * β - 3 * τ) / 174 := by
    dsimp [η]
    exact le_trans (min_le_left _ _) (by
      dsimp [η0]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))))
  have hη_le_7 : η ≤ casesplitExponent β ζ exscal τ τ' ϱ / 2 := by
    dsimp [η]
    exact le_trans (min_le_left _ _) (by
      dsimp [η0]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _)
              (le_trans (min_le_right _ _) (min_le_right _ _))))))
  have hη_le_8 : η ≤ τ * pf / 4 := by
    dsimp [η]
    exact min_le_right _ _
  have hη_lt_plankF : 2 * η < τ * pf := by
    linarith [hη_le_8, h8_pos]
  have hparams : CaseParams β ζ exscal ϱ η τ τ' := by
    constructor
    · exact hτ_pos
    · exact hτ_lt_τ'
    · exact hexscal_lt_half
    · -- thinScale  (τ + exscal < 1)
      nlinarith [hτ_le_exscal2, hexscal_le_100]
    · -- thinHalf  (τ + exscal ≤ 1/2): free at these choices, since `τ ≤ exscal/2` and
      -- `exscal ≤ 1/100` give `τ + exscal ≤ (3/2)·exscal ≤ 3/200 < 1/2`
      linarith [hτ_le_exscal2, hexscal_le_100]
    · -- densityBias  (2^20 * η < ϱ)
      change (2 : ℝ) ^ 20 * η < ϱ
      have h : (2 : ℝ) ^ 20 * η ≤ ϱ / 2 := by
        calc
          (2 : ℝ) ^ 20 * η ≤ (2 : ℝ) ^ 20 * (ϱ / 2 ^ 21) :=
            mul_le_mul_of_nonneg_left hη_le_1 (by positivity)
          _ = ϱ / 2 := by ring
      exact lt_of_le_of_lt h (by nlinarith [hϱ_pos])
    · -- slabDensity  (6 * η < exscal): the (C5) exponent `2η` in the density clause
      -- (F8) doubled the coefficient `3` that `Kakeya.ThinCase.ThinBall.fullness_bodies` had
      -- brought, so the second `min` term of `η0` is `exscal / 8` (it was `exscal / 4`) and
      -- `hη_le_2 : η ≤ exscal / 8` gives `6η ≤ 6exscal/8 < exscal`
      exact show 6 * η < exscal by
        have hle : 6 * η ≤ 6 * exscal / 8 := by
          calc
            6 * η ≤ 6 * (exscal / 8) :=
              mul_le_mul_of_nonneg_left hη_le_2 (by norm_num : 0 ≤ (6 : ℝ))
            _ = 6 * exscal / 8 := by ring
        exact lt_of_le_of_lt hle (by nlinarith [hexscal_pos])
    · -- slabBias  (2^20 * ϱ < exscal)
      change (2 : ℝ) ^ 20 * ϱ < exscal
      exact h2p20ϱ_lt_exscal
    · -- thick  (2^20 * η < ϱ * β * τ)
      change (2 : ℝ) ^ 20 * η < ϱ * β * τ
      have hϱβτ_pos : 0 < ϱ * β * τ := by positivity
      have h : (2 : ℝ) ^ 20 * η ≤ ϱ * β * τ / 2 := by
        calc
          (2 : ℝ) ^ 20 * η ≤ (2 : ℝ) ^ 20 * (ϱ * β * τ / 2 ^ 21) :=
            mul_le_mul_of_nonneg_left hη_le_3 (by positivity)
          _ = ϱ * β * τ / 2 := by ring
      exact lt_of_le_of_lt h (half_lt_self hϱβτ_pos)
    · -- slab  (12 * η + 12 * exscal + 3 * τ < β / 2)
      exact slabBudget hβ hη_le_4 hexscal_le_β100 hτ_le_exscal2
    · -- smallMultiplicity  (17 * η + ϱ < exscal * (1 + ζ) * β)
      exact smallMultiplicityFieldBudget hβ hζ hexscal_pos hη_le_5 hϱ_lt_exscalβ
    · -- transverse  (3 * τ + 87 * η < τ' * β)
      exact transverseBudget hη_le_6 h3τ_lt_τ'β
    · -- tangential  (2^20 * (ϱ + τ') < exscal * β * ζ / 2)
      exact tangentialBudget hϱ_le_τ' hτ'_le_gain (by positivity)
    · -- rhoLeTau  (ϱ ≤ τ)
      exact hϱ_le_τ
  exact ⟨τ, τ', ϱ, η, hτ_pos, hτ'_pos, hϱ_pos, hη_pos, hparams, hη_le_7, hη_lt_plankF⟩

/-- **The side data of the case split** (blueprint `lem:ml2setupSideData`).

Everything `Kakeya.VeryNotSticky.exists_goalMult` consumes beyond `cfg`, `bd`, `params` and
`β ≤ 1`, collected into one bundle so that arranging it is a statement of its own rather than
four extra conjuncts of `Kakeya.VeryNotSticky.exists_setup`. In the blueprint these are
arranged not in `lem:ml2setupexists` but in the paragraph of the proof of `lemmain2vns` that
chooses `δ` small enough; they are named here because that paragraph is otherwise not
represented by a declaration of its own.

Besides the two constants `CP`, `Θ` and the plank-Frostman exponent `ηF`, which are data and
carry no content of their own, three of the seven remaining fields are assumptions the
blueprint makes rather than discharges:
`thick`, whose achievability is the `δ`-independence question recorded in the note at the end
of blueprint subsection `thickCaseSection`; `tangential`, items (a)–(c) of
`lem:ml2tangential`, which the blueprint likewise assumes and lets travel to its consumers;
and `thr` together with `thr_thick`, whose defining property blueprint
`def:ml2aScaleDataThreshold` does not fix.

The thin-case data `tc` is a field rather than a parameter because `caseScale` and
`tangential` both mention it — the seventh clause of Configuration `hyp:ml2scale` is stated
against the comparison constant `tc.C`, which exists only once the thin-case data does. That
is the same reason `Kakeya.VeryNotSticky.SlabScale` travels here rather than standing free. -/
structure CaseSideData (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (τ τ' : ℝ) where
  /-- The comparison constant `C_{lem:ml2thickPlank}(C₀)` of blueprint
  `def:ml2thickPlankConstant`, carried as data so that the plank presentation and the
  parameter budget of blueprint `plankF` can be asserted at one and the same value; see
  `Kakeya.VeryNotSticky.ThickDensityThresholds`. -/
  CP : NNReal
  /-- The non-concentration constant `C_{lem:ml2thickMbound}(C₀)` of blueprint
  `def:ml2thickMboundConstant`, carried as data for the same reason as `CP`. -/
  Θ : NNReal
  /-- The plank-Frostman exponent `η_{plankF}` of blueprint `plankF`, carried as data so that
  the estimate and the exponent budget `2η < τ η_{plankF}` can be asserted at one and the same
  value; see `Kakeya.VeryNotSticky.ThickDensityThresholds`. It is produced at the canonical
  value `Kakeya.VeryNotSticky.plankFrostmanExponent cfg.β (ϱβτ/8)`. -/
  ηF : ℝ
  /-- The non-concentration dilation `C_NC` of blueprint `plankF` as Section 6 renders it
  (`Kakeya.FrostmanEstimate.plankEstimate`), carried as data for exactly the reason `CP` and
  `Θ` are: `Kakeya.VeryNotSticky.PlankFrostmanUsable` gets *weaker* as it grows, since
  `Plank.IsThickeningNonconcentrated` is a stronger hypothesis at a larger dilation, while
  `Kakeya.VeryNotSticky.ThickPlankPresentable` gets *stronger*, its `nonconcentration` field
  being asserted at that dilation. So the two fields `plankF` and `plankPres` of
  `Kakeya.VeryNotSticky.ThickDensityThresholds` must be asserted at one and the same value,
  and neither may quantify it inside the other. It is `δ`-free — Section 6 produces it ahead of
  `ε`, as `Plank.ThickenedRepr.fibreDilation cThk` — and it is realized from
  `Kakeya.VeryNotSticky.plankFrostmanVolumeAt_plankFrostmanExponent`. Unlike `ηF` it needs no
  canonical name, because no field compares it with another quantity. -/
  C_NC : NNReal
  /-- hypotheses (T3) and (T6) of blueprint `lem:ml2thick`, together with the Section 6 plank
  presentation, all at the triple `(CP, Θ, C_NC)` and the exponent `ηF` -/
  thick : ThickDensityThresholds cfg bd τ CP Θ C_NC ηF
  /-- the by-choice thresholds of Configuration `hyp:ml2scale` -/
  thr : ScaleThresholds
  /-- the eighth clause of `hyp:ml2scale`, at the thick gain `ν_{lem:ml2thick} = ϱβτ/8` -/
  thr_thick : cfg.δ ≤ thr.aScale (cfg.ϱ * cfg.β * τ / 8)
  /-- the thin-case data of Configuration `hyp:ml2thinsetup` -/
  tc : ThinConfig cfg bd
  /-- Configuration `hyp:ml2slabscale` -/
  slabScale : SlabScale cfg bd tc τ
  /-- Configuration `hyp:ml2scale`, read at the transverse gain `τ'β/2` -/
  caseScale : CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr
  /-- items (a)–(c) of blueprint `lem:ml2tangential` -/
  tangential : cfg.a ≤ cfg.δ ^ (1 - τ) → cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) → TangentialInputs cfg tc τ'

/-- **The thick case from `Kakeya.VeryNotSticky.CaseSideData`.**

The form in which the top-level assembly would use the thick branch:
`Kakeya.VeryNotSticky.goalMult_of_a_ge` reading its `hdens` off the side data of the case
split, which already contains the thick-case bundle as its field `thick`. So the thick branch
needs nothing beyond `params`, `bd` and that side data, and the ball data becomes implicit,
being determined by the side data. -/
theorem goalMult_of_a_ge_of_caseSideData (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    {bd : BallData cfg} (sd : CaseSideData cfg bd τ τ')
    (hthick : cfg.δ ^ (1 - τ) ≤ cfg.a) :
    ∃ ν > (0 : ℝ), cfg.goalMult ν :=
  goalMult_of_a_ge cfg params bd sd.thick hthick


/-! ### Realizing the side data: the pieces that are not assumptions

`Kakeya.VeryNotSticky.exists_setup_caseSideData` below has to produce every field of
`Kakeya.VeryNotSticky.CaseSideData`. Four of them are *not* content of the construction and
are discharged here, once and for all, so that the remaining obligation is exactly the part
the blueprint leaves open:

* `thr` and `thr_thick` — `Kakeya.VeryNotSticky.nonempty_caseSideData` below, from
  `Kakeya.VeryNotSticky.exists_scaleThresholds_of_le_one` and the field `cfg.hδ1`. The same
  lemma also shows that the `CaseScale` a producer has to supply may be read at *any*
  threshold bundle, the bundle carried by `CaseSideData` being replaceable;
* the fields `hηF` and `budget` of `Kakeya.VeryNotSticky.ThickDensityThresholds`, and the
  guarded field `plankF` — `Kakeya.VeryNotSticky.thickDensityThresholds_canonical` below, at
  the canonical exponent `Kakeya.VeryNotSticky.plankFrostmanExponent cfg.β (ϱβτ/8)`, from the
  binder `hplankF` of `exists_setup_caseSideData` together with
  `Kakeya.VeryNotSticky.plankFrostmanUsable_of_thick`.
-/

/-- **The two thresholds of blueprint `plankF` under the thick-case guard.**

Blueprint `plankF` is applicable at the scales of the configuration as soon as its parameters
`(ηF, b₀)` fit them: that is the predicate
`Kakeya.VeryNotSticky.PlankFrostmanUsable`, whose two thresholds read
`CP δ/a ≤ b₀` and `CP (CP δ/b)^{ηF} ≤ c₁ δ^{2η}`. Both mention the working scales `a`, `b` of the
factoring, which Configuration `hyp:ml2setup` constrains only by `δ ≤ a ≤ b ≤ r₁`, so neither
is a threshold on `δ` alone.

Under the thick-case guard `δ^{1-τ} ≤ a` they become ones, and this lemma is that reduction:
since `δ = δ^τ δ^{1-τ} ≤ δ^τ a` and, `a ≤ b` being the field
`Kakeya.VeryNotSticky.hdims`, also `δ ≤ δ^τ b`, the two ratios satisfy `δ/a ≤ δ^τ` and
`δ/b ≤ δ^τ`, and the thresholds follow from
`CP δ^τ ≤ b₀` and `CP^{1+ηF} δ^{τ ηF - 2η} ≤ c₁`.

This is the computation the docstrings of
`Kakeya.VeryNotSticky.PlankFrostmanUsable` and
`Kakeya.VeryNotSticky.ThickDensityThresholds.plankF` record as the reason the field is
satisfiable: the second hypothesis is met for `δ` small exactly when the exponent
`τ ηF - 2η` is positive, i.e. `2η < τ ηF` — which is the budget of
`Kakeya.VeryNotSticky.ThickDensityThresholds.budget` and of the target's binder
`Kakeya.VeryNotSticky.PlankFrostmanBudget` since R16-A, the factor `2` matching F8 , which reads
(C5) at `δ^{2η}`. With it `hc₁` is met for `δ` small by
`Kakeya.VeryNotSticky.eventually_plankFrostman_thresholds` read at `η := 2 cfg.η`; it stays a
binder here so that the lemma is stated at one fixed `δ`. -/
theorem plankFrostmanUsable_of_thick {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {τ : ℝ}
    {CP C_NC b₀ : NNReal} {ηF : ℝ} (hCP : 1 ≤ CP) (hηF : 0 < ηF)
    (hthick : cfg.δ ^ (1 - τ) ≤ cfg.a)
    (hvol : PlankFrostmanVolumeAt.{u} cfg.β (cfg.ϱ * cfg.β * τ / 8) ηF b₀ C_NC)
    (hb₀ : CP * cfg.δ ^ τ ≤ b₀)
    (hc₁ : CP ^ (1 + ηF) * cfg.δ ^ (τ * ηF - 2 * cfg.η) ≤ bd.c₁) :
    PlankFrostmanUsable bd τ CP C_NC ηF := by
  have hδ0 : cfg.δ ≠ 0 := ne_of_gt cfg.hδ
  have hCP0 : CP ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCP)
  have hδa : cfg.δ ≤ cfg.a := cfg.hdims.1
  have hab : cfg.a ≤ cfg.b := cfg.hdims.2.1
  have ha0 : 0 < cfg.a := lt_of_lt_of_le cfg.hδ hδa
  have hb0 : 0 < cfg.b := lt_of_lt_of_le ha0 hab
  -- `δ = δ^τ · δ^{1-τ}`, the splitting behind both ratio bounds.
  have hsplit : cfg.δ = cfg.δ ^ τ * cfg.δ ^ (1 - τ) := by
    have hτs : τ + (1 - τ) = (1 : ℝ) := by ring
    rw [← NNReal.rpow_add hδ0, hτs, NNReal.rpow_one]
  have hδb : cfg.δ ^ (1 - τ) ≤ cfg.b := le_trans hthick hab
  have hdiv_a : cfg.δ / cfg.a ≤ cfg.δ ^ τ := by
    rw [div_le_iff₀ ha0]
    calc cfg.δ = cfg.δ ^ τ * cfg.δ ^ (1 - τ) := hsplit
      _ ≤ cfg.δ ^ τ * cfg.a := by gcongr
  have hdiv_b : cfg.δ / cfg.b ≤ cfg.δ ^ τ := by
    rw [div_le_iff₀ hb0]
    calc cfg.δ = cfg.δ ^ τ * cfg.δ ^ (1 - τ) := hsplit
      _ ≤ cfg.δ ^ τ * cfg.b := by gcongr
  refine ⟨b₀, hvol, ?_, ?_⟩
  · calc CP * cfg.δ / cfg.a = CP * (cfg.δ / cfg.a) := by rw [mul_div_assoc]
      _ ≤ CP * cfg.δ ^ τ := by gcongr
      _ ≤ b₀ := hb₀
  · have h1 : CP * cfg.δ / cfg.b ≤ CP * cfg.δ ^ τ := by
      rw [mul_div_assoc]; gcongr
    have h2 : (CP * cfg.δ / cfg.b) ^ ηF ≤ CP ^ ηF * cfg.δ ^ (τ * ηF) := by
      calc (CP * cfg.δ / cfg.b) ^ ηF ≤ (CP * cfg.δ ^ τ) ^ ηF := NNReal.rpow_le_rpow h1 hηF.le
        _ = CP ^ ηF * (cfg.δ ^ τ) ^ ηF := NNReal.mul_rpow
        _ = CP ^ ηF * cfg.δ ^ (τ * ηF) := by rw [← NNReal.rpow_mul]
    have hCPpow : CP ^ (1 + ηF) = CP * CP ^ ηF := by
      rw [NNReal.rpow_add hCP0, NNReal.rpow_one]
    have hδpow : cfg.δ ^ (τ * ηF) = cfg.δ ^ (τ * ηF - 2 * cfg.η) * cfg.δ ^ (2 * cfg.η) := by
      rw [← NNReal.rpow_add hδ0]
      congr 1
      ring
    calc CP * (CP * cfg.δ / cfg.b) ^ ηF ≤ CP * (CP ^ ηF * cfg.δ ^ (τ * ηF)) := by gcongr
      _ = CP ^ (1 + ηF) * cfg.δ ^ (τ * ηF) := by rw [hCPpow, mul_assoc]
      _ = CP ^ (1 + ηF) * cfg.δ ^ (τ * ηF - 2 * cfg.η) * cfg.δ ^ (2 * cfg.η) := by
            rw [hδpow, ← mul_assoc]
      _ ≤ bd.c₁ * cfg.δ ^ (2 * cfg.η) := by gcongr

/-- **The `δ`-free half of blueprint `plankF`, at the canonical exponent.**

`Kakeya.VeryNotSticky.plankFrostmanVolume` derives blueprint `plankF` from `K_F(β)`, and
`Kakeya.VeryNotSticky.plankFrostmanVolumeAt_plankFrostmanExponent` moves it to the named
exponent `Kakeya.VeryNotSticky.plankFrostmanExponent β ε`. Composing them is what
`Kakeya.VeryNotSticky.exists_setup_caseSideData` must do **before** it fixes `δ`: the
non-concentration dilation `C_NC` and the parameter `b₀` produced here are functions of `β`
and `ε` alone, so the two thresholds of
`Kakeya.VeryNotSticky.plankFrostmanUsable_of_thick` are genuine smallness conditions on `δ`.

Recording the composition separately is what keeps that quantifier order visible; see the
docstring of `Kakeya.VeryNotSticky.plankFrostmanExponent` for why the exponent may not be
existentially bound here. -/
theorem exists_plankFrostmanVolumeAt_canonical {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) {ε : ℝ} (hε : 0 < ε) :
    ∃ C_NC : NNReal, 1 ≤ C_NC ∧ ∃ b₀ : NNReal, 0 < b₀ ∧
      PlankFrostmanVolumeAt.{u} β ε (plankFrostmanExponent.{u} β ε) b₀ C_NC :=
  plankFrostmanVolumeAt_plankFrostmanExponent (plankFrostmanVolume hβ hβ1 hF hε)

open MeasureTheory in
/-- **The thick-case bundle at the canonical plank-Frostman exponent.**

Three of the eight fields of `Kakeya.VeryNotSticky.ThickDensityThresholds` are discharged
here, at the exponent `ηF = Kakeya.VeryNotSticky.plankFrostmanExponent cfg.β (ϱβτ/8)` at
which `Kakeya.VeryNotSticky.exists_setup_caseSideData` instantiates the structure:

* `hηF` and `budget`, `0 < ηF` and `2η < τ ηF`, are two of the three conjuncts of the binder
  `hplankF` of that statement, `Kakeya.VeryNotSticky.PlankFrostmanBudget`, arranged ahead of
  `δ` by `Kakeya.VeryNotSticky.exists_caseParams`;
* `plankF` is `Kakeya.VeryNotSticky.plankFrostmanUsable_of_thick`, whose guard is the one the
  field already carries, from the `δ`-free plank estimate `hvol` (supplied by
  `Kakeya.VeryNotSticky.exists_plankFrostmanVolumeAt_canonical`) and the two fixed-scale
  thresholds `hb₀`, `hc₁`. Since F8  `hc₁` reads
  `CP^{1+ηF} δ^{τ ηF - 2η} ≤ c₁`, which `hbudget : 2η < τ ηF`
  supplies for small `δ` through `Kakeya.VeryNotSticky.eventually_plankFrostman_thresholds`
  read at `η := 2 cfg.η`; it is a binder here because the lemma is stated at one fixed `δ`.

What is left is `bias`, `plankPres` and `density`, the three the blueprint assumes rather than
discharges, plus the two constant normalizations `hCP` and `hΘ`. -/
theorem thickDensityThresholds_canonical {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    {τ ηF : ℝ} {CP Θ₀ C_NC b₀ : NNReal} (hCP : 1 ≤ CP) (hΘ₀ : 1 ≤ Θ₀) (hηF : 0 < ηF)
    (hbudget : 2 * cfg.η < τ * ηF)
    (hbias : (bd.Cbias : ENNReal) * (((48 * bd.C₀ ^ 6) ^ 3 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(τ * cfg.ϱ)))
    (hpres : cfg.δ ^ (1 - τ) ≤ cfg.a → ThickPlankPresentable bd CP Θ₀ C_NC)
    (hvol : PlankFrostmanVolumeAt.{u} cfg.β (cfg.ϱ * cfg.β * τ / 8) ηF b₀ C_NC)
    (hb₀ : CP * cfg.δ ^ τ ≤ b₀)
    (hc₁ : CP ^ (1 + ηF) * cfg.δ ^ (τ * ηF - 2 * cfg.η) ≤ bd.c₁)
    (hdensity : statement_of_universal_thickDensity_bare.{u} cfg bd τ CP Θ₀) :
    ThickDensityThresholds cfg bd τ CP Θ₀ C_NC ηF where
  hCP := hCP
  hΘ := hΘ₀
  bias := hbias
  plankPres := hpres
  hηF := hηF
  budget := hbudget
  plankF := fun hthick => plankFrostmanUsable_of_thick hCP hηF hthick hvol hb₀ hc₁
  density := hdensity

/-- **The threshold bundle is satisfiable at all three of its thresholds simultaneously.**

`Kakeya.VeryNotSticky.exists_scaleThresholds_of_le_one` exposes only the defining inequality
of `aScale`, which is all the thick chain spends. `Kakeya.VeryNotSticky.CaseScale` reads two
of the three thresholds — `aScaleData_threshold` at `aScale ν` and `typicalAngle_threshold` at
`typical` — so a producer of `Kakeya.VeryNotSticky.CaseSideData`, which has to assert the
`CaseScale` and the bundle it carries at one and the same `thr`, needs both at once. This is
that strengthening, at the same trivial witness: all three thresholds equal to `1`, absorbing
the constant `1`, for which `aScale_absorb` reads `1 ≤ δ^{-η}` and holds because `0 < δ ≤ 1`
and `η > 0`. The third inequality, at `fill`, is carried too, so that the statement covers
every field of `Kakeya.VeryNotSticky.ScaleThresholds` rather than the two in use today. -/
theorem exists_scaleThresholds_ge {δ : NNReal} (hδ1 : δ ≤ 1) :
    ∃ thr : ScaleThresholds,
      (∀ ν : ℝ, δ ≤ thr.aScale ν) ∧ δ ≤ thr.typical ∧ δ ≤ thr.fill := by
  refine ⟨{ aScale := fun _ => 1,
            aScale_mem := by intro ν; norm_num,
            aScaleConst := fun _ _ => 1,
            one_le_aScaleConst := by intro ν η; rfl,
            aScale_absorb := by
              intro ν η hη d hd hda
              have hd0 : (0 : ENNReal) < (d : ENNReal) := ENNReal.coe_pos.mpr hd
              have hd1 : (d : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr hda
              have hneg : -η < 0 := neg_lt_zero.mpr hη
              have hone : (1 : ENNReal) ≤ (d : ENNReal) ^ (-η) :=
                ENNReal.one_le_rpow_of_pos_of_le_one_of_neg hd0 hd1 hneg
              simpa using hone,
            typical := 1,
            typical_mem := by norm_num,
            fill := 1,
            fill_mem := by norm_num }, fun _ => hδ1, hδ1, hδ1⟩

/-- **The side data of the case split, from the five bundles that carry its content.**

`Kakeya.VeryNotSticky.CaseSideData` has eleven fields, of which four are data (`CP`, `Θ`,
`ηF`, `C_NC`) and seven carry content. This lemma discharges two of the seven, `thr` and
`thr_thick`, from the field `cfg.hδ1` alone, by
`Kakeya.VeryNotSticky.exists_scaleThresholds_of_le_one`: the threshold bundle carries no
defining property that ties it to the configuration, so the trivial bundle — all thresholds
`1`, absorbing the constant `1` — serves, and `cfg.δ ≤ 1` discharges the eighth clause of
Configuration `hyp:ml2scale` at *every* gain, in particular at the thick gain `ϱβτ/8` of
`thr_thick`.

It also decouples the `CaseScale` from the bundle. In `CaseSideData` the two are asserted
against one and the same `thr`, but `thr` occurs in `CaseScale` only through the single clause
`Kakeya.VeryNotSticky.CaseScale.aScaleData_threshold`, so a `CaseScale` at *any* threshold
bundle `thr₀` suffices: the clause is re-proved at the bundle produced here. A producer of the
side data therefore never has to match its threshold bundle to anyone else's.

What remains — `thick`, `tc`, `slabScale`, `caseScale` and `tangential` — is the genuine
content of blueprint `lem:ml2setupSideData`, three items of which the blueprint assumes rather
than discharges; see the docstring of `Kakeya.VeryNotSticky.CaseSideData`. -/
theorem nonempty_caseSideData {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {τ τ' : ℝ}
    {CP Θ C_NC : NNReal} {ηF : ℝ}
    (thick : ThickDensityThresholds cfg bd τ CP Θ C_NC ηF)
    (tc : ThinConfig cfg bd) (slabScale : SlabScale cfg bd tc τ)
    {thr₀ : ScaleThresholds}
    (caseScale : CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr₀)
    (tangential : cfg.a ≤ cfg.δ ^ (1 - τ) → cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) → TangentialInputs cfg tc τ') :
    Nonempty (CaseSideData cfg bd τ τ') := by
  obtain ⟨thr, hthr, htyp, -⟩ := exists_scaleThresholds_ge cfg.hδ1
  exact ⟨{ CP := CP
           Θ := Θ
           ηF := ηF
           C_NC := C_NC
           thick := thick
           thr := thr
           thr_thick := hthr _
           tc := tc
           slabScale := slabScale
           caseScale :=
             { caseScale with
               aScaleData_threshold := hthr _
               typicalAngle_threshold := htyp }
           tangential := tangential }⟩

/-- **The coarse endpoint of the `ρ`-counting window is in the window.**

The hypothesis `hcount` of `Kakeya.VeryNotSticky.exists_setup_caseSideData` is quantified over
`ρ ∈ [δ^{1-exscal}, δ^{exscal}]`, and the construction of Configuration `hyp:ml2setup` reads
its field `Kakeya.VeryNotSticky.tube_count` off that hypothesis at the coarse endpoint
`ρ = δ^{1-exscal}`. That endpoint is admissible exactly because `exscal < 1/2`, the field
`Kakeya.VeryNotSticky.CaseParams.scale`: with `0 < δ ≤ 1` the map `s ↦ δ^s` is antitone, so
`δ^{1-exscal} ≤ δ^{exscal}` as soon as `exscal ≤ 1 - exscal`. Without it the window is empty
and the counting hypothesis says nothing. -/
theorem coarseScale_mem_window {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {exscal : ℝ}
    (hexscal : exscal ≤ 1 / 2) :
    δ ^ (1 - exscal) ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) :=
  ⟨le_rfl, NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)⟩

open Topology Filter in
/-- **The multiscale grid is eventually fine enough** (the field
`Kakeya.VeryNotSticky.gridFine`).

`1 ≤ η ⌈log log 1/δ⌉` for all sufficiently small `δ`, for every fixed `η > 0`. This is the one
field of `Kakeya.VeryNotSticky` that is a condition on `δ` alone, involving no constant
produced after `δ`, and it is therefore discharged here rather than assumed: the grid length
`Tube.ssfGridLen δ = ⌈log log 1/δ⌉` tends to infinity as `δ → 0⁺`, because
`1/δ → ∞` and `log` tends to infinity along `atTop`, so `ssfGridLen δ` eventually exceeds
`1/η`.

This is the statement the docstring of `Kakeya.VeryNotSticky.gridFine` attributes to
`Kakeya.StickyKakeya.exists_ssfGridLen_threshold`: sub-polynomiality of the grid step is the
design intent of the grid length `log log 1/δ`. It is proved directly from
`Nat.le_ceil` and the two `atTop` limits, so it depends on nothing but the definition of the
grid length. -/
theorem eventually_gridFine {η : ℝ} (hη : 0 < η) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, 1 ≤ η * (Tube.ssfGridLen δ : ℝ) := by
  have h_coe_nhds : Tendsto (fun δ : NNReal => (δ : ℝ)) (𝓝[>] (0 : NNReal)) (𝓝 (0 : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hδ0 : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), 0 < δ := by
    simpa [Set.Ioi] using
      (eventually_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : NNReal), δ ∈ Set.Ioi (0 : NNReal))
  have h_coe : Tendsto (fun δ : NNReal => (δ : ℝ)) (𝓝[>] (0 : NNReal)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h_coe_nhds, ?_⟩
    filter_upwards [hδ0] with δ hδ
    exact_mod_cast hδ
  have h_inv : Tendsto (fun δ : NNReal => (1 : ℝ) / (δ : ℝ)) (𝓝[>] (0 : NNReal)) atTop := by
    simpa [Function.comp_def, one_div] using (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp h_coe
  have h_loglog : Tendsto (fun δ : NNReal => Real.log (Real.log (1 / (δ : ℝ))))
      (𝓝[>] (0 : NNReal)) atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h_inv)
  filter_upwards [h_loglog.eventually (eventually_ge_atTop (1 / η))] with δ hδ
  have hceil : 1 / η ≤ (Tube.ssfGridLen δ : ℝ) :=
    hδ.trans (Nat.le_ceil (Real.log (Real.log (1 / (δ : ℝ)))))
  have hmul := mul_le_mul_of_nonneg_left hceil hη.le
  rwa [mul_one_div, div_self hη.ne'] at hmul


open Topology Filter in
/-- **The typical-angle multiplicity threshold is eventually met** (the fourth clause of
Configuration `hyp:ml2scale`, `Kakeya.VeryNotSticky.CaseScale.multiplicity_large`).

`2 ≤ (δ/r₁)^{-η}` at `r₁ = δ^{exscal}`, for all sufficiently small `δ`. Like
`Kakeya.VeryNotSticky.eventually_gridFine` this is a condition on `δ` and the exponent
parameters alone — it mentions neither `bd.C₀` nor `bd.Cbias` nor the thin-case comparison
constant, the three quantities the construction produces only after `δ` — so it is discharged
here rather than assumed. Indeed `δ/r₁ = δ^{1-exscal}`, so the left-hand side is
`δ^{-(1-exscal)η}` and the exponent `(1-exscal)η` is positive and fixed before `δ`.

It is the only one of the thirteen clauses of `Kakeya.VeryNotSticky.CaseScale` with that
property; the other twelve all mention a constant produced after `δ`, and are therefore
arrangeable only alongside the construction of `Kakeya.VeryNotSticky.BallData`. -/
theorem eventually_multiplicity_large {η exscal : ℝ} (hη : 0 < η) (hexscal : exscal < 1) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      (2 : ENNReal) ≤ ((δ / δ ^ exscal : NNReal) : ENNReal) ^ (-η) := by
  have hρ : 0 < (1 - exscal) * η := mul_pos (by linarith) hη
  have hδ0 : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), 0 < δ := by
    simpa [Set.Ioi] using
      (eventually_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : NNReal), δ ∈ Set.Ioi (0 : NNReal))
  filter_upwards [ENNReal.eventually_coe_rpow_le_of_pos hρ
      (C := (1 : ENNReal) / 2) (by norm_num), hδ0] with δ hδ hδpos
  have hne : δ ≠ 0 := hδpos.ne'
  have hdiv : (δ / δ ^ exscal : NNReal) = δ ^ (1 - exscal) := by
    rw [NNReal.rpow_sub hne, NNReal.rpow_one]
  have hsign : (1 - exscal) * (-η) = -((1 - exscal) * η) := by ring
  rw [hdiv, ENNReal.coe_rpow_of_nonneg _ (by linarith : (0 : ℝ) ≤ 1 - exscal),
    ← ENNReal.rpow_mul, hsign, ENNReal.rpow_neg]
  calc (2 : ENNReal) = ((1 : ENNReal) / 2)⁻¹ := by norm_num
    _ ≤ ((δ : ENNReal) ^ ((1 - exscal) * η))⁻¹ := ENNReal.inv_le_inv' hδ

/-- **The exponent budget of blueprint `plankF`, at a free plank-Frostman exponent.**

`2η < τ ηF` for *some* exponent `ηF > 0` at which the plank-Frostman volume estimate
`Kakeya.VeryNotSticky.PlankFrostmanVolumeAt` holds, together with the two constants
`b₀`, `C_NC` that estimate carries.

**The factor `2` is R16-A**. GWZ's thick case applies Lemma 6.4 (`gwz.txt` l.806-808) to planks of short
side `δ/b ≤ δ/a ≤ δ^τ` (l.2110-2119) at fullness `λ(P, Y_P) ⪆ δ^η` (l.2121-2122); under the
`⪆` convention (l.153, every-`ε` slack) that is the budget `η < τ η_{6.4}`, with
`η = η(β, ζ)` chosen after `τ` and `η_{6.4}` (l.1776). This development renders every
`⪆ δ^η` on the path as `δ^{2η}` with a `δ`-free constant — since F8  also the per-segment density (C5), `Kakeya.VeryNotSticky.BallData.segs_density` —
so the second threshold of `plankF` reads `CP^{1+ηF} δ^{τ ηF - 2η} ≤ c₁` and the budget
stated against that rendering is `2η < τ ηF`. This is a *strengthening* of the hypothesis
(fewer admissible parameter tuples), i.e. a change of meaning of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` and of
`Kakeya.VeryNotSticky.SideDataResidue` with their texts unchanged; Lemma 9.1
(`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`) is unchanged in text and meaning and
re-closes from `Kakeya.VeryNotSticky.exists_caseParams` at `η ≤ τ η_{plankF}/4`.

This is the honest form of the binder that
`Kakeya.VeryNotSticky.exists_setup_caseSideData` used to state as
`η < τ * Kakeya.VeryNotSticky.plankFrostmanExponent β (ϱβτ/8)`.  That form named a
`Classical.choose` witness in a *statement*, which is a fidelity defect twice over: nothing in
the development bounds the chosen value from below, so the hypothesis is neither checkable nor
transportable; and the bundle the statement produces —
`Kakeya.VeryNotSticky.ThickDensityThresholds`, whose fields `hηF`, `budget` and `plankF` are
exactly the three conjuncts here — takes its exponent **free** already, so nothing downstream
ever wanted the canonical one.

It is a **weaker hypothesis** than the canonical-exponent form at the same factor, hence a
*strengthening* of every statement that assumes it:
`Kakeya.VeryNotSticky.plankFrostmanBudget_of_lt` derives it from
`2η < τ · plankFrostmanExponent β (ϱβτ/8)` and the Frostman estimate, which every consumer
has in scope.  Nothing is deferred: the data this
existential carries is precisely the data the old form recovered by calling
`Kakeya.VeryNotSticky.exists_plankFrostmanVolumeAt_canonical`. -/
def PlankFrostmanBudget (β ϱ τ η : ℝ) : Prop :=
  ∃ ηF : ℝ, 0 < ηF ∧ 2 * η < τ * ηF ∧
    ∃ C_NC : NNReal, 1 ≤ C_NC ∧ ∃ b₀ : NNReal, 0 < b₀ ∧
      PlankFrostmanVolumeAt.{u} β (ϱ * β * τ / 8) ηF b₀ C_NC

/-- **The `Classical.choose`-valued budget at `2η` implies the free-exponent one.**

Witnessed at `ηF = Kakeya.VeryNotSticky.plankFrostmanExponent β (ϱβτ/8)` itself, whose
positivity is `Kakeya.VeryNotSticky.plankFrostmanExponent_pos` and whose estimate is
`Kakeya.VeryNotSticky.exists_plankFrostmanVolumeAt_canonical`.  This is what lets
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge` keep discharging the budget out of
`Kakeya.VeryNotSticky.exists_caseParams`, which produces that form (R16-A: `2η < τ η_{plankF}`). -/
theorem plankFrostmanBudget_of_lt {β ϱ τ η : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hε : 0 < ϱ * β * τ / 8)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (h : 2 * η < τ * plankFrostmanExponent.{u} β (ϱ * β * τ / 8)) :
    PlankFrostmanBudget.{u} β ϱ τ η := by
  obtain ⟨C_NC, hC_NC, b₀, hb₀, hvol⟩ :=
    exists_plankFrostmanVolumeAt_canonical.{u} hβ hβ1 hF hε
  exact ⟨plankFrostmanExponent.{u} β (ϱ * β * τ / 8), plankFrostmanExponent_pos _ _, h,
    C_NC, hC_NC, b₀, hb₀, hvol⟩

open MeasureTheory Topology Filter ShadedBody in
/-- **The statement of the last Section-9 leaf, as a `Prop`** — the binders and the conclusion of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` verbatim. The leaf itself now lives in `MainLemma2/VeryNotStickyClosed.lean`, downstream of its
three producers ; this `Prop` is kept
here, at the leaf's former place, so that the chain that produces it (`exists_setup_caseSideData_general`
and its tripwires) can name the leaf's type without importing the leaf. The relocated leaf is stated with
the same text and proved by unfolding this definition — the two cannot drift apart. -/
def SetupCaseSideDataAt {β ζ exscal ϱ η τ τ' : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) : Prop :=
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∀ i ∈ s, (T i).toTube.IsCentred) →
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ∃ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (e : cfg.ι ≃ ι) (c : NNReal),
          (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
              cfg.η = η) ∧
          ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
              (fun i ↦ (cfg.T (e.symm i)).toShadedBody)
              s (fun i ↦ (T i).toShadedBody) c ∧
          (δ : ENNReal) ^ η ≤ (c : ENNReal) ∧
          Nonempty (CaseSideData cfg bd τ τ')

open MeasureTheory Topology Filter ShadedBody in
/-- **Main Lemma 2, very not sticky case: assembling the cases** (blueprint
`lem:ml2casesplit`).

Let `cfg` realize Configuration `hyp:ml2setup`, let `params` satisfy the explicit budgets of
Definition `hyp:ml2params`, and let `scale` satisfy Configuration `hyp:ml2scale`. Then the
goal `eqgoalmuT` holds with the gain
`ν = Kakeya.VeryNotSticky.casesplitExponent cfg.β cfg.ζ cfg.exscal τ τ' cfg.ϱ`, which is
positive by `Kakeya.VeryNotSticky.casesplitExponent_pos`.

The convex bodies `W ∈ 𝕎_B` have smallest affine thickness `τ₂(W) ∼ a`, and `a` does not
depend on `B` by (C4), so `le_total (cfg.δ ^ (1 - τ)) cfg.a` splits the proof into two
branches. If `δ^{1-τ} ≤ a` we are in the thick case and
`Kakeya.VeryNotSticky.goalMult_of_a_ge` gives the goal with exponent `ϱ β τ / 8`. If
`a ≤ δ^{1-τ}` we are in the thin case and `Kakeya.goalMult_of_a_le` gives it with exponent
`thinExponent cfg.β cfg.ζ cfg.exscal τ'`. In either case the exponent is at least `ν`, and
since `0 < δ ≤ 1` the map `s ↦ δ^s` is antitone
(`ENNReal.rpow_le_rpow_of_exponent_ge`), so the estimate with the larger exponent implies the
estimate with `ν`.

The field `cfg.hδ1` records `δ ≤ 1`, which makes `s ↦ δ^s` antitone.

The eleven fixed-scale smallness hypotheses in `δ` of Configuration `hyp:ml2scale` are
packaged as `Kakeya.VeryNotSticky.CaseScale` and threaded through the thin branch. The first
ensures that the dilated angular scale `ρ₂*` is at most one; the next three are consumed
inside `Kakeya.VeryNotSticky.exists_isTypicalAnglePlank`; the fifth,
`Kakeya.VeryNotSticky.CaseScale.transverse_radius`, is the transverse transfer-radius
threshold `6 C_{w₁}(C₀) ≤ δ^{-τ'}` consumed by
`Kakeya.VeryNotSticky.goalMult_of_theta_ge`; the seventh is what
`Kakeya.VeryNotSticky.transverseBallFill` spends on its constant; and the eighth, ninth,
tenth and eleventh are the by-choice thresholds bundled as
`Kakeya.VeryNotSticky.ScaleThresholds`, threaded from here to the leaves that will consume
them. They hold once `δ` is sufficiently small, with `bd.C₀`, `bd.Cbias`, `tc.C`, the gain and
the exponents fixed first, as required by the eventual top-level theorem.

This lemma is where Configuration `hyp:ml2scale` is *arranged*, and two of its clauses — the
seventh and the tenth — have left-hand sides produced after `δ`. The seventh mentions the
comparison constant `tc.C` of Configuration `hyp:ml2thinsetup`, which exists only once the
thin-case data does, so the bundle cannot be a free-standing hypothesis: like
`Kakeya.VeryNotSticky.SlabScale`, it travels inside `hslabScale`, the packaged form *there is
a thin configuration whose comparison constant satisfies the thresholds*. Packaging the thin
configuration together with both bundles is what makes the constant available, and it is why
this lemma consumes the thin data from `hslabScale` rather than calling
`Kakeya.VeryNotSticky.exists_thinConfig` itself; that lemma is what produces such a bundle,
and hence what will discharge `hslabScale` once `δ` is taken small in terms of the constant it
returns. Note that `exists_thinConfig` does not use the thin-case hypothesis `a ≤ δ^{1-τ}`, so
`hslabScale` is stated unconditionally.

**Both instances of the eighth clause are carried,** at the two gains by which blueprint
`lem:ml2casesplit` indexes it, and against the one shared `thr`. The `CaseScale` inside
`hslabScale` is read at the transverse gain `ν = τ'β/2`, the gain at which the thin chain
invokes `Kakeya.VeryNotSticky.exists_aScaleData` through
`Kakeya.VeryNotSticky.goalMult_of_theta_ge`; the separate `hthrThick` is the same clause at
the thick gain `ν_{lem:ml2thick} = ϱβτ/8`, which the thick branch needs because
`Kakeya.VeryNotSticky.goalMult_of_a_ge` reduces to
`Kakeya.VeryNotSticky.goalMult_of_a_ge_of_goalDensity`, and that in turn applies
`exists_aScaleData` at the thick gain.

The thick instance is a bare inequality rather than a second `CaseScale`, matching the binder
of blueprint `lem:ml2thickFromDens`: the clause mentions only `δ`, the gain and data fixed
before `δ`, whereas `CaseScale` also mentions `bd` and the thin-case constant `tc.C`, neither
of which the thick chain sees. Both gains are functions of `β` and `ζ` alone and are fixed
before `δ`, so, as the blueprint proof of `lem:ml2casesplit` records, taking the smaller of
the two thresholds arranges both at once; this lemma is where that is assumed, and no
declaration below it carries a fixed-scale threshold of its own.

Further hypotheses beyond Configuration `hyp:ml2setup` are needed and are therefore
explicit.

* `hβ1 : cfg.β ≤ 1`, which is hypothesis (T1) of blueprint `lem:ml2thick` and is consumed by
  the thick branch through `Kakeya.VeryNotSticky.goalMult_of_a_ge` and by the non-slab leaves
  of the thin branch, through `Kakeya.goalMult_of_a_le`, where the Katz–Tao bound
  `Kakeya.VeryNotSticky.nonslabKKT` needs it. It is not implied by
  `cfg.hβ`, which only gives `0 < β`, and `Kakeya.VeryNotSticky.CaseParams` carries no such
  budget; blueprint `hyp:ml2params` records that omission. It is threaded here rather than
  discharged, which is the first of the two remedies discussed in the note at the end of
  blueprint subsection `thickCaseSection`.
* `hdens : Kakeya.VeryNotSticky.ThickDensityThresholds cfg bd τ`, hypotheses (T3) and (T6) of
  blueprint `lem:ml2thick`: the two scale thresholds of blueprint `thickDensityThresholds`,
  the second in the form quantified over the constants that
  `Kakeya.VeryNotSticky.exists_denseInBody` produces and guarded by the thick-case
  hypothesis `δ^{1-τ} ≤ a` of `lem:ml2thickDensity`, which this proof supplies from the
  branch of its dichotomy where it holds. They are threaded by the same remedy
  and for the same reason as `hβ1`, and are named rather than written out because they occur
  verbatim as a field of `Kakeya.VeryNotSticky.CaseSideData` as well; see that
  structure.
* the third conjunct of `hslabScale`, `Nonempty (TangentialInputs cfg tc τ')`, which is items
  (a)–(c) of blueprint `lem:ml2tangential`. It travels inside `hslabScale` rather than as a
  free hypothesis because it mentions the thin-case data `tc`, exactly as
  `Kakeya.VeryNotSticky.SlabScale` and the seventh clause of `hyp:ml2scale` do; from here it
  is threaded through `Kakeya.goalMult_of_a_le`,
  `Kakeya.VeryNotSticky.goalMult_of_b_le` and
  `Kakeya.VeryNotSticky.goalMult_of_multBodies_ge` to the tangential leaf.
* `bd`: the thin branch needs Configuration `hyp:ml2thinsetup`. As the blueprint proof
  stresses, that is *not* an extra assumption on `(𝕋, Y)` — it is extra data attached to the
  very same pair, and `lem:ml2thinsetupexists` produces it from Configuration `hyp:ml2setup`
  and `a ≤ δ^{1-τ}`. So this lemma takes only the `cfg`-relative per-ball data
  `bd : Kakeya.VeryNotSticky.BallData cfg` of `hyp:ml2setup`, and obtains the thin-case bundle
  from `hslabScale`, packaged with its fixed-scale thresholds as explained above. No refinement
  of `(𝕋, Y)` is taken here: the pair fed to the thin case is the one already recorded by
  `cfg`. -/
theorem exists_goalMult (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ') (bd : BallData cfg)
    (hβ1 : cfg.β ≤ 1) {CP Θ C_NC : NNReal} {ηF : ℝ}
    (hdens : ThickDensityThresholds cfg bd τ CP Θ C_NC ηF)
    (thr : ScaleThresholds)
    (hthrThick : cfg.δ ≤ thr.aScale (cfg.ϱ * cfg.β * τ / 8))
    (hslabScale : ∃ tc : ThinConfig cfg bd,
      SlabScale cfg bd tc τ ∧ CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr ∧
        (cfg.a ≤ cfg.δ ^ (1 - τ) → cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) →
          Nonempty (TangentialInputs cfg tc τ'))) :
    cfg.goalMult (casesplitExponent cfg.β cfg.ζ cfg.exscal τ τ' cfg.ϱ) := by
  rcases le_total (cfg.δ ^ (1 - τ)) cfg.a with (hthick | hthin)
  · -- thick case: cfg.δ ^ (1 - τ) ≤ cfg.a
    have hthick_res : cfg.goalMult (cfg.ϱ * cfg.β * τ / 8) :=
      Kakeya.VeryNotSticky.goalMult_of_a_ge_of_bareThreshold cfg params bd hβ1 hthick
        hthrThick hdens.bias
        hdens.hCP hdens.hΘ hdens.hηF (hdens.plankF hthick) (hdens.plankPres hthick)
        (hdens.density hthick)
    have hδ1_ennreal : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
    set ν := casesplitExponent cfg.β cfg.ζ cfg.exscal τ τ' cfg.ϱ with hν_def
    have hν_le : ν ≤ cfg.ϱ * cfg.β * τ / 8 := min_le_left _ _
    have hpow : (cfg.δ : ENNReal) ^ (cfg.ϱ * cfg.β * τ / 8) ≤ (cfg.δ : ENNReal) ^ ν :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδ1_ennreal hν_le
    have h_mul : (cfg.δ : ENNReal) ^ (cfg.ϱ * cfg.β * τ / 8) * (cfg.s.card : ENNReal) ^ cfg.β ≤
      (cfg.δ : ENNReal) ^ ν * (cfg.s.card : ENNReal) ^ cfg.β := by
      gcongr
    exact le_trans hthick_res h_mul
  · -- thin case: cfg.a ≤ cfg.δ ^ (1 - τ)
    obtain ⟨tc, ss, scale, tin⟩ := hslabScale
    have hthin_res : cfg.goalMult (thinExponent cfg.β cfg.ζ cfg.exscal τ') :=
      Kakeya.goalMult_of_a_le cfg params hβ1 hthin tc scale ss (fun h₁ h₂ => (tin h₁ h₂).some)
    have hδ1_ennreal : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
    set ν := casesplitExponent cfg.β cfg.ζ cfg.exscal τ τ' cfg.ϱ with hν_def
    have hν_le : ν ≤ thinExponent cfg.β cfg.ζ cfg.exscal τ' := min_le_right _ _
    have hpow : (cfg.δ : ENNReal) ^ (thinExponent cfg.β cfg.ζ cfg.exscal τ') ≤
      (cfg.δ : ENNReal) ^ ν :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδ1_ennreal hν_le
    have h_mul : (cfg.δ : ENNReal) ^ (thinExponent cfg.β cfg.ζ cfg.exscal τ') *
      (cfg.s.card : ENNReal) ^ cfg.β ≤
      (cfg.δ : ENNReal) ^ ν * (cfg.s.card : ENNReal) ^ cfg.β := by
      gcongr
    exact le_trans hthin_res h_mul

end Kakeya.VeryNotSticky
