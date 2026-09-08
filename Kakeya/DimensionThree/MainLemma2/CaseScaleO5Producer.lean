/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.CaseScaleNonslabRefute
public import Kakeya.DimensionThree.Slab.Multiplicity

/-!
# G6 — the producer of O5 (`CaseScale.transverseFill_fullness`) at general `(a, b)`

**What this file delivers.** `Kakeya.VeryNotSticky.eventually_caseScale_O5_of_C_le` proves the
clause O5 of Configuration `hyp:ml2scale` — the field
`Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness`, pinned as the named `Prop`
`Kakeya.VeryNotSticky.statement_of_universal_caseScale_O5`
(`MainLemma2/CaseScaleNonslabRefute.lean`) — for **every** configuration at the recorded
hypotheses, eventually as `δ → 0⁺`. Until now that clause had exactly one producer route: it is
*vacuous* at `a = b` because its transverse guard `δ^{-τ'}·(a/b) ≤ 1` is false there
(`Kakeya.VeryNotSticky.not_transverseGuard_of_a_eq_b`), which is what
`Kakeya.VeryNotSticky.eventually_caseScale_of_C_le` uses and what confines the existing
`CaseScale` producer to the degenerate path `a = b = δ`. This file replaces that appeal to
`cfg.a = cfg.b` by a proof.

**Read the two existing refutations first, because they fix the target shape.**

* `MainLemma2/CaseScaleNonslabRefute.lean` — `Kakeya.VeryNotSticky.false_of_transverseFill_fullness`
  refutes the **pre-** O5: unguarded, with the middle plank dimension `b'` *unpinned*,
  at exponent `cfg.η`, with the `ThinBall` index `cfg.η`. Its witness takes `b' := 1` and an
  axis-aligned `a' × 1 × 1` prism, whose carrier volume `8a'` is far too small to be paid for by
  the body-shade masses in the non-slab regime. **What this file targets is the repaired clause**,
  and every one of the three repairs is load-bearing here:
  * the **upper pin `b' ≤ C₀·(b/r₁)`** is what makes the plank carriers comparable to the body
    carriers — it is used as `hbup` in `plank_fullness_ge`, and without it the refutation's
    `b' = 1` makes `fullness t SP` arbitrarily small;
  * the **`ThinBall` index `2·cfg.η`**  is what makes
    `Kakeya.ThinCase.ThinBall.fullness_bodies` read `δ^{6·cfg.η}` and not `δ^{3·cfg.η}`;
  * the **exponent `16·cfg.η`** together with
    `Kakeya.VeryNotSticky.CaseParams.thinHalf : τ + exscal ≤ 1/2` is what makes the budget close;
    at any fixed multiple `k·η` with `k` chosen before `τ + exscal ≤ 1/2` it does not.
  So the row is **not** refuted: `false_of_transverseFill_fullness` takes the old text verbatim as
  its hypothesis `hO5` and, as its own docstring records, does not entail the live field.
* `MainLemma2/ThinPerBallRefute.lean` — `Kakeya.ThinCase.PerBallRefute` refutes
  `Kakeya.ThinCase.perBall` without its localisation binder `hloc`. That is a constraint on the
  *producer of the `ThinBall`*, not on this file: every input `tb` here is **given**, and the
  repaired `perBall`/`thinSetupExists`/`exists_thinConfig` chain that builds one already carries
  `hloc` and discharges it from `Kakeya.VeryNotSticky.BallData.bodies_subset_ball`. Nothing below
  uses `perBall`; the only `ThinBall` fields read are `fullness_bodies`, `bodies'_subset` and
  `Wb_le_W`.

**One hypothesis this file needs that the O5 field does not carry: `hthin : cfg.a ≤ cfg.δ^{1-τ}`.**
This is recorded, not hidden. Under the transverse guard alone one gets only
`a/r₁ ≤ δ^{τ'}`, and `a'^{16η} ≤ C₀^{16η}·δ^{16τ'η}` beats `δ^{6η}` only if `16τ' > 6 + exscal`,
which `Kakeya.VeryNotSticky.CaseParams.transverse : 3τ + 87η < τ'·β` does not give. With the thin
guard one gets `a' ≤ C₀·δ^{1-τ-exscal}` and, under `thinHalf`, `16η(1-τ-exscal) ≥ 8η > 6η + ε`.
So a `CaseScale` at general `(a, b)` is available exactly on the **thin** branch — the same guard
`Kakeya.VeryNotSticky.CaseScale.plank_small` already carries as an antecedent, and the same guard
the general-branch row G9 must carry. It is an explicit binder of
`eventually_caseScale_O5_of_C_le` and of every consumer in
`MainLemma2/SetupThresholdsGeneral.lean`.

**The chain**:

1. `Kakeya.ThinCase.ThinBall.fullness_bodies` at the `tb` index `2·cfg.η`:
   `δ^{6η} ≤ C · λ(𝕎'_B, Y_{𝕎'_B})`.
2. `Kakeya.ShadedBody.sum_volumeReal_shade_eq_fullness_mul` turns that into a lower bound on the
   body-shade mass `∑_{𝕎'_B}|Y(W)|` in terms of the body-carrier mass `∑_{𝕎'_B}|W|`.
3. O5's own mass pin keeps a
   `(C^{sel})⁻¹ = plankSelectionConstant(C₀)⁻¹` fraction of it on the selection `t`.
4. `Kakeya.VeryNotSticky.BallData.bodies_thickness` and `Kakeya.HasThicknesses.le_volume` give the
   carrier floor `|W| ≥ r₁·b·a/(6C₀³)` per body (through the enlargement sandwich
   `Kakeya.ThinCase.ThinBall.Wb_le_W`), so `∑_{𝕎'_B}|W| ≥ #t · r₁ b a/(6C₀³)`.
5. O5's transport pin turns body-shade mass into plank-shade mass at the factor `(2r₁)³`, and
   `Kakeya.ShadedPlank.volume_carrier` evaluates the plank carriers at `8a'b'` exactly. The two
   `#t`'s **cancel**: the bound does not depend on the size of the selection.
6. `hupper : a' ≤ C₀(a/r₁)` and `hbup : b' ≤ C₀(b/r₁)` pay for the change of carrier at a
   `δ`-free `C₀²`, giving `λ(t, SP) ≥ δ^{6η}/(384·C₀⁵·C^{sel}·C)` — the constant
   `Kakeya.VeryNotSticky.o5PlankConstant`.
7. `hthin` and `hupper` give `a'^{16η} ≤ C₀^{16η}·δ^{16η(1-τ-exscal)}`, and the budget
   `6η + ε < 16η(1-τ-exscal)` — supplied from `CaseParams.thinHalf` by
   `Kakeya.VeryNotSticky.o5_budget_of_thinHalf` — absorbs every `δ`-free constant.

Nothing here changes an existing statement; the O5 pin
`Kakeya.VeryNotSticky.statement_of_universal_caseScale_O5` and its tripwire
`…_pinned` are untouched and are what this file's conclusion is stated against.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody

universe u

/-! ### The `δ`-free constant of the plank fullness bound -/

/-- **The `δ`-free loss of the plank-fullness transport**, `384·C₀⁵·C^{sel}(C₀)`.

`384 = 64 · 6` is `8` (the plank carrier `8a'b'`) times `8` (the transport factor `(2r₁)³ = 8r₁³`)
times `6` (the inscribed-simplex constant of `Kakeya.HasThicknesses.le_volume` in `ℝ³`); the five
powers of `C₀` are three from the carrier floor `r₁ b a/(6C₀³)` and one each from the pins
`a' ≤ C₀(a/r₁)`, `b' ≤ C₀(b/r₁)`; `Kakeya.VeryNotSticky.plankSelectionConstant` is O5's own
selection loss. -/
noncomputable def o5PlankConstant (C₀ : NNReal) : NNReal :=
  384 * C₀ ^ 5 * plankSelectionConstant C₀

lemma one_le_o5PlankConstant {C₀ : NNReal} (hC₀ : 1 ≤ C₀) : 1 ≤ o5PlankConstant C₀ := by
  have h1 : (1 : NNReal) ≤ C₀ ^ 5 := one_le_pow₀ hC₀
  have h2 : (1 : NNReal) ≤ plankSelectionConstant C₀ := one_le_plankSelectionConstant C₀
  have h3 : (1 : NNReal) * (1 * 1) ≤ 384 * (C₀ ^ 5 * plankSelectionConstant C₀) :=
    mul_le_mul' (by norm_num) (mul_le_mul' h1 h2)
  simpa [o5PlankConstant, mul_assoc] using h3

/-! ### The two geometric inputs -/

/-- **The carrier floor of a factoring body**: `|W| ≥ r₁·b·a/(6C₀³)`.

`Kakeya.VeryNotSticky.BallData.bodies_thickness` (clause (C4)) gives the affine thickness profile
`∼ (r₁, b, a)` at constant `C₀`, and `Kakeya.HasThicknesses.le_volume` — the inscribed-simplex
bound, constant `1/3! = 1/6` in `ℝ³` — turns it into a volume floor. The outer shaded body
`tb.W j` of the thin configuration is an *enlargement* of the geometric body `bd.Wb j`
(`Kakeya.ThinCase.ThinBall.Wb_le_W`, the lower half of the enlargement sandwich), so the floor
transports to it by monotonicity. -/
theorem bodyVolume_ge (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {C : NNReal}
    {B : bd.bι} (hB : B ∈ bd.bs)
    (tb : ThinCase.ThinBall C bd.C₀ (bd.segs B) bd.Y (bd.bodies B) bd.Wb bd.blk
      cfg.δ cfg.a (2 * cfg.η)) {j : bd.ω} (hj : j ∈ tb.bodies') :
    ((cfg.r₁ * cfg.b * cfg.a / (6 * bd.C₀ ^ 3) : NNReal) : ENNReal)
      ≤ volume (tb.W j).carrier := by
  have hj' : j ∈ bd.bodies B := tb.bodies'_subset hj
  have hprof := bd.bodies_thickness B hB j hj'
  have hvol := Kakeya.HasThicknesses.le_volume bd.hC₀ (bd.Wb j)
    (cfg.r₁ : NNReal).coe_nonneg (cfg.b : NNReal).coe_nonneg (cfg.a : NNReal).coe_nonneg hprof
  have hmono : volume (bd.Wb j).carrier ≤ volume (tb.W j).carrier :=
    measure_mono (SetLike.coe_subset_coe.mpr (tb.Wb_le_W j hj))
  refine le_trans (le_trans (le_of_eq ?_) hvol) hmono
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1

/-- **The body-family shading mass is positive**, from the fullness clause (T2) alone: were it
zero, `Kakeya.ShadedBody.fullness` would be zero and (T2) would read `δ^{6η} ≤ 0`. -/
theorem sum_shade_bodies_pos (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {C : NNReal}
    {B : bd.bι}
    (tb : ThinCase.ThinBall C bd.C₀ (bd.segs B) bd.Y (bd.bodies B) bd.Wb bd.blk
      cfg.δ cfg.a (2 * cfg.η)) :
    0 < ∑ i ∈ tb.bodies', volume (tb.W i).shade := by
  rcases eq_or_lt_of_le
      (show (0 : ENNReal) ≤ ∑ i ∈ tb.bodies', volume (tb.W i).shade from zero_le) with h | h
  · exfalso
    have hf : ShadedBody.fullness tb.bodies' tb.W = 0 := by
      have h0 : ((ShadedBody.fullness tb.bodies' tb.W : NNReal) : ENNReal) = 0 := by
        rw [ShadedBody.fullness_def tb.bodies' tb.W, ← h]
        simp
      exact_mod_cast h0
    have hfb := tb.fullness_bodies
    rw [hf] at hfb
    simp only [ENNReal.coe_zero, mul_zero, nonpos_iff_eq_zero] at hfb
    exact absurd hfb (ENNReal.rpow_pos (ENNReal.coe_pos.mpr cfg.hδ) ENNReal.coe_ne_top).ne'
  · exact h

/-! ### The plank-fullness lower bound — the geometric half of O5 -/

/-- **The plank family of O5 has fullness `≥ δ^{6η}/(384 C₀⁵ C^{sel} C)`.**

This is the whole geometric content of O5, at O5's own hypotheses and with *no* budget: the
transverse guard is not used, the lower pin `C₀⁻¹(a/r₁) ≤ a'` is not used, and neither is the
size of the selection `t` — the two occurrences of `#t` cancel. See the module docstring for the
seven-step chain; the constants are `Kakeya.VeryNotSticky.o5PlankConstant` and the `ThinBall`
comparison constant `C`. -/
theorem plank_fullness_ge (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {C : NNReal}
    {B : bd.bι} (hB : B ∈ bd.bs)
    (tb : ThinCase.ThinBall C bd.C₀ (bd.segs B) bd.Y (bd.bodies B) bd.Wb bd.blk
      cfg.δ cfg.a (2 * cfg.η))
    {a' b' : NNReal} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}
    (t : Finset bd.ω) (SP : bd.ω → ShadedPlank a' b' hab' hb1')
    (hts : t ⊆ tb.bodies')
    (hupper : a' ≤ bd.C₀ * (cfg.a / cfg.r₁))
    (hbup : b' ≤ bd.C₀ * (cfg.b / cfg.r₁))
    (hsel : ((plankSelectionConstant bd.C₀ : ENNReal))⁻¹ *
        (∑ i ∈ tb.bodies', volume (tb.W i).shade) ≤ ∑ i ∈ t, volume (tb.W i).shade)
    (hvol : ∀ i ∈ t, volume (ShadedPlank.bodies SP i).shade *
        ENNReal.ofReal ((2 * (cfg.r₁ : ℝ)) ^ 3) = volume (tb.W i).shade) :
    (cfg.δ : ENNReal) ^ (6 * cfg.η) ≤
      ((o5PlankConstant bd.C₀ * C : NNReal) : ENNReal) *
        ((ShadedBody.fullness t (ShadedPlank.bodies SP) : NNReal) : ENNReal) := by
  classical
  set Csel : NNReal := plankSelectionConstant bd.C₀ with hCsel
  set c₃ : NNReal := 8 * cfg.r₁ ^ 3 with hc₃
  set V₀ : NNReal := cfg.r₁ * cfg.b * cfg.a / (6 * bd.C₀ ^ 3) with hV₀
  set Ssp : ENNReal := ∑ i ∈ t, volume (ShadedPlank.bodies SP i).shade with hSsp
  set Csp : ENNReal := ∑ i ∈ t, volume (ShadedPlank.bodies SP i).carrier with hCsp
  set Sw : ENNReal := ∑ i ∈ t, volume (tb.W i).shade with hSw
  set Sbs : ENNReal := ∑ i ∈ tb.bodies', volume (tb.W i).shade with hSbs
  set Cbs : ENNReal := ∑ i ∈ tb.bodies', volume (tb.W i).carrier with hCbs
  have hr0 : (0 : NNReal) < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  have hC₀0 : (0 : NNReal) < bd.C₀ := lt_of_lt_of_le zero_lt_one bd.hC₀
  have hCsel0 : Csel ≠ 0 := by
    rw [hCsel]
    exact (lt_of_lt_of_le zero_lt_one (one_le_plankSelectionConstant bd.C₀)).ne'
  have hc₃E : ENNReal.ofReal ((2 * (cfg.r₁ : ℝ)) ^ 3) = (c₃ : ENNReal) := by
    rw [hc₃, ← ENNReal.ofReal_coe_nnreal]
    congr 1
    push_cast
    ring
  have hc₃0 : (c₃ : NNReal) ≠ 0 := by rw [hc₃]; positivity
  -- Step 1: the transport pin, summed
  have hstep1 : Ssp * (c₃ : ENNReal) = Sw := by
    rw [hSsp, hSw, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [← hc₃E]; exact hvol i hi
  -- Step 2: the plank carriers are exactly `8a'b'`
  have hstep2 : Csp = (t.card : ENNReal) * ((8 * a' * b' : NNReal) : ENNReal) := by
    rw [hCsp, Finset.sum_congr rfl (fun i _ => ShadedPlank.volume_carrier (SP i)),
      Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  -- Step 3: the body-carrier floor
  have hstep3 : (t.card : ENNReal) * (V₀ : ENNReal) ≤ Cbs := by
    rw [hCbs]
    calc (t.card : ENNReal) * (V₀ : ENNReal)
        = ∑ _i ∈ t, (V₀ : ENNReal) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ t, volume (tb.W i).carrier :=
          Finset.sum_le_sum fun i hi => bodyVolume_ge cfg bd hB tb (hts hi)
      _ ≤ ∑ i ∈ tb.bodies', volume (tb.W i).carrier :=
          Finset.sum_le_sum_of_subset hts
  -- Step 4: the change of carrier, `8a'b'·(2r₁)³ ≤ 384 C₀⁵ · r₁ b a/(6C₀³)`
  have hnum : (8 * a' * b' * c₃ : NNReal) ≤ 384 * bd.C₀ ^ 5 * V₀ := by
    calc (8 * a' * b' * c₃ : NNReal)
        ≤ 8 * (bd.C₀ * (cfg.a / cfg.r₁)) * (bd.C₀ * (cfg.b / cfg.r₁)) * c₃ := by gcongr
      _ = 384 * bd.C₀ ^ 5 * V₀ := by
          rw [hc₃, hV₀]
          apply NNReal.coe_injective
          have hr : (cfg.r₁ : ℝ) ≠ 0 := by exact_mod_cast hr0.ne'
          have hC : (bd.C₀ : ℝ) ≠ 0 := by exact_mod_cast hC₀0.ne'
          push_cast
          field_simp
          ring
  -- Step 5: positivity, so that the fullness quotient is not `0/0`
  have hSbs0 : 0 < Sbs := sum_shade_bodies_pos cfg bd tb
  have hSw0 : 0 < Sw := by
    refine lt_of_lt_of_le ?_ hsel
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top) hSbs0.ne'
  have hSsp0 : Ssp ≠ 0 := by
    intro h
    rw [h, zero_mul] at hstep1
    exact hSw0.ne' hstep1.symm
  have hCsp0 : Csp ≠ 0 := by
    intro h
    refine hSsp0 ?_
    have hle : Ssp ≤ Csp :=
      Finset.sum_le_sum fun i _ => measure_mono (ShadedPlank.bodies SP i).shade_subset
    rw [h] at hle
    exact nonpos_iff_eq_zero.mp hle
  have hCspT : Csp ≠ ⊤ := by
    rw [hstep2]
    exact ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
  -- Step 6: the selection pin, cleared of its inverse
  have hsel' : Sbs ≤ (Csel : ENNReal) * Sw := by
    have h : (Csel : ENNReal) * (((Csel : ENNReal))⁻¹ * Sbs) ≤ (Csel : ENNReal) * Sw := by
      gcongr
    rwa [← mul_assoc,
      ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr hCsel0) ENNReal.coe_ne_top,
      one_mul] at h
  -- Step 7: the chain
  have key : (cfg.δ : ENNReal) ^ (6 * cfg.η) * Csp * (c₃ : ENNReal) ≤
      ((o5PlankConstant bd.C₀ * C : NNReal) : ENNReal) * Sw := by
    have hfb : (cfg.δ : ENNReal) ^ (6 * cfg.η) ≤
        (C : ENNReal) * ((ShadedBody.fullness tb.bodies' tb.W : NNReal) : ENNReal) := by
      have h := tb.fullness_bodies
      rwa [show (3 : ℝ) * (2 * cfg.η) = 6 * cfg.η by ring] at h
    calc (cfg.δ : ENNReal) ^ (6 * cfg.η) * Csp * (c₃ : ENNReal)
        = (t.card : ENNReal) * ((cfg.δ : ENNReal) ^ (6 * cfg.η) *
            ((8 * a' * b' * c₃ : NNReal) : ENNReal)) := by
          rw [hstep2]; push_cast; ring
      _ ≤ (t.card : ENNReal) * ((cfg.δ : ENNReal) ^ (6 * cfg.η) *
            ((384 * bd.C₀ ^ 5 * V₀ : NNReal) : ENNReal)) := by
          gcongr
      _ = ((384 * bd.C₀ ^ 5 : NNReal) : ENNReal) *
            ((cfg.δ : ENNReal) ^ (6 * cfg.η) * ((t.card : ENNReal) * (V₀ : ENNReal))) := by
          push_cast
          ring
      _ ≤ ((384 * bd.C₀ ^ 5 : NNReal) : ENNReal) *
            (((C : ENNReal) * ((ShadedBody.fullness tb.bodies' tb.W : NNReal) : ENNReal)) *
              Cbs) := by
          gcongr
      _ = ((384 * bd.C₀ ^ 5 : NNReal) : ENNReal) * ((C : ENNReal) * Sbs) := by
          rw [hSbs, ShadedBody.sum_volumeReal_shade_eq_fullness_mul, ← hCbs]
          ring
      _ ≤ ((384 * bd.C₀ ^ 5 : NNReal) : ENNReal) * ((C : ENNReal) * ((Csel : ENNReal) * Sw)) := by
          gcongr
      _ = ((o5PlankConstant bd.C₀ * C : NNReal) : ENNReal) * Sw := by
          rw [o5PlankConstant, ← hCsel]
          push_cast
          ring
  -- Step 8: divide out the transport factor and read the quotient as a fullness
  have hc₃E0 : (c₃ : ENNReal) ≠ 0 := by exact_mod_cast hc₃0
  have hdiv : Ssp = Sw / (c₃ : ENNReal) := by
    rw [← hstep1, ENNReal.mul_div_cancel_right hc₃E0 ENNReal.coe_ne_top]
  rw [ShadedBody.fullness_def, ← hSsp, ← hCsp, ← mul_div_assoc,
    ENNReal.le_div_iff_mul_le (Or.inl hCsp0) (Or.inl hCspT), hdiv, ← mul_div_assoc,
    ENNReal.le_div_iff_mul_le (Or.inl hc₃E0) (Or.inl ENNReal.coe_ne_top)]
  exact key

/-! ### The exponent budget -/

/-- **The O5 budget from `Kakeya.VeryNotSticky.CaseParams.thinHalf`**: `τ + exscal ≤ 1/2` forces `16η(1 - τ - exscal) ≥ 8η`, which beats
`6η + ε` for every `ε ≤ η`. The numeral `16` cannot be replaced by a smaller fixed multiple
chosen before `thinHalf`: at `1 - τ - exscal = 7/k` the left side is exactly `7η`. -/
lemma o5_budget_of_thinHalf {exscal η τ ε : ℝ} (hη : 0 < η) (hthinHalf : τ + exscal ≤ 1 / 2)
    (hε : ε ≤ η) : 6 * η + ε < 16 * η * (1 - τ - exscal) := by nlinarith

/-! ### The producer -/

/-- **G6: the O5 clause of `Kakeya.VeryNotSticky.CaseScale`, produced at general `(a, b)`.**

The conclusion is the pinned `Prop` `Kakeya.VeryNotSticky.statement_of_universal_caseScale_O5`
— i.e. the field `Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness` verbatim, by
`Kakeya.VeryNotSticky.statement_of_universal_caseScale_O5_pinned` — with **no** appeal to
`cfg.a = cfg.b`. It therefore replaces `Kakeya.VeryNotSticky.not_transverseGuard_of_a_eq_b` in
`Kakeya.VeryNotSticky.eventually_caseScale_of_C_le`, which is what confined the existing `CaseScale`
producer to the degenerate path.

The hypotheses are: the pins `cfg.δ = d`, `cfg.exscal = exscal`, `cfg.η = η`, `bd.C₀ = C₀`; and the
thin-constant bound `1 ≤ C ≤ cfg.δ^{-ε}`. The **thin guard** `cfg.a ≤ cfg.δ^{1-τ}` is no longer
an outer binder: it is the first antecedent of the clause
itself, so this theorem produces O5 for **every** `(a, b)` and the guard is discharged by
whoever consumes the clause. The budget `hbud` is
`Kakeya.VeryNotSticky.o5_budget_of_thinHalf` at any `ε ≤ η`. -/
theorem eventually_caseScale_O5_of_C_le (C₀ : NNReal) (hC₀ : 1 ≤ C₀)
    {exscal η τ τ' ε : ℝ} (hη : 0 < η)
    (hbud : 6 * η + ε < 16 * η * (1 - τ - exscal)) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (C : NNReal),
        cfg.δ = d → cfg.exscal = exscal → cfg.η = η → bd.C₀ = C₀ →
        1 ≤ C → C ≤ cfg.δ ^ (-ε) →
        statement_of_universal_caseScale_O5 cfg bd τ τ' C := by
  filter_upwards [eventually_nnreal_le_rpow_neg (o5PlankConstant C₀ * C₀ ^ (16 * η))
      (show (0 : ℝ) < 16 * η * (1 - τ - exscal) - 6 * η - ε by linarith),
    self_mem_nhdsWithin] with d hK hd0
  intro cfg bd C hδ hex hη' hC₀' h1C hCle hthin _hguard B hB tb a' b' hab' hb1' t SP hts
    _hlow hupper hbup hsel hvol
  have hdpos : (0 : NNReal) < cfg.δ := cfg.hδ
  have hdne : cfg.δ ≠ 0 := hdpos.ne'
  have hr0 : (0 : NNReal) < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  -- the geometric half
  have hgeom := plank_fullness_ge cfg bd hB tb t SP hts hupper hbup hsel hvol
  rw [← ENNReal.coe_rpow_of_ne_zero hdne, ← ENNReal.coe_mul, ENNReal.coe_le_coe] at hgeom
  -- the thin guard, pushed through the upper pin
  have hupper' : a' ≤ C₀ * cfg.δ ^ (1 - τ - exscal) := by
    refine hupper.trans ?_
    rw [hC₀']
    gcongr
    calc cfg.a / cfg.r₁ ≤ cfg.δ ^ (1 - τ) / cfg.δ ^ exscal := by
          rw [show cfg.r₁ = cfg.δ ^ cfg.exscal from rfl, hex]
          gcongr
      _ = cfg.δ ^ (1 - τ - exscal) := by
          rw [show (1 : ℝ) - τ - exscal = (1 - τ) - exscal from by ring]
          exact (NNReal.rpow_sub hdne (1 - τ) exscal).symm
  -- the budget
  have hnum : o5PlankConstant bd.C₀ * C * a' ^ (16 * cfg.η) ≤ cfg.δ ^ (6 * cfg.η) := by
    rw [hC₀', hη']
    calc o5PlankConstant C₀ * C * a' ^ (16 * η)
        ≤ o5PlankConstant C₀ * cfg.δ ^ (-ε) * (C₀ * cfg.δ ^ (1 - τ - exscal)) ^ (16 * η) := by
          gcongr
      _ = (o5PlankConstant C₀ * C₀ ^ (16 * η)) *
            (cfg.δ ^ (-ε) * cfg.δ ^ ((1 - τ - exscal) * (16 * η))) := by
          rw [NNReal.mul_rpow, ← NNReal.rpow_mul]
          ring
      _ ≤ cfg.δ ^ (-(16 * η * (1 - τ - exscal) - 6 * η - ε)) *
            (cfg.δ ^ (-ε) * cfg.δ ^ ((1 - τ - exscal) * (16 * η))) := by
          gcongr
          rw [hδ]
          exact hK
      _ = cfg.δ ^ (6 * η) := by
          rw [← NNReal.rpow_add hdne, ← NNReal.rpow_add hdne]
          congr 1
          ring
  -- cancel the positive `δ`-free factor
  have hpos : (0 : NNReal) < o5PlankConstant bd.C₀ * C := by
    refine mul_pos (lt_of_lt_of_le zero_lt_one ?_) (lt_of_lt_of_le zero_lt_one h1C)
    rw [hC₀']
    exact one_le_o5PlankConstant hC₀
  exact le_of_mul_le_mul_left (hnum.trans hgeom) hpos

/-! ### Tripwires -/

/-- Tripwire 1: what `eventually_caseScale_O5_of_C_le` produces is exactly the field
`Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness`, read through the pin
`Kakeya.VeryNotSticky.statement_of_universal_caseScale_O5`. The proof is the identity, so this
`example` breaks the moment either side moves. -/
example (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {τ τ' ν : ℝ} {C : NNReal}
    {thr : ScaleThresholds} (scale : CaseScale cfg bd τ τ' ν C thr) :
    statement_of_universal_caseScale_O5 cfg bd τ τ' C :=
  scale.transverseFill_fullness

/-- Tripwire 2: the geometric bound is stated at O5's own hypotheses — the transverse guard and
the lower pin `C₀⁻¹(a/r₁) ≤ a'` are **not** among them, so `plank_fullness_ge` applies verbatim
inside any consumer of the field, in particular in the regime `a = b` where the guard is false. -/
example (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {C : NNReal}
    {B : bd.bι} (hB : B ∈ bd.bs)
    (tb : ThinCase.ThinBall C bd.C₀ (bd.segs B) bd.Y (bd.bodies B) bd.Wb bd.blk
      cfg.δ cfg.a (2 * cfg.η))
    {a' b' : NNReal} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}
    (t : Finset bd.ω) (SP : bd.ω → ShadedPlank a' b' hab' hb1')
    (hts : t ⊆ tb.bodies')
    (hupper : a' ≤ bd.C₀ * (cfg.a / cfg.r₁))
    (hbup : b' ≤ bd.C₀ * (cfg.b / cfg.r₁))
    (hsel : ((plankSelectionConstant bd.C₀ : ENNReal))⁻¹ *
        (∑ i ∈ tb.bodies', volume (tb.W i).shade) ≤ ∑ i ∈ t, volume (tb.W i).shade)
    (hvol : ∀ i ∈ t, volume (ShadedPlank.bodies SP i).shade *
        ENNReal.ofReal ((2 * (cfg.r₁ : ℝ)) ^ 3) = volume (tb.W i).shade) :
    (cfg.δ : ENNReal) ^ (6 * cfg.η) ≤
      ((o5PlankConstant bd.C₀ * C : NNReal) : ENNReal) *
        ((ShadedBody.fullness t (ShadedPlank.bodies SP) : NNReal) : ENNReal) :=
  plank_fullness_ge cfg bd hB tb t SP hts hupper hbup hsel hvol

end Kakeya.VeryNotSticky
