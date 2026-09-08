/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.WindowPacking

/-!
# The `C`-power budget of the Step-3 route into `reduction_to_slab_atTypicalAngle`

This file contains no geometry.  It is the arithmetic of one question:

> `ShadedPlank.reduction_to_slab_atTypicalAngle` must produce `c1` with `c1⁻¹ ≤ δ ^ (-ε')`, and it
> is handed a constant `C` with only `1 ≤ C ≤ δ ^ (-ε)`.  If the route it is proved by loses a
> factor `C ^ k` together with an absolute constant, for which `(k, ε, ε')` is that affordable?

The answer, `Plank.not_routeAffordsCPower`, is: **never, once `ε' ≤ k · ε`** — no threshold on `δ`
can rescue it, because the hypothesis `C ≤ δ ^ (-ε)` is *only* an upper bound and the adversary may
take `C = δ ^ (-ε)` exactly.  The gap must be strict, `k · ε < ε'`, with the strictness paying for
the absolute constant.

That turns the exponent bookkeeping of the route into a decidable question, and
`Plank.routePower_of_bounds` answers it: the Step-3 assembly's output constant is
`c1 = cBall · cLamBox ^ 2` with `cLamBox ≈ lamScale · a ^ (-η_L)` and
`lamScale = (2 · Cmult)⁻¹ · a ^ ε_int · lamLower / (512 · Nov · cTan)`
(`Plank.slabwiseDensity_of_preassembly`, `Kakeya.slabwiseDensity_of_outputs`), so

```
c1⁻¹  ≍  cBall⁻¹ · (Cmult · Nov · cTan / lamLower) ^ 2,
```

and if the five factors grow like `C ^ 1`, `C ^ 1`, `C ^ m`, `C ^ 2`, `C ^ (-1)` respectively then
`c1⁻¹` grows like `C ^ (9 + 2 m)`.  `Plank.routePower_floor` records the part of that which is
**not** an artefact: `cBall⁻¹ ∝ C` (from `Plank.slabwiseDensity_of_preassembly`'s exposed
`(100776960 * Ceta)⁻¹ ≤ cBall` together with `Ceta ∝ C · log C`), `Cmult ∝ C` (forced by
`ShadedBody.HasCConstantMultiplicity s Y'' C`) and `lamLower ∝ C⁻¹` (forced by
`ShadedBody.IsCRefinement s Y'' s (bodies Y) C⁻¹`) already give `k ≥ 5`, **whatever `Nov` and `cTan`
are**.

So `2 * ε ≤ ε'` cannot be enough, and neither can `4 * ε ≤ ε'`.

`Plank.step3_floor_refutes_two_eps` and `Plank.step3_floor_refutes_four_eps` are the two
instantiations, and the two `example`s below are the tripwires: they take the affordability claim as
a hypothesis and derive `False`.
-/

@[expose] public section

open scoped NNReal Real

noncomputable section

namespace Plank

/-! ## The affordability predicate -/

/-- **"The route loses `Kabs · C ^ k`, and that is affordable."**

The scalar shape of every obligation of the form *"the produced constant `c1` satisfies
`c1⁻¹ ≤ δ ^ (-ε')`, where `c1⁻¹ = Kabs · C ^ k` and the incoming constant obeys
`1 ≤ C ≤ δ ^ (-ε)`"*.  The threshold `δthr` may be chosen first, exactly as
`ShadedPlank.reduction_to_slab_atTypicalAngle` chooses it, and `δ` and `C` come afterwards. -/
def RouteAffordsCPower (ε ε' k : ℝ) (Kabs : ℝ≥0) : Prop :=
  ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ δ C : ℝ≥0, 0 < δ → δ ≤ δthr → 1 ≤ C → C ≤ δ ^ (-ε) →
      Kabs * C ^ k ≤ δ ^ (-ε')

/-- **A non-strict exponent gap is never affordable.**

If `ε' ≤ k · ε` and the absolute constant exceeds `1`, then `Plank.RouteAffordsCPower ε ε' k Kabs`
is false: no threshold `δthr` works, because at every scale the adversary may take `C = δ ^ (-ε)`
exactly, and then the two sides differ by the factor `Kabs > 1` alone.

This is why the gap in `ShadedPlank.reduction_to_slab_atTypicalAngle`'s hypothesis `2 * ε ≤ ε'` has
to be compared against the route's `k` **strictly**: `k · ε < ε'`, with the slack paying for the
absolute constant. -/
theorem not_routeAffordsCPower {ε ε' k : ℝ} (hε : 0 < ε) (hgap : ε' ≤ k * ε)
    {Kabs : ℝ≥0} (hK : 1 < Kabs) : ¬ RouteAffordsCPower ε ε' k Kabs := by
  rintro ⟨δthr, hδpos, hδ1, H⟩
  have h1C : (1 : ℝ≥0) ≤ δthr ^ (-ε) := by
    have h := NNReal.rpow_le_rpow_of_exponent_ge hδpos hδ1
      (show (-ε) ≤ (0 : ℝ) by linarith)
    simpa using h
  have hmain := H δthr (δthr ^ (-ε)) hδpos le_rfl h1C le_rfl
  have hpow : (δthr ^ (-ε) : ℝ≥0) ^ k = δthr ^ (-(k * ε)) := by
    rw [← NNReal.rpow_mul]
    congr 1
    ring
  rw [hpow] at hmain
  have hmono : (δthr : ℝ≥0) ^ (-ε') ≤ δthr ^ (-(k * ε)) :=
    NNReal.rpow_le_rpow_of_exponent_ge hδpos hδ1 (by linarith)
  have htpos : (0 : ℝ≥0) < δthr ^ (-(k * ε)) := NNReal.rpow_pos hδpos
  have hfinal : Kabs * δthr ^ (-(k * ε)) ≤ 1 * δthr ^ (-(k * ε)) := by
    rw [one_mul]
    exact hmain.trans hmono
  exact absurd (le_of_mul_le_mul_right hfinal htpos) (not_le.mpr hK)

/-- **Affordability is antitone in the exponent.**  If losing `C ^ k'` is affordable then so is
losing `C ^ k` for any `k ≤ k'`, because `C ≥ 1`.  This is the step that lets a *lower* bound on the
route's `C`-power refute affordability. -/
theorem RouteAffordsCPower.mono_exponent {ε ε' k k' : ℝ} (hkk : k ≤ k') {Kabs : ℝ≥0}
    (h : RouteAffordsCPower ε ε' k' Kabs) : RouteAffordsCPower ε ε' k Kabs := by
  obtain ⟨δthr, hδpos, hδ1, H⟩ := h
  refine ⟨δthr, hδpos, hδ1, ?_⟩
  intro δ C hδ0 hδle hC hCle
  exact le_trans (mul_le_mul' le_rfl (NNReal.rpow_le_rpow_of_exponent_le hC hkk))
    (H δ C hδ0 hδle hC hCle)

/-- **A route whose `C`-power is at or above a known floor, with a non-strict gap, is refuted.**
The composition of `Plank.RouteAffordsCPower.mono_exponent` with
`Plank.not_routeAffordsCPower`: a *lower* bound `kfloor ≤ k` on the loss suffices. -/
theorem not_routeAffordsCPower_of_floor {ε ε' k kfloor : ℝ} (hε : 0 < ε)
    (hfloor : kfloor ≤ k) (hgap : ε' ≤ kfloor * ε) {Kabs : ℝ≥0} (hK : 1 < Kabs) :
    ¬ RouteAffordsCPower ε ε' k Kabs :=
  fun h => not_routeAffordsCPower hε hgap hK (h.mono_exponent hfloor)

/-! ## Composing the powers of the Step-3 assembly -/

/-- **The `C`-power of the Step-3 output constant, composed.**

`c1⁻¹ ≍ cBall⁻¹ · (Cmult · Nov · cTan / lamLower) ^ 2`, so if

* `cBall⁻¹ ≤ K₁ · C`      (from the exposed `(100776960 * Ceta)⁻¹ ≤ cBall` and `Ceta ∝ C · log C`),
* `Cmult ≤ K₂ · C`        (forced by `ShadedBody.HasCConstantMultiplicity s Y'' C`),
* `lamLower⁻¹ ≤ K₃ · C`   (forced by `ShadedBody.IsCRefinement s Y'' s (bodies Y) C⁻¹`),
* `cTan ≤ K₄ · C ^ 2`     (from the exposed `cTan ≤ max 1728 (8192 * Cang' ^ 2)`, `Cang' ∝ C`),
* `Nov ≤ K₅ · C ^ m`,

then `c1⁻¹ ≤ K · C ^ (9 + 2 * m)`.  The exponent `9 + 2 m = 1 + 2 * (1 + 1 + 2 + m)` is the whole
content: the four inner factors are squared because `cLamBox` enters `c1` squared. -/
theorem routePower_of_bounds {C K₁ K₂ K₃ K₄ K₅ x₁ x₂ x₃ x₄ x₅ : ℝ≥0} (hC : 1 ≤ C) {m : ℝ}
    (h₁ : x₁ ≤ K₁ * C ^ (1 : ℝ)) (h₂ : x₂ ≤ K₂ * C ^ (1 : ℝ))
    (h₃ : x₃ ≤ K₃ * C ^ (1 : ℝ)) (h₄ : x₄ ≤ K₄ * C ^ (2 : ℝ))
    (h₅ : x₅ ≤ K₅ * C ^ m) :
    x₁ * (x₂ * x₃ * x₄ * x₅) ^ (2 : ℝ)
      ≤ (K₁ * (K₂ * K₃ * K₄ * K₅) ^ (2 : ℝ)) * C ^ (9 + 2 * m) := by
  have hC0 : (C : ℝ≥0) ≠ 0 := by
    intro h
    rw [h] at hC
    exact absurd hC (by norm_num)
  have hinner : x₂ * x₃ * x₄ * x₅ ≤ (K₂ * K₃ * K₄ * K₅) * C ^ (1 + 1 + 2 + m) := by
    calc x₂ * x₃ * x₄ * x₅
        ≤ (K₂ * C ^ (1 : ℝ)) * (K₃ * C ^ (1 : ℝ)) * (K₄ * C ^ (2 : ℝ)) * (K₅ * C ^ m) :=
          mul_le_mul' (mul_le_mul' (mul_le_mul' h₂ h₃) h₄) h₅
      _ = (K₂ * K₃ * K₄ * K₅) * (C ^ (1 : ℝ) * C ^ (1 : ℝ) * C ^ (2 : ℝ) * C ^ m) := by ring
      _ = (K₂ * K₃ * K₄ * K₅) * C ^ (1 + 1 + 2 + m) := by
          rw [← NNReal.rpow_add hC0, ← NNReal.rpow_add hC0, ← NNReal.rpow_add hC0]
  calc x₁ * (x₂ * x₃ * x₄ * x₅) ^ (2 : ℝ)
      ≤ (K₁ * C ^ (1 : ℝ)) * ((K₂ * K₃ * K₄ * K₅) * C ^ (1 + 1 + 2 + m)) ^ (2 : ℝ) :=
        mul_le_mul' h₁ (NNReal.rpow_le_rpow hinner (by norm_num))
    _ = (K₁ * (K₂ * K₃ * K₄ * K₅) ^ (2 : ℝ)) *
          (C ^ (1 : ℝ) * (C ^ (1 + 1 + 2 + m)) ^ (2 : ℝ)) := by
        rw [NNReal.mul_rpow]; ring
    _ = (K₁ * (K₂ * K₃ * K₄ * K₅) ^ (2 : ℝ)) * C ^ (9 + 2 * m) := by
        rw [← NNReal.rpow_mul, ← NNReal.rpow_add hC0]
        congr 2
        ring

/-- **The part of the Step-3 `C`-power that is not an artefact: `k ≥ 5`.**

Even if the slab-overlap count `Nov` and the tangentiality constant `cTan` were **absolute**, the
three factors that the target's own hypotheses force — `cBall⁻¹ ∝ C`, `Cmult ∝ C`,
`lamLower⁻¹ ∝ C` — already compose to `C ^ 5`, because the last two are squared.

This is `Plank.routePower_of_bounds` with the `cTan` and `Nov` factors dropped, and it is the reason
neither `2 * ε ≤ ε'` nor `4 * ε ≤ ε'` can be enough. -/
theorem routePower_floor {C K₁ K₂ K₃ x₁ x₂ x₃ : ℝ≥0} (hC : 1 ≤ C)
    (h₁ : x₁ ≤ K₁ * C ^ (1 : ℝ)) (h₂ : x₂ ≤ K₂ * C ^ (1 : ℝ))
    (h₃ : x₃ ≤ K₃ * C ^ (1 : ℝ)) :
    x₁ * (x₂ * x₃) ^ (2 : ℝ) ≤ (K₁ * (K₂ * K₃) ^ (2 : ℝ)) * C ^ (5 : ℝ) := by
  have hC0 : (C : ℝ≥0) ≠ 0 := by
    intro h
    rw [h] at hC
    exact absurd hC (by norm_num)
  have hinner : x₂ * x₃ ≤ (K₂ * K₃) * C ^ (2 : ℝ) := by
    calc x₂ * x₃ ≤ (K₂ * C ^ (1 : ℝ)) * (K₃ * C ^ (1 : ℝ)) := mul_le_mul' h₂ h₃
      _ = (K₂ * K₃) * (C ^ (1 : ℝ) * C ^ (1 : ℝ)) := by ring
      _ = (K₂ * K₃) * C ^ (2 : ℝ) := by
          rw [← NNReal.rpow_add hC0]
          norm_num
  calc x₁ * (x₂ * x₃) ^ (2 : ℝ)
      ≤ (K₁ * C ^ (1 : ℝ)) * ((K₂ * K₃) * C ^ (2 : ℝ)) ^ (2 : ℝ) :=
        mul_le_mul' h₁ (NNReal.rpow_le_rpow hinner (by norm_num))
    _ = (K₁ * (K₂ * K₃) ^ (2 : ℝ)) * (C ^ (1 : ℝ) * (C ^ (2 : ℝ)) ^ (2 : ℝ)) := by
        rw [NNReal.mul_rpow]; ring
    _ = (K₁ * (K₂ * K₃) ^ (2 : ℝ)) * C ^ (5 : ℝ) := by
        rw [← NNReal.rpow_mul, ← NNReal.rpow_add hC0]
        norm_num

/-! ## The two verdicts -/

/-- **`2 * ε ≤ ε'` cannot pay for the Step-3 route.**  At the floor `k = 5` of
`Plank.routePower_floor`, and at the exponents the only call site uses
(`Kakeya.VeryNotSticky.exists_isReductionFillAvailable_uniform`: now `ε = η/256`, `ε' = η/2`, i.e.
`ε' = 2 ε`), affordability is false for every absolute constant `> 1`. -/
theorem step3_floor_refutes_two_eps {ε k : ℝ} (hε : 0 < ε) (hk : 5 ≤ k) {Kabs : ℝ≥0}
    (hK : 1 < Kabs) : ¬ RouteAffordsCPower ε (2 * ε) k Kabs :=
  not_routeAffordsCPower_of_floor hε hk (by linarith) hK

/-- **The pre-authorised `4 * ε ≤ ε'` cannot pay for it either.**  Same floor `k = 5`. -/
theorem step3_floor_refutes_four_eps {ε k : ℝ} (hε : 0 < ε) (hk : 5 ≤ k) {Kabs : ℝ≥0}
    (hK : 1 < Kabs) : ¬ RouteAffordsCPower ε (4 * ε) k Kabs :=
  not_routeAffordsCPower_of_floor hε hk (by linarith) hK

/-- **`5 * ε ≤ ε'` is still not enough** — the gap has to be strict, because the absolute constant
has to be paid for.  This is the sharpest form of the obstruction. -/
theorem step3_floor_refutes_five_eps {ε k : ℝ} (hε : 0 < ε) (hk : 5 ≤ k) {Kabs : ℝ≥0}
    (hK : 1 < Kabs) : ¬ RouteAffordsCPower ε (5 * ε) k Kabs :=
  not_routeAffordsCPower_of_floor hε hk (by linarith) hK

/-- Tripwire for `2 * ε ≤ ε'`.  Anyone who believes the Step-3 route closes
`ShadedPlank.reduction_to_slab_atTypicalAngle` under its stated hypothesis `2 * ε ≤ ε'`, with an
absolute loss of `100 · C ^ 5`, is asserting `h`; and `h` is false. -/
example (h : ∀ {ε : ℝ}, 0 < ε → RouteAffordsCPower ε (2 * ε) 5 100) : False :=
  step3_floor_refutes_two_eps (ε := 1) one_pos le_rfl (by norm_num) (h one_pos)

/-- Tripwire for the pre-authorised `4 * ε ≤ ε'`. -/
example (h : ∀ {ε : ℝ}, 0 < ε → RouteAffordsCPower ε (4 * ε) 5 100) : False :=
  step3_floor_refutes_four_eps (ε := 1) one_pos le_rfl (by norm_num) (h one_pos)

/-- **The obstruction is exactly the absolute constant**, for contrast: with `k * ε ≤ ε'` and an
absolute loss of at most `1`, affordability holds at `δthr = 1`.  Recorded so that
`Plank.not_routeAffordsCPower` is not mistaken for an impossibility in principle: what fails is
paying for a constant `> 1` out of a non-strict exponent gap. -/
theorem routeAffordsCPower_of_le_one {ε ε' k : ℝ} (hk : 0 ≤ k) (hgap : k * ε ≤ ε')
    {Kabs : ℝ≥0} (hK : Kabs ≤ 1) : RouteAffordsCPower ε ε' k Kabs := by
  refine ⟨1, one_pos, le_rfl, ?_⟩
  intro δ C hδ0 hδle _ hCle
  have hCk : C ^ k ≤ δ ^ (-(k * ε)) := by
    calc C ^ k ≤ (δ ^ (-ε)) ^ k := NNReal.rpow_le_rpow hCle hk
      _ = δ ^ (-(k * ε)) := by rw [← NNReal.rpow_mul]; congr 1; ring
  calc Kabs * C ^ k ≤ 1 * δ ^ (-(k * ε)) := mul_le_mul' hK hCk
    _ = δ ^ (-(k * ε)) := one_mul _
    _ ≤ δ ^ (-ε') := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδle (by linarith)

/-! ## The ledger, pinned so that a repair of the binder cannot retire the refutation

`ShadedPlank.reduction_to_slab_atTypicalAngle` **used to** offer the gap `2 * ε ≤ ε'`, and now
offers `128 * ε ≤ ε'`.  That repair is exactly the change this section was written to survive: a
tripwire stated *about the binder* would not have survived it — it would silently have stopped
biting.  So the refutation is stated here about `Plank.Step3LedgerPayable`, a predicate
that mentions only the **gap multiplier** `g` a statement offers and the **`C`-power** `k` a route
loses.  `Plank.not_step3LedgerPayable` then bites for every `g ≤ k`, hence for the former `g = 2`,
for the pre-authorised `g = 4`, and for any future repair that stops at or below the floor `k = 5`.
-/

/-- **The exact obligation any Step-3 proof of `ShadedPlank.reduction_to_slab_atTypicalAngle` must
discharge**, as a function of the gap multiplier `g` the statement's binder offers (now `128`,
via `128 * ε ≤ ε'`) and of the `C`-power `k` the route loses (at least `5`, by
`Plank.routePower_floor`).

Deliberately independent of that binder — and the repair to `128 * ε ≤ ε'` has since demonstrated
it: this file compiled **unchanged** across that change, because it imports only
`Kakeya.DimensionThree.Plank.WindowPacking` and never mentions the binder.  Changing the binder
cannot make this predicate vacuous, and cannot make `Plank.not_step3LedgerPayable` stop biting. -/
def Step3LedgerPayable (g k : ℝ) : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ∀ Kabs : ℝ≥0, 1 < Kabs → RouteAffordsCPower ε (g * ε) k Kabs

/-- **A gap multiplier at or below the route's `C`-power is never payable.**

The durable form of `Plank.not_routeAffordsCPower`.  It refutes every `g ≤ k` at once, so it
survives any repair of `ShadedPlank.reduction_to_slab_atTypicalAngle`'s binder that does not raise
the multiplier **strictly** above the route's power. -/
theorem not_step3LedgerPayable {g k : ℝ} (hg : g ≤ k) : ¬ Step3LedgerPayable g k := by
  intro h
  exact not_routeAffordsCPower (ε := 1) one_pos
    (show g * 1 ≤ k * 1 by simpa using hg)
    (show (1 : ℝ≥0) < 2 by norm_num)
    (h one_pos 2 (by norm_num))

/-- **A strictly larger gap multiplier is payable, at a threshold chosen after the constant.**

This is the constructive half, and it says exactly what a genuine repair has to supply: not a
smaller absolute constant, and not a threshold on `δ` at the current gap, but a gap multiplier
*strictly greater* than the route's `C`-power.  The threshold is `Kabs ^ (-(g - k)⁻¹)`. -/
theorem routeAffordsCPower_of_strict {ε ε' k : ℝ} (hk : 0 ≤ k)
    (hgap : k * ε < ε') {Kabs : ℝ≥0} (hK : 1 ≤ Kabs) :
    RouteAffordsCPower ε ε' k Kabs := by
  set d : ℝ := ε' - k * ε with hd_def
  have hd : 0 < d := by rw [hd_def]; linarith
  have hKpos : (0 : ℝ≥0) < Kabs := lt_of_lt_of_le zero_lt_one hK
  refine ⟨Kabs ^ (-d⁻¹), NNReal.rpow_pos hKpos, ?_, ?_⟩
  · have h := NNReal.rpow_le_rpow_of_exponent_le hK
      (show (-d⁻¹) ≤ (0 : ℝ) by simp only [neg_nonpos]; positivity)
    simpa using h
  · intro δ C hδ0 hδle _ hCle
    have hδ1 : δ ≤ 1 := by
      refine hδle.trans ?_
      have h := NNReal.rpow_le_rpow_of_exponent_le hK
        (show (-d⁻¹) ≤ (0 : ℝ) by simp only [neg_nonpos]; positivity)
      simpa using h
    -- `Kabs ≤ δ ^ (-d)`
    have hthr : Kabs ≤ δ ^ (-d) := by
      have hbase : δ ^ d ≤ (Kabs ^ (-d⁻¹)) ^ d := NNReal.rpow_le_rpow hδle hd.le
      have hval : (Kabs ^ (-d⁻¹)) ^ d = Kabs⁻¹ := by
        rw [← NNReal.rpow_mul]
        rw [show (-d⁻¹) * d = -1 by field_simp]
        rw [NNReal.rpow_neg_one]
      rw [hval] at hbase
      have hδd : (0 : ℝ≥0) < δ ^ d := NNReal.rpow_pos hδ0
      have := (NNReal.le_inv_iff_mul_le (by positivity)).mp hbase
      rw [NNReal.rpow_neg]
      exact le_inv_of_le_inv₀ hδd (by simpa using hbase)
    have hCk : C ^ k ≤ δ ^ (-(k * ε)) := by
      calc C ^ k ≤ (δ ^ (-ε)) ^ k := NNReal.rpow_le_rpow hCle hk
        _ = δ ^ (-(k * ε)) := by rw [← NNReal.rpow_mul]; congr 1; ring
    calc Kabs * C ^ k ≤ δ ^ (-d) * δ ^ (-(k * ε)) := mul_le_mul' hthr hCk
      _ = δ ^ (-d + -(k * ε)) := (NNReal.rpow_add hδ0.ne' _ _).symm
      _ = δ ^ (-ε') := by rw [hd_def]; congr 1; ring

/-- **The repair criterion.**  Granting nothing but a gap multiplier strictly above the route's
`C`-power, the ledger is payable.  Together with `Plank.not_step3LedgerPayable` this is a
dichotomy: `Step3LedgerPayable g k` holds iff `k < g`. -/
theorem step3LedgerPayable_of_strict {g k : ℝ} (hk : 0 ≤ k) (hgap : k < g) :
    Step3LedgerPayable g k := by
  intro ε hε Kabs hKabs
  exact routeAffordsCPower_of_strict hk (by nlinarith) (le_of_lt hKabs)

/-- Tripwire at the gap `ShadedPlank.reduction_to_slab_atTypicalAngle` currently offers, `g = 2`. -/
example (h : Step3LedgerPayable 2 5) : False := not_step3LedgerPayable (by norm_num) h

/-- Tripwire at the pre-authorised `4 * ε ≤ ε'`, `g = 4`. -/
example (h : Step3LedgerPayable 4 5) : False := not_step3LedgerPayable (by norm_num) h

/-- Tripwire at `g = 5`: the gap must be **strict**, so even matching the floor fails. -/
example (h : Step3LedgerPayable 5 5) : False := not_step3LedgerPayable le_rfl h

/-- Tripwire at the gap multiplier `8` that a first repair attempt would naturally pick, against the
`C`-power `9` of the route with the *best possible* `Nov` and `cTan`: `8` clears the irreducible
floor `5` but **not** the achievable route.  This is the record that `8 * ε ≤ ε'` is the cheapest
sufficient relation for the floor and **not** the honest one. -/
example (h : Step3LedgerPayable 8 9) : False := not_step3LedgerPayable (by norm_num) h

/-! ### The repaired binder, `128 * ε ≤ ε'`, and why the multiplier is `128`

`ShadedPlank.reduction_to_slab_atTypicalAngle` now offers `128 * ε ≤ ε'`, read by its two
dischargers at `ε = η/256`, `ε' = η/2` — where `128 * (η/256) = η/2` **exactly**, so the numerals
cannot drift apart without `le_of_eq (by ring)` failing in
`Kakeya.VeryNotSticky.exists_isReductionFillAvailable`.

Two independent traces of the route's `C`-power `k` exist and they disagree, so both are pinned
here rather than one being believed: `k = 105`
and `k = 57` (, tracing `Plank.slab_pointwise_overlap_le` to `⌈(2(4K+r)/r)^12⌉` with
`K = Θ(C)` **and** `r = Θ(1/C)`, so the ratio is quadratic in `C` and `Nov = Θ(C^24)`, giving
`k = 9 + 2·24 = 57`).

`128` clears both. The four facts below are the whole justification of that numeral, and they are
kernel-checked rather than argued: the repair is payable against **either** trace, `64` is payable
against the smaller trace but **not** the larger, and `32` is payable against neither. So `128` is
the least power of two that clears both traces, and the choice is not slack. -/
theorem step3LedgerPayable_128_57 : Step3LedgerPayable 128 57 :=
  step3LedgerPayable_of_strict (by norm_num) (by norm_num)

/-- The repaired multiplier is payable against g's larger trace `k = 105` too. -/
theorem step3LedgerPayable_128_105 : Step3LedgerPayable 128 105 :=
  step3LedgerPayable_of_strict (by norm_num) (by norm_num)

/-- **`64` is not enough against `k = 105`.**  The record that halving the repaired multiplier
fails against g's trace, so `128` is not overkill. -/
example (h : Step3LedgerPayable 64 105) : False := not_step3LedgerPayable (by norm_num) h

/-- **`32` is not enough even against the smaller trace `k = 57`.** -/
example (h : Step3LedgerPayable 32 57) : False := not_step3LedgerPayable (by norm_num) h

/-- **The gap must still be strict at the repaired multiplier**: matching the power exactly fails,
exactly as at `g = k = 5`.  This is what stops a later "simplification" from setting `k := g`. -/
example (h : Step3LedgerPayable 128 128) : False := not_step3LedgerPayable le_rfl h

end Plank

end
