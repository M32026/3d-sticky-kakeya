/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Section6PartBWiring

/-!
# The Part-(B) volume-ratio exponent is logarithmic in `1 / δ`, and absorbable

`Kakeya.PartBLoss.exists_threshold_rpow_le_fullnessConstant`
(`Kakeya/DimensionThree/Plank/PartBLossAbsorption.lean`) needs
`((N + 1 : ℕ) : ℝ≥0∞) ≤ δ ^ (-η)` for the volume-ratio exponent `N` of the Part-(B)
Proposition-5.1 input.  This file supplies every ingredient of that bound **except** one, which is
blocked by a missing attribute in another component's file; see "What is blocked" below.

## ⚠ A phantom citation in a existing file

`Kakeya/DimensionThree/Plank/Section6PartBProp51Input.lean` documents
`Kakeya.Section6PartBData.fineVolumeRatio` with

> *"… it is **logarithmic** in `1/δ`, which is what
> `Kakeya.Section6PartBData.fineVolumeRatio_exponent_spec` records."*

**`fineVolumeRatio_exponent_spec` does not exist** — `grep -rn` over `Kakeya/` at this tip returns
exactly that one docstring line and no declaration.

## What is here

The complete `N`- and `M`-hypotheses of
`Kakeya.PartBLoss.exists_threshold_rpow_le_fullnessConstant`, and the statement
`Section6PartBProp51Input.lean` asserted in prose:

* `ofFiniteVolumeBounds_exponent_le` / `…_of_lt_two_pow` — reaching the exponent, which
  `ShadedBody.OuterInnerVolumeRatio.ofFiniteVolumeBounds` builds as `Nat.clog 2 (Nat.find …)`.
  Three lines: `Nat.find_le`, `Nat.clog_mono_right`, and `Nat.clog_pow` for the dyadic form;
* `one_le_two_pow_mul`, `exists_le_two_pow_mul`, `lt_two_pow_mul_of_le` — the dyadic bound
  `V < 2 ^ (3k + j + 1) · (C · δ³)`, because
  `2 ^ (3k+j+1) · (C · δ³) = 2 · (2 ^ j · C) · (2 ^ k · δ)³ ≥ 2V > V`.  Entirely in `ℝ≥0∞`; the only
  real-number step is `k = Nat.log 2 ⌈δ⁻¹⌉₊ + 1`;
* `exists_partB_volumeRatio_offset` — the `δ`-free offset at Part (B)'s own two quantities;
* **`fineVolumeRatio_exponent_le_log`** and **`fineVolumeRatio_exponent_spec`** — the exponent bound
  `≤ 3 · (Nat.log 2 ⌈δ⁻¹⌉₊ + 1) + j + 1`, and the `∃ j` form that is the statement
  `Section6PartBProp51Input.lean` cites;
* `ceil_inv_le_sq`, `exists_threshold_log_offset_le_rpow_neg` — the absorption of that shape, reusing
  f's existing `Section6PartBData.dyadicPigeonholeNatConstant_le_pow_one_add_logb` at `m = 2` and
  `ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg` at `k = 3`;
* **`exists_threshold_fineVolumeRatio_exponent_succ_le_rpow_neg`** — the `N`-hypothesis, assembled;
* **`exists_threshold_card_le_rpow_neg_seven`** — the `M`-hypothesis, from
  `Tube.card_le_of_EssDistinct`'s `δ ^ (-6)` count (exponent `2n = 6`, not `4`) with a whole factor
  `1/δ` of slack absorbing its constant.

## The one attribute this needed, and why

`ShadedBody.OuterInnerVolumeRatio.ofFiniteVolumeBounds` did not carry `@[expose]`, while its sibling
`ofVolumeBounds` one declaration above it did.  Under the module system that made the exponent opaque
to every `module` file: `show` reported *"not definitionally equal"* and `unfold` *"failed to
unfold"*, while the identical proof from a plain-`import` file.  Diagnosed by bisection —
same proof, same namespace, with and without `noncomputable section` and `@[expose] public section`;
the only variable that breaks it is `module` + `public import`.

**One attribute was added, on that one declaration, and nothing else in `Kakeya/Factoring/`**; the
rationale is recorded at the declaration itself.  `@[expose]` only makes a body visible across module
boundaries: it cannot change what any existing proof proves and cannot make a false statement
provable.  This is also the reason the prose claim in `Section6PartBProp51Input.lean` was never
written as a theorem — the tooling made the true statement unprovable, so the author asserted it
instead.
-/

@[expose] public section

open MeasureTheory Filter Topology

open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

namespace PartBLoss

open _root_.ShadedBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι κ : Type*} [DecidableEq κ]

/-! ### Reaching the exponent

`ShadedBody.OuterInnerVolumeRatio.ofFiniteVolumeBounds` builds its exponent as
`Nat.clog 2 (Nat.find …)`.  It carries `@[expose]` — added by this steps, see the note in
`Kakeya/Factoring/WeightedPipeline.lean` — so the body is visible here and the bound is three
lines. -/

omit [DecidableEq κ] in
/-- **The exponent produced by `ShadedBody.OuterInnerVolumeRatio.ofFiniteVolumeBounds` is at most
`Nat.clog 2 n` for any `n` above the volume ratio.**

`Nat.find_le` bounds the `Nat.find`, `Nat.clog_mono_right` finishes.  This is what makes the
exponent reachable at all: before `ofFiniteVolumeBounds` was exposed, no `module` caller could bound
it, which is why the claim it supports had to be asserted in prose. -/
theorem ofFiniteVolumeBounds_exponent_le (F : FactorFamily E ι κ)
    (ob ib : ENNReal)
    (houter : ∀ j ∈ F.outerSet, volume (F.outerBody j).carrier ≤ ob)
    (hinner : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j, ib ≤ volume (F.innerBody i).carrier)
    (hobTop : ob ≠ ∞) (hibPos : 0 < ib) (hibTop : ib ≠ ∞)
    {n : ℕ} (hn : ob / ib < (n : ENNReal)) :
    (OuterInnerVolumeRatio.ofFiniteVolumeBounds F ob ib houter hinner hobTop hibPos
        hibTop).exponent ≤ Nat.clog 2 n := by
  have hfind : Nat.find (ENNReal.exists_nat_gt
      (ENNReal.div_ne_top hobTop hibPos.ne')) ≤ n := Nat.find_le hn
  show Nat.clog 2 (Nat.find (ENNReal.exists_nat_gt
      (ENNReal.div_ne_top hobTop hibPos.ne'))) ≤ Nat.clog 2 n
  exact Nat.clog_mono_right 2 hfind

omit [DecidableEq κ] in
/-- The dyadic form, which is the usable one: `Nat.clog 2 (2 ^ m) = m`. -/
theorem ofFiniteVolumeBounds_exponent_le_of_lt_two_pow (F : FactorFamily E ι κ)
    (ob ib : ENNReal)
    (houter : ∀ j ∈ F.outerSet, volume (F.outerBody j).carrier ≤ ob)
    (hinner : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j, ib ≤ volume (F.innerBody i).carrier)
    (hobTop : ob ≠ ∞) (hibPos : 0 < ib) (hibTop : ib ≠ ∞)
    {m : ℕ} (hm : ob < 2 ^ m * ib) :
    (OuterInnerVolumeRatio.ofFiniteVolumeBounds F ob ib houter hinner hobTop hibPos
        hibTop).exponent ≤ m := by
  have hdiv : ob / ib < ((2 ^ m : ℕ) : ENNReal) := by
    rw [ENNReal.div_lt_iff (Or.inl hibPos.ne') (Or.inl hibTop)]
    push_cast
    exact hm
  have h := ofFiniteVolumeBounds_exponent_le F ob ib houter hinner hobTop hibPos hibTop hdiv
  rwa [Nat.clog_pow 2 m (by norm_num : 1 < 2)] at h

/-! ### The dyadic ingredients, all in `ℝ≥0∞` -/

/-- `1 ≤ 2 ^ k * δ` at `k = Nat.log 2 ⌈δ⁻¹⌉₊ + 1`. -/
theorem one_le_two_pow_mul {δ : ℝ≥0} (hδ0 : 0 < δ) :
    (1 : ℝ≥0) ≤ 2 ^ (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1) * δ := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hceil : ((δ : ℝ))⁻¹ ≤ (⌈((δ : ℝ))⁻¹⌉₊ : ℝ) := Nat.le_ceil _
  have hlt : (⌈((δ : ℝ))⁻¹⌉₊ : ℕ) < 2 ^ (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hltR : (⌈((δ : ℝ))⁻¹⌉₊ : ℝ) < (2 : ℝ) ^ (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1) := by
    exact_mod_cast hlt
  have hkey : (1 : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1) * (δ : ℝ) := by
    have h1 : ((δ : ℝ))⁻¹ < (2 : ℝ) ^ (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1) :=
      lt_of_le_of_lt hceil hltR
    have h2 := mul_lt_mul_of_pos_left h1 hδR
    rw [mul_inv_cancel₀ hδR.ne'] at h2
    rw [mul_comm]
    exact h2.le
  have hcoe : ((1 : ℝ≥0) : ℝ) ≤ ((2 ^ (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1) * δ : ℝ≥0) : ℝ) := by
    push_cast
    exact hkey
  exact_mod_cast hcoe

/-- A finite quantity is dominated by a dyadic multiple of any positive finite one. -/
theorem exists_le_two_pow_mul {V C : ENNReal} (hVtop : V ≠ ⊤) (hC0 : C ≠ 0)
    (hCtop : C ≠ ⊤) :
    ∃ j : ℕ, V ≤ 2 ^ j * C := by
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hVtop hC0)
  refine ⟨n, ?_⟩
  have hVn : V ≤ (n : ENNReal) * C := by
    rw [← ENNReal.div_le_iff_le_mul (Or.inl hC0) (Or.inl hCtop)]
    exact hn.le
  refine hVn.trans (mul_le_mul_left ?_ C)
  calc (n : ENNReal) ≤ ((2 ^ n : ℕ) : ENNReal) := by
        exact_mod_cast Nat.le_of_lt_succ (Nat.lt_succ_of_lt (Nat.lt_two_pow_self))
    _ = 2 ^ n := by push_cast; ring

/-- **The dyadic bound at `m = 3k + j + 1`**, with no real analysis. -/
theorem lt_two_pow_mul_of_le {V C : ENNReal} (hV0 : V ≠ 0) (hVtop : V ≠ ⊤)
    {j : ℕ} (hj : V ≤ 2 ^ j * C) {k : ℕ} {δ : ℝ≥0} (hk : (1 : ℝ≥0) ≤ 2 ^ k * δ) :
    V < 2 ^ (3 * k + j + 1) * (C * (δ : ENNReal) ^ 3) := by
  have hkE : (1 : ENNReal) ≤ ((2 : ENNReal) ^ k) * (δ : ENNReal) := by
    have hc : ((1 : ℝ≥0) : ENNReal) ≤ ((2 ^ k * δ : ℝ≥0) : ENNReal) := by exact_mod_cast hk
    simpa [ENNReal.coe_mul] using hc
  have hcube : (1 : ENNReal) ≤ ((2 : ENNReal) ^ (3 * k)) * (δ : ENNReal) ^ 3 := by
    have h3 := pow_le_pow_left' hkE 3
    calc (1 : ENNReal) = 1 ^ 3 := by norm_num
      _ ≤ (((2 : ENNReal) ^ k) * (δ : ENNReal)) ^ 3 := h3
      _ = ((2 : ENNReal) ^ (3 * k)) * (δ : ENNReal) ^ 3 := by
          rw [mul_pow, ← pow_mul]
          congr 2
          ring
  have hrearr : (2 : ENNReal) ^ (3 * k + j + 1) * (C * (δ : ENNReal) ^ 3)
      = 2 * (2 ^ j * C) * ((2 : ENNReal) ^ (3 * k) * (δ : ENNReal) ^ 3) := by
    rw [pow_add, pow_add]
    ring
  rw [hrearr]
  calc V < 2 * V := by
        rw [two_mul]
        exact ENNReal.lt_add_right hVtop hV0
    _ ≤ 2 * (2 ^ j * C) := by gcongr
    _ = 2 * (2 ^ j * C) * 1 := by rw [mul_one]
    _ ≤ 2 * (2 ^ j * C) * ((2 : ENNReal) ^ (3 * k) * (δ : ENNReal) ^ 3) := by gcongr

/-! ### The Part-(B) instantiation: the missing `fineVolumeRatio_exponent_spec` -/

section PartB

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib CF C₀ : ℝ≥0}

/-- The single `δ`-free dyadic offset of the Part-(B) volume ratio: `|B(0,4)| ≤ 2 ^ j · c₃`. -/
theorem exists_partB_volumeRatio_offset :
    ∃ j : ℕ, volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (plankWindowRadius : ℝ))
      ≤ 2 ^ j * ((Metric.lt_volume_convexHull.c 3 : ℝ≥0) : ENNReal) := by
  refine exists_le_two_pow_mul (measure_closedBall_lt_top).ne ?_ ENNReal.coe_ne_top
  exact ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos 3).ne'


/-- **The Part-(B) volume-ratio exponent is logarithmic in `1 / δ`, explicitly.** -/
theorem fineVolumeRatio_exponent_le_log
    (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)
    (hδ0 : 0 < δ)
    (hball : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1)
    {j : ℕ}
    (hj : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (plankWindowRadius : ℝ))
      ≤ 2 ^ j * ((Metric.lt_volume_convexHull.c 3 : ℝ≥0) : ENNReal)) :
    (D.fineVolumeRatio hδ0 hball).exponent
      ≤ 3 * (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1) + j + 1 := by
  have hV0 : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3))
      (plankWindowRadius : ℝ)) ≠ 0 := by
    refine (Metric.measure_closedBall_pos volume _ ?_).ne'
    have hpos : (0 : ℝ≥0) < plankWindowRadius := by
      rw [plankWindowRadius]; norm_num
    exact_mod_cast hpos
  have hlt := lt_two_pow_mul_of_le (V := volume (Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin 3)) (plankWindowRadius : ℝ)))
    (C := ((Metric.lt_volume_convexHull.c 3 : ℝ≥0) : ENNReal))
    hV0 (measure_closedBall_lt_top).ne hj (one_le_two_pow_mul hδ0)
  unfold Kakeya.Section6PartBData.fineVolumeRatio
  exact ofFiniteVolumeBounds_exponent_le_of_lt_two_pow _ _ _ _ _ _ _ _ hlt

/-- **`fineVolumeRatio_exponent_spec`: the statement `Section6PartBProp51Input.lean` asserts in prose,
now proved.**

That file's docstring for `Kakeya.Section6PartBData.fineVolumeRatio` says the exponent

> *"is **logarithmic** in `1/δ`, which is what
> `Kakeya.Section6PartBData.fineVolumeRatio_exponent_spec` records."*

No such declaration existed.  It could not have: the exponent was opaque to every `module` file until
`ShadedBody.OuterInnerVolumeRatio.ofFiniteVolumeBounds` was exposed.  This is that
statement, with `j` the single `δ`-free dyadic offset of
`Kakeya.PartBLoss.exists_partB_volumeRatio_offset`.  The prose claim in
`Section6PartBProp51Input.lean` should now cite this. -/
theorem fineVolumeRatio_exponent_spec
    (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)
    (hδ0 : 0 < δ)
    (hball : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1) :
    ∃ j : ℕ, (D.fineVolumeRatio hδ0 hball).exponent
      ≤ 3 * (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1) + j + 1 := by
  obtain ⟨j, hj⟩ := exists_partB_volumeRatio_offset
  exact ⟨j, fineVolumeRatio_exponent_le_log D hδ0 hball hj⟩

end PartB

/-! ### Absorbing the logarithmic exponent -/

/-- `⌈δ⁻¹⌉₊ ≤ (1 / δ) ^ 2` for `0 < δ ≤ 1 / 2`. -/
theorem ceil_inv_le_sq {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    (⌈δ⁻¹⌉₊ : ℝ) ≤ (1 / δ) ^ 2 := by
  have h1 : (⌈δ⁻¹⌉₊ : ℝ) ≤ δ⁻¹ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hkey : δ⁻¹ + 1 ≤ (1 / δ) ^ 2 := by
    have hd2 : (0 : ℝ) < δ ^ 2 := by positivity
    rw [div_pow, one_pow, le_div_iff₀ hd2]
    have hexp : (δ⁻¹ + 1) * δ ^ 2 = δ + δ ^ 2 := by
      field_simp
    rw [hexp]
    nlinarith [hδ0, hδ]
  linarith

/-- **The explicit logarithmic exponent bound absorbs into any negative power of `δ`.** -/
theorem exists_threshold_log_offset_le_rpow_neg {η : ℝ} (hη : 0 < η) (j : ℕ) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ →
      ((3 * (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1) + j + 1 + 1 : ℕ) : ENNReal)
        ≤ (δ : ENNReal) ^ (-η) := by
  have hη2 : (0 : ℝ) < η / 2 := by positivity
  set K : ℝ≥0 := (3 : ℝ≥0) + (j : ℝ≥0) + 2 with hK
  have hK1 : (1 : ENNReal) ≤ (K : ENNReal) := by
    have hk : (1 : ℝ≥0) ≤ K := by
      dsimp [K]
      calc (1 : ℝ≥0) ≤ 3 := by norm_num
        _ ≤ 3 + (j : ℝ≥0) := le_self_add
        _ ≤ 3 + (j : ℝ≥0) + 2 := le_self_add
    exact_mod_cast hk
  obtain ⟨u₁, hu₁, h₁⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (ShadedBody.eventually_const_le_coe_rpow_neg hK1 ENNReal.coe_ne_top hη2)
  obtain ⟨u₂, hu₂, h₂⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg hη2 3)
  refine ⟨min (min u₁ u₂) (1 / 2), lt_min (lt_min hu₁ hu₂) (by norm_num), ?_⟩
  intro δ hδ0 hδ
  have hδ1 := h₁ ⟨hδ0, hδ.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hδ2 := h₂ ⟨hδ0, hδ.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hhalf : δ ≤ 1 / 2 := hδ.trans (min_le_right _ _)
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hhalfR : (δ : ℝ) ≤ 1 / 2 := by
    have := hhalf
    rw [← NNReal.coe_le_coe] at this
    push_cast at this
    exact this
  have h2inv : (2 : ℝ) ≤ 1 / (δ : ℝ) := by
    rw [le_div_iff₀ hδR]; linarith
  -- the logarithmic core, from A7f's Bernoulli bound at m = 2
  have hcore : ((Kakeya.dyadicPigeonholeNatConstant ⌈((δ : ℝ))⁻¹⌉₊ : ℕ) : ℝ)
      ≤ (1 + Real.logb 2 (1 / (δ : ℝ))) ^ 3 :=
    Kakeya.Section6PartBData.dyadicPigeonholeNatConstant_le_pow_one_add_logb h2inv
      (by simpa using ceil_inv_le_sq hδR hhalfR)
  have hL : (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1 : ℕ) = Kakeya.dyadicPigeonholeNatConstant
      ⌈((δ : ℝ))⁻¹⌉₊ := rfl
  have hbase : (1 : ℝ) ≤ 1 + Real.logb 2 (1 / (δ : ℝ)) := by
    have : (0 : ℝ) ≤ Real.logb 2 (1 / (δ : ℝ)) :=
      Real.logb_nonneg (by norm_num) (by linarith)
    linarith
  have hpow1 : (1 : ℝ) ≤ (1 + Real.logb 2 (1 / (δ : ℝ))) ^ 3 := one_le_pow₀ hbase
  -- collect over ℝ
  have hreal : ((3 * (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1) + j + 1 + 1 : ℕ) : ℝ)
      ≤ ((K : ℝ≥0) : ℝ) * (1 + Real.logb 2 (1 / (δ : ℝ))) ^ 3 := by
    have hc : (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ : ℝ) + 1
        ≤ (1 + Real.logb 2 (1 / (δ : ℝ))) ^ 3 := by
      have h := hcore
      rw [← hL] at h
      push_cast at h
      exact h
    have hKR : ((K : ℝ≥0) : ℝ) = 3 + (j : ℝ) + 2 := by
      dsimp [K]; push_cast; ring
    rw [hKR]
    push_cast
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hjP : (j : ℝ) ≤ (j : ℝ) * (1 + Real.logb 2 (1 / (δ : ℝ))) ^ 3 := by
      nlinarith [hpow1, hj0]
    nlinarith [hc, hpow1, hjP, hj0]
  calc ((3 * (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1) + j + 1 + 1 : ℕ) : ENNReal)
      = ENNReal.ofReal ((3 * (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1) + j + 1 + 1 : ℕ) : ℝ) := by
        rw [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (((K : ℝ≥0) : ℝ) * (1 + Real.logb 2 (1 / (δ : ℝ))) ^ 3) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = (K : ENNReal) * (ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ)))) ^ 3 := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 1 + Real.logb 2 (1 / (δ : ℝ)))]
    _ ≤ (δ : ENNReal) ^ (-(η / 2)) * (δ : ENNReal) ^ (-(η / 2)) :=
        mul_le_mul' hδ1.2.2 hδ2
    _ = (δ : ENNReal) ^ (-η) := by
        rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hδ0.ne') ENNReal.coe_ne_top]
        congr 1
        ring


/-! ### The `N`-hypothesis of the fullness-constant absorption, supplied -/

/-- **The volume-ratio exponent of the Part-(B) Proposition-5.1 input is sub-polynomial.**

This is exactly the `N`-hypothesis of
`Kakeya.PartBLoss.exists_threshold_rpow_le_fullnessConstant`
(`Kakeya/DimensionThree/Plank/PartBLossAbsorption.lean`): for every tolerance `η > 0` there is a
threshold below which `N + 1 ≤ δ ^ (-η)`.  The threshold depends only on `η` and on the single
`δ`-free offset `j`, so it is fixed before the configuration — which is what the consumer needs, and
which is why the offset had to be pulled out of the `δ`-dependent part first. -/
theorem exists_threshold_fineVolumeRatio_exponent_succ_le_rpow_neg {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
        {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
        {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0}
        {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {m Cfib CF C₀ : ℝ≥0}
        (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)
        (hδ0 : 0 < δ)
        (hball : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ Metric.closedBall 0 1),
        δ ≤ δ₀ →
        (((D.fineVolumeRatio hδ0 hball).exponent + 1 : ℕ) : ENNReal)
          ≤ (δ : ENNReal) ^ (-η) := by
  obtain ⟨j, hj⟩ := exists_partB_volumeRatio_offset
  obtain ⟨δ₀, hδ₀, habs⟩ := exists_threshold_log_offset_le_rpow_neg hη j
  refine ⟨δ₀, hδ₀, ?_⟩
  intro a b hab hb1 ι q δ T κ coarseSet ρ R m Cfib CF C₀ D hδ0 hball hδ
  have hN := fineVolumeRatio_exponent_le_log D hδ0 hball hj
  have hstep : ((D.fineVolumeRatio hδ0 hball).exponent + 1 : ℕ)
      ≤ (3 * (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1) + j + 1 + 1 : ℕ) := by omega
  calc (((D.fineVolumeRatio hδ0 hball).exponent + 1 : ℕ) : ENNReal)
      ≤ ((3 * (Nat.log 2 ⌈((δ : ℝ))⁻¹⌉₊ + 1) + j + 1 + 1 : ℕ) : ENNReal) := by
        exact_mod_cast hstep
    _ ≤ (δ : ENNReal) ^ (-η) := habs δ hδ0 hδ

/-! ### The `M`-hypothesis of the fullness-constant absorption, supplied -/

/-- **The cardinality hypothesis `M ≤ δ ^ (-7)` of
`Kakeya.PartBLoss.exists_threshold_rpow_le_fullnessConstant`, from the two hypotheses the 6.6(B)
chain already carries.**

`Tube.card_le_of_EssDistinct` bounds a pairwise essentially distinct family of `δ`-tubes in the unit
ball by `C₃ · (1/δ) ^ 6` — the exponent is `2n = 6`, not `4`; that correction is f's and this is
its third independent confirmation.  So the `-7` the pipeline envelope asks for has a whole factor
`1/δ` of slack, which is what absorbs the constant `C₃` below the threshold `δ ≤ 1/C₃`.

`M` is quantified with only `M ≤ q.card`, because the consumer's `M` is the cardinality of the
*scale-selected* subfamily of `q`; a subfamily bound is all that is needed and it keeps this lemma
independent of the selection API. -/
theorem exists_threshold_card_le_rpow_neg_seven :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0}, 0 < δ → δ ≤ δ₀ →
      ∀ (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      (∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ Metric.closedBall 0 1) →
      (q : Set ι).Pairwise (fun i j =>
        _root_.IsEssentiallyDistinct ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
      ∀ M : ℕ, M ≤ q.card → (M : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) := by
  have hC3 : (0 : ℝ) < Tube.card_le_of_EssDistinct.C 3 := Tube.card_le_of_EssDistinct.C_pos
  refine ⟨min 1 (Real.toNNReal (Tube.card_le_of_EssDistinct.C 3))⁻¹,
    lt_min one_pos (inv_pos.mpr (Real.toNNReal_pos.mpr hC3)), ?_⟩
  intro ι q δ hδ0 hδ T hball hED M hM
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδ1 : δ ≤ 1 := hδ.trans (min_le_left _ _)
  have hδC : δ ≤ (Real.toNNReal (Tube.card_le_of_EssDistinct.C 3))⁻¹ :=
    hδ.trans (min_le_right _ _)
  -- `C₃ ≤ 1 / δ`
  have hCδ : Tube.card_le_of_EssDistinct.C 3 ≤ 1 / (δ : ℝ) := by
    have hpos : (0 : ℝ≥0) < Real.toNNReal (Tube.card_le_of_EssDistinct.C 3) :=
      Real.toNNReal_pos.mpr hC3
    have hstep : δ * Real.toNNReal (Tube.card_le_of_EssDistinct.C 3) ≤ 1 := by
      calc δ * Real.toNNReal (Tube.card_le_of_EssDistinct.C 3)
          ≤ (Real.toNNReal (Tube.card_le_of_EssDistinct.C 3))⁻¹
              * Real.toNNReal (Tube.card_le_of_EssDistinct.C 3) := by
            gcongr
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
    have hstepR : (δ : ℝ) * Tube.card_le_of_EssDistinct.C 3 ≤ 1 := by
      have := (NNReal.coe_le_coe.mpr hstep)
      push_cast at this
      rwa [Real.coe_toNNReal _ hC3.le] at this
    rw [le_div_iff₀ hδR]
    linarith [hstepR]
  -- the count
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hraw := Tube.card_le_of_EssDistinct (E := EuclideanSpace ℝ (Fin 3)) hδ0 1 q
    (fun i => (T i).toTube) (by simpa using hball) (by simpa using hED)
  rw [hfr] at hraw
  have hMq : (M : ℝ) ≤ (q.card : ℝ) := by exact_mod_cast hM
  have hinv6 : (0 : ℝ) < (1 / (δ : ℝ)) ^ (2 * 3) := by positivity
  have hchain : (M : ℝ) ≤ (1 / (δ : ℝ)) ^ (7 : ℕ) := by
    calc (M : ℝ) ≤ (q.card : ℝ) := hMq
      _ ≤ Tube.card_le_of_EssDistinct.C 3 * (1 / (δ : ℝ)) ^ (2 * 3) := hraw
      _ ≤ (1 / (δ : ℝ)) * (1 / (δ : ℝ)) ^ (2 * 3) := by
          exact mul_le_mul_of_nonneg_right hCδ hinv6.le
      _ = (1 / (δ : ℝ)) ^ (7 : ℕ) := by ring
  have hrpow : (δ : ℝ) ^ (-(7 : ℝ)) = (1 / (δ : ℝ)) ^ (7 : ℕ) := by
    rw [Real.rpow_neg hδR.le, show ((7 : ℝ)) = ((7 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div, ← inv_pow]
  rw [hrpow]
  exact hchain

end PartBLoss

end Kakeya

end

end
