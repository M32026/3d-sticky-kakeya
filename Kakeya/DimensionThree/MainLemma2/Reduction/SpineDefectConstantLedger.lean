/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.GridUniformBand
public import Kakeya.MultiScaleLoss
public import Kakeya.MultiScaleFac.Homogenize
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectPotential

/-!
# `T-D6` — the constant ledger of the defect descent

 raises the item that decides the architecture of the defect route.
Every restriction of a `Kakeya.MultiScaleFac.GridUniform` in this tree **squares** the uniformity
constant:

```
 uniformTubeSetCuOf C   = max C (overlapConstBOTight n)
 bandRestrictConst C A  = max (uniformTubeSetCuOf C) (max A 1)
 gridUniformBandConst C A = (bandRestrictConst C A) ^ 2
```

and both ways of restricting carry it — `exists_homogenizing_pass_gridUniform` returns
`GridUniform t' T Mg (gridUniformBandConst C 2)`, and `exists_gridUniform_restrict_band` returns
`GridUniform t' T N (gridUniformBandConst C A)`.  So a descent that re-entered the uniformiser once
per trial would accumulate `C ^ (2 ^ n)` after `n` trials, with `n = Pmax h δ`.

This file **compiles that ledger, with its firing controls, and settles the question**:

* `reentryConst_one`, `reentryConst_two` — the firing controls  asks for: one
  re-entry gives `gridUniformBandConst Cu 2`, two give its square.  Both are `rfl`, so the ledger is
  provably measuring the tree's own constant and not a paraphrase of it.
* `gridUniformBandConst_eq_sq`, `reentryConst_eq_pow` — above the absolute floor the band constant
  *is* the square, hence `reentryConst C n = C ^ 2 ^ n`.
* `exists_lt_reentryConst_of_le` — the ledger exceeds **every** `δ`-free ceiling.
* `exists_threshold_le_ssfGridLen`, `exists_threshold_le_Pmax` — the number of trials is unbounded
  as `δ → 0`, because `Tube.ssfGridLen δ = ⌈log log (1/δ)⌉₊` is.
* **`not_reentry_le_of_le` — the verdict.**  For every `δ`-free `Cu₀` there is a threshold below
  which `Cu₀ < reentryConst Cu (Pmax h δ)`.  A descent that re-enters the uniformiser per trial
  therefore has **no** `δ`-free uniformity ceiling, and the existing block's binder
  `∀ Cu₀ : NNReal, ∀ᶠ (δ : NNReal) in 𝓝[>] 0, … → Cu ≤ Cu₀` — in which `Cu₀` is quantified *before*
  `δ` — cannot be met.  This is outcome (b) of `T-D6`.

* **The positive half, and the whole point of condition `C-D1`:**
  `Tube.UniformTubeSet.restrictOccupied` — restricting a hierarchy to a subfamily `S ⊆ u`, on the
  nodes `S` **occupies**, needs **no new constant at all**.  The nodes, the assignment, the nesting
  and the injectivity are the ambient ones; bounded overlap is monotone in both the index set and
  the family; and the *only* debt is Definition 2.1(iii)'s two halves on the restricted classes,
  named `Kakeya.ML2Core.IsClassHomogeneousOn`, which is a genuine homogeneity statement and not a
  constant.  **The ambient reading of that clause is unusable** — asked at every node of `𝒰` it
  forces `S = ∅` (`Kakeya.ML2Core.eq_empty_of_ambient_class_band`), which is why the index set
  shrinks to `S.image (𝒰.cover.assign k)`.  So the source's *"the retained family inherits the same
  tower"* (l.4104–4108) is available in the tree, at the price of one clause, and the doubly
  exponential ledger above is **avoidable** — provided the descent never calls the uniformiser
  again.

`Kakeya.ML2Core.pairProfile`'s footprint design is what makes the one-hierarchy reading usable: the
potential is stated on containment, so it never mentions the classes that `le_card_class` is about.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

/-! ## The ledger of a per-trial re-entry -/

section Ledger

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- **The uniformity constant after `n` re-entries of the homogenizing pass.**

`Kakeya.MultiScaleFac.exists_homogenizing_pass_gridUniform` takes a `GridUniform` at constant `C`
and returns one at `gridUniformBandConst C 2`; this is the composite over `n` trials. -/
noncomputable def reentryConst (C : NNReal) : ℕ → NNReal
  | 0 => C
  | n + 1 => Kakeya.MultiScaleFac.gridUniformBandConst (E := E) (reentryConst C n) 2

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **`T-D6` firing control, one re-entry.**  If this is not the tree's own constant, the ledger is
measuring the wrong thing. -/
theorem reentryConst_one (C : NNReal) :
    reentryConst (E := E) C 1 = Kakeya.MultiScaleFac.gridUniformBandConst (E := E) C 2 := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **`T-D6` firing control, two re-entries.**  The ledger sees the second application, applied to
the first — the squaring  names. -/
theorem reentryConst_two (C : NNReal) :
    reentryConst (E := E) C 2 = Kakeya.MultiScaleFac.gridUniformBandConst (E := E)
      (Kakeya.MultiScaleFac.gridUniformBandConst (E := E) C 2) 2 := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Above the absolute floor — the tight-net multiplicity and the band ratio `2` — the band
constant **is** the square. -/
theorem gridUniformBandConst_eq_sq {C : NNReal}
    (hB : ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) ≤ C) (h2 : 2 ≤ C) :
    Kakeya.MultiScaleFac.gridUniformBandConst (E := E) C 2 = C ^ 2 := by
  have hcu : Kakeya.MultiScaleFac.uniformTubeSetCuOf (E := E) C = C := max_eq_left hB
  have hmax : max (2 : NNReal) 1 = 2 := max_eq_left one_le_two
  rw [Kakeya.MultiScaleFac.gridUniformBandConst, Kakeya.MultiScaleFac.bandRestrictConst, hcu, hmax,
    max_eq_left h2]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The floor is stable under a re-entry: the constant only grows. -/
theorem le_gridUniformBandConst_self {C : NNReal} (h1 : 1 ≤ C) :
    C ≤ Kakeya.MultiScaleFac.gridUniformBandConst (E := E) C 2 := by
  have hle : C ≤ Kakeya.MultiScaleFac.bandRestrictConst (E := E) C 2 :=
    le_max_of_le_left (le_max_left _ _)
  calc C = C ^ 1 := (pow_one C).symm
    _ ≤ C ^ 2 := pow_le_pow_right₀ h1 one_le_two
    _ ≤ (Kakeya.MultiScaleFac.bandRestrictConst (E := E) C 2) ^ 2 := pow_le_pow_left' hle 2
    _ = Kakeya.MultiScaleFac.gridUniformBandConst (E := E) C 2 := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The ledger in closed form: `C ^ 2 ^ n`, doubly exponential in the number of trials.** -/
theorem reentryConst_eq_pow {C : NNReal}
    (hB : ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) ≤ C) (h2 : 2 ≤ C) :
    ∀ n : ℕ, reentryConst (E := E) C n = C ^ (2 ^ n) := by
  intro n
  induction n with
  | zero => simp [reentryConst]
  | succ n ih =>
    have hBn : ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal)
        ≤ reentryConst (E := E) C n := by
      rw [ih]
      calc ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) ≤ C := hB
        _ = C ^ 1 := (pow_one C).symm
        _ ≤ C ^ (2 ^ n) := pow_le_pow_right₀ (le_trans one_le_two h2) (Nat.one_le_two_pow)
    have h2n : (2 : NNReal) ≤ reentryConst (E := E) C n := by
      rw [ih]
      calc (2 : NNReal) ≤ C := h2
        _ = C ^ 1 := (pow_one C).symm
        _ ≤ C ^ (2 ^ n) := pow_le_pow_right₀ (le_trans one_le_two h2) (Nat.one_le_two_pow)
    have hstep : reentryConst (E := E) C (n + 1)
        = Kakeya.MultiScaleFac.gridUniformBandConst (E := E) (reentryConst (E := E) C n) 2 := rfl
    rw [hstep, gridUniformBandConst_eq_sq hBn h2n, ih, ← pow_mul, pow_succ]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The ledger exceeds every `δ`-free ceiling.**  This is the half of `T-D6` that decides the
architecture: no `Cu₀ : NNReal` chosen before `δ` can bound the constant after enough trials. -/
theorem exists_lt_reentryConst_of_le {C : NNReal}
    (hB : ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) ≤ C) (h2 : 2 ≤ C)
    (Cu₀ : NNReal) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Cu₀ < reentryConst (E := E) C n := by
  have h1C : (1 : NNReal) < C := lt_of_lt_of_le one_lt_two h2
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt Cu₀ h1C
  refine ⟨m, fun n hn => ?_⟩
  rw [reentryConst_eq_pow hB h2 n]
  refine lt_of_lt_of_le hm (pow_le_pow_right₀ (le_of_lt h1C) ?_)
  exact le_trans hn Nat.lt_two_pow_self.le

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The explicit squaring, as  demands it**: two re-entries give the square of
one.  If this ever stops compiling, the ledger has drifted off the tree's own constant. -/
theorem reentryConst_two_eq_sq {C : NNReal}
    (hB : ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) ≤ C) (h2 : 2 ≤ C) :
    reentryConst (E := E) C 2 = (reentryConst (E := E) C 1) ^ 2 := by
  rw [reentryConst_eq_pow hB h2 2, reentryConst_eq_pow hB h2 1, ← pow_mul]
  norm_num

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The ledger composes: `n + m` re-entries are `m` re-entries starting from the constant after
`n`. -/
theorem reentryConst_add (C : NNReal) (n : ℕ) :
    ∀ m : ℕ, reentryConst (E := E) C (n + m)
      = reentryConst (E := E) (reentryConst (E := E) C n) m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    have hL : reentryConst (E := E) C (n + (m + 1))
        = Kakeya.MultiScaleFac.gridUniformBandConst (E := E)
            (reentryConst (E := E) C (n + m)) 2 := rfl
    have hR : reentryConst (E := E) (reentryConst (E := E) C n) (m + 1)
        = Kakeya.MultiScaleFac.gridUniformBandConst (E := E)
            (reentryConst (E := E) (reentryConst (E := E) C n) m) 2 := rfl
    rw [hL, hR, ih]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **One re-entry already saturates the floor**, whatever the starting constant: the tree's own
`gridUniformBandConst` bumps `C` above both the tight-net multiplicity and the band ratio.  This is
what makes the verdict below unconditional, and therefore not vacuous. -/
theorem floor_le_reentryConst_one (C : NNReal) :
    ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) ≤ reentryConst (E := E) C 1 ∧
      2 ≤ reentryConst (E := E) C 1 := by
  have hB1 : ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal)
      ≤ Kakeya.MultiScaleFac.bandRestrictConst (E := E) C 2 :=
    le_max_of_le_left (le_max_right _ _)
  have h21 : (2 : NNReal) ≤ Kakeya.MultiScaleFac.bandRestrictConst (E := E) C 2 :=
    le_max_of_le_right (le_max_left _ _)
  have hsq : Kakeya.MultiScaleFac.bandRestrictConst (E := E) C 2
      ≤ (Kakeya.MultiScaleFac.bandRestrictConst (E := E) C 2) ^ 2 := by
    calc Kakeya.MultiScaleFac.bandRestrictConst (E := E) C 2
        = (Kakeya.MultiScaleFac.bandRestrictConst (E := E) C 2) ^ 1 := (pow_one _).symm
      _ ≤ (Kakeya.MultiScaleFac.bandRestrictConst (E := E) C 2) ^ 2 :=
          pow_le_pow_right₀ Kakeya.MultiScaleFac.one_le_bandRestrictConst one_le_two
  exact ⟨le_trans hB1 hsq, le_trans h21 hsq⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The ledger exceeds every `δ`-free ceiling, from *any* starting constant.** -/
theorem exists_lt_reentryConst (C Cu₀ : NNReal) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Cu₀ < reentryConst (E := E) C n := by
  obtain ⟨hB, h2⟩ := floor_le_reentryConst_one (E := E) C
  obtain ⟨n₁, hn₁⟩ := exists_lt_reentryConst_of_le (E := E) hB h2 Cu₀
  refine ⟨n₁ + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + m := ⟨n - 1, by omega⟩
  rw [reentryConst_add (E := E) C 1 m]
  exact hn₁ m (by omega)

end Ledger

/-! ## The number of trials is unbounded -/

section TrialCount

/-- `Tube.ssfGridLen δ = ⌈log log (1/δ)⌉₊` exceeds any given `M` below a threshold. -/
theorem exists_threshold_le_ssfGridLen (M : ℕ) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ → M ≤ Tube.ssfGridLen δ := by
  refine ⟨⟨Real.exp (-(Real.exp M)), (Real.exp_pos _).le⟩, ?_, ?_⟩
  · exact_mod_cast Real.exp_pos _
  intro δ hδ hle
  have hδR : (0 : ℝ) < (δ : ℝ) := hδ
  have hleR : (δ : ℝ) ≤ Real.exp (-(Real.exp (M : ℝ))) := hle
  have hmul : Real.exp (Real.exp (M : ℝ)) * (δ : ℝ) ≤ 1 := by
    calc Real.exp (Real.exp (M : ℝ)) * (δ : ℝ)
        ≤ Real.exp (Real.exp (M : ℝ)) * Real.exp (-(Real.exp (M : ℝ))) :=
          mul_le_mul_of_nonneg_left hleR (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hinv : Real.exp (Real.exp (M : ℝ)) ≤ 1 / (δ : ℝ) := (le_div_iff₀ hδR).mpr hmul
  have hlog1 : Real.exp (M : ℝ) ≤ Real.log (1 / (δ : ℝ)) := by
    have hx := Real.log_le_log (Real.exp_pos _) hinv
    rwa [Real.log_exp] at hx
  have hlog2 : (M : ℝ) ≤ Real.log (Real.log (1 / (δ : ℝ))) := by
    have hx := Real.log_le_log (Real.exp_pos _) hlog1
    rwa [Real.log_exp] at hx
  have hc := Nat.ceil_le_ceil hlog2
  rw [Nat.ceil_natCast] at hc
  exact hc

/-- The trial count `Pmax h δ` is unbounded as `δ → 0`. -/
theorem exists_threshold_le_Pmax {h : ℝ} (hh : 0 < h) (M : ℕ) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ → M ≤ Pmax h δ := by
  obtain ⟨δ₀, hδ₀, hM⟩ := exists_threshold_le_ssfGridLen (max M 1)
  refine ⟨δ₀, hδ₀, fun δ hδ hle => ?_⟩
  have hN := hM δ hδ hle
  have hN1 : 1 ≤ Tube.ssfGridLen δ := le_trans (le_max_right M 1) hN
  have hMN : M ≤ Tube.ssfGridLen δ := le_trans (le_max_left M 1) hN
  have hceil : 1 ≤ ⌈(4 : ℝ) / h⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
  have hhalf : Tube.ssfGridLen δ ≤ Tube.ssfGridLen δ * (Tube.ssfGridLen δ + 1) / 2 := by
    have : 2 * Tube.ssfGridLen δ ≤ Tube.ssfGridLen δ * (Tube.ssfGridLen δ + 1) := by nlinarith
    omega
  calc M ≤ Tube.ssfGridLen δ := hMN
    _ ≤ Tube.ssfGridLen δ * (Tube.ssfGridLen δ + 1) / 2 := hhalf
    _ ≤ (Tube.ssfGridLen δ * (Tube.ssfGridLen δ + 1) / 2) * ⌈(4 : ℝ) / h⌉₊ :=
        Nat.le_mul_of_pos_right _ hceil

end TrialCount

/-! ## The verdict -/

section Verdict

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **`T-D6`, outcome (b): a per-trial re-entry has no `δ`-free uniformity ceiling.**

For every `Cu₀ : NNReal` chosen *before* `δ` — which is exactly the quantifier order of the existing
block's binder `∀ Cu₀ : NNReal, ∀ᶠ (δ : NNReal) in 𝓝[>] 0, … → Cu ≤ Cu₀` — there is a threshold
below which the constant accumulated over the descent's own `Pmax h δ` trials already exceeds it.

Hence condition `C-D1`: the descent must run on **one** hierarchy, with only the family varying.
`Tube.UniformTubeSet.restrictOccupied` is what makes that possible. -/
theorem not_reentry_le_of_le {C : NNReal}
    (hB : ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) ≤ C) (h2 : 2 ≤ C)
    {h : ℝ} (hh : 0 < h) (Cu₀ : NNReal) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧
      ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ → Cu₀ < reentryConst (E := E) C (Pmax h δ) := by
  obtain ⟨n₀, hn₀⟩ := exists_lt_reentryConst_of_le (E := E) hB h2 Cu₀
  obtain ⟨δ₀, hδ₀, hP⟩ := exists_threshold_le_Pmax hh n₀
  exact ⟨δ₀, hδ₀, fun δ hδ hle => hn₀ _ (hP δ hδ hle)⟩


omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **`T-D6`, outcome (b), unconditional.**  No hypothesis on the starting constant at all: for
every `Cu : NNReal` and every `Cu₀ : NNReal` chosen before `δ`, the constant accumulated over the
descent's own `Pmax h δ` re-entries eventually exceeds `Cu₀`.

This is the statement that decides the architecture.  A defect descent that re-enters
`Kakeya.MultiScaleFac.exists_homogenizing_pass_gridUniform` (or
`Kakeya.MultiScaleFac.exists_gridUniform_restrict_band`) once per trial **cannot** satisfy the
existing block's binder `∀ Cu₀ : NNReal, ∀ᶠ (δ : NNReal) in 𝓝[>] 0, … → Cu ≤ Cu₀`, in which `Cu₀` is
quantified before `δ`. -/
theorem not_reentry_le (C : NNReal) {h : ℝ} (hh : 0 < h) (Cu₀ : NNReal) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧
      ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ → Cu₀ < reentryConst (E := E) C (Pmax h δ) := by
  obtain ⟨n₀, hn₀⟩ := exists_lt_reentryConst (E := E) C Cu₀
  obtain ⟨δ₀, hδ₀, hP⟩ := exists_threshold_le_Pmax hh n₀
  exact ⟨δ₀, hδ₀, fun δ hδ hle => hn₀ _ (hP δ hδ hle)⟩

end Verdict

/-! ## The positive half: one hierarchy, one constant -/

section OneHierarchy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}

open scoped Classical in
/-- **GWZ Definition 2.1(iii) on a retained subfamily** — the source's *"the retained family
inherits the same tower … pairwise within a factor two at each fixed level or pair of levels"*
(l.4104-4108), in the tree's class vocabulary and at the ambient constant `Cu`.

Quantified over the nodes `S` **occupies**, `S.image (𝒰.cover.assign k)`, and not over the ambient
`𝒰.cover.indexSet k`: a node of the ambient hierarchy that `S` misses has an empty `S`-class, and a
two-sided band asked there forces `bN k = 0` and hence `S = ∅`
(`Kakeya.ML2Core.eq_empty_of_ambient_class_band`).  Occupancy is the restriction the source performs
when it says the retained family inherits the tower. -/
def IsClassHomogeneousOn {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (S : Finset ι) : Prop :=
  ∃ bN : ℕ → NNReal, ∀ k ≤ Tube.ssfGridLen δ,
    ∀ j ∈ S.image (𝒰.cover.assign k),
      ((Tube.coverClass S (𝒰.cover.assign k) j).card : NNReal) ≤ Cu * bN k ∧
        bN k ≤ Cu * ((Tube.coverClass S (𝒰.cover.assign k) j).card : NNReal)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The permanent record of why the band must be on the OCCUPIED nodes**.

Asked at *every ambient* node, the two-sided band is jointly unsatisfiable for every subfamily that
misses one node: the missed node's `S`-class is empty, so the lower half forces `bN k = 0`, the
upper half then empties **every** `S`-class, and `S` itself is empty.  That is exactly the class of
subfamily a mass-weighted dyadic selection produces, so the ambient reading is unusable and
`Tube.UniformTubeSet.restrictOccupied` below quantifies over `S.image (𝒰.cover.assign k)`. -/
theorem eq_empty_of_ambient_class_band (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    {S : Finset ι} (hS : S ⊆ u) (bN : ℕ → NNReal) {k : ℕ} (hk : k ≤ Tube.ssfGridLen δ)
    (hup : ∀ j ∈ 𝒰.cover.indexSet k,
      ((Tube.coverClass S (𝒰.cover.assign k) j).card : NNReal) ≤ Cu * bN k)
    (hlow : ∀ j ∈ 𝒰.cover.indexSet k,
      bN k ≤ Cu * ((Tube.coverClass S (𝒰.cover.assign k) j).card : NNReal))
    {j₀ : ι} (hj₀ : j₀ ∈ 𝒰.cover.indexSet k)
    (hmiss : Tube.coverClass S (𝒰.cover.assign k) j₀ = ∅) : S = ∅ := by
  classical
  have hbN : bN k = 0 := by
    have := hlow j₀ hj₀
    rw [hmiss] at this
    simpa using this
  refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
  have hji : 𝒰.cover.assign k i ∈ 𝒰.cover.indexSet k := 𝒰.cover.assign_mem k hk i (hS hi)
  have hcls : i ∈ Tube.coverClass S (𝒰.cover.assign k) (𝒰.cover.assign k i) := by
    simp [Tube.coverClass, hi]
  have hcard : ((Tube.coverClass S (𝒰.cover.assign k) (𝒰.cover.assign k i)).card : NNReal) ≤ 0 := by
    have := hup _ hji
    rwa [hbN, mul_zero] at this
  have : (Tube.coverClass S (𝒰.cover.assign k) (𝒰.cover.assign k i)).card = 0 := by
    exact_mod_cast le_antisymm (by exact_mod_cast hcard) (Nat.zero_le _)
  rw [Finset.card_eq_zero] at this
  simp [this] at hcls

open scoped Classical in
/-- **Restriction to a subfamily at the same constant, on the nodes the subfamily occupies.**

`C-D1` made usable.  The index set shrinks to `S.image (𝒰.cover.assign k)`; the nodes, the
assignment, the nesting and the injectivity are the ambient ones untouched; bounded overlap is
monotone in both the index set and the family; and Definition 2.1(iii)'s two halves are exactly
`Kakeya.ML2Core.IsClassHomogeneousOn`'s.  **No new constant anywhere** — contrast
`Kakeya.ML2Core.not_reentry_le`, where re-homogenizing through
`Kakeya.MultiScaleFac.exists_homogenizing_pass_gridUniform` costs `Cu ^ 2 ^ n` after `n` trials.

The occupied index set is the tree's own idiom: `exists_homogenizing_pass_gridUniform` already
returns `indexSet' k = t'.image (assign k)`. -/
noncomputable def _root_.Tube.UniformTubeSet.restrictOccupied
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) {S : Finset ι} (hS : S ⊆ u)
    (hhom : IsClassHomogeneousOn 𝒰 S) :
    Tube.UniformTubeSet S T (Tube.ssfGridLen δ) Cu where
  cover :=
    { indexSet := fun k => S.image (𝒰.cover.assign k)
      assign := 𝒰.cover.assign
      tube := 𝒰.cover.tube
      assign_mem := fun k _ i hi => Finset.mem_image_of_mem _ hi
      le_tube_assign := fun k hk i hi => 𝒰.cover.le_tube_assign k hk i (hS hi)
      nested := fun k hk i hi j hj => 𝒰.cover.nested k hk i (hS hi) j (hS hj)
      tube_nested := fun k hk i hi => 𝒰.cover.tube_nested k hk i (hS hi) }
  branchingN := hhom.choose
  tube_injOn := by
    intro k hk
    refine Set.InjOn.mono ?_ (𝒰.tube_injOn k hk)
    intro j hj
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    exact_mod_cast 𝒰.cover.assign_mem k hk i (hS hi)
  boundedOverlap := by
    classical
    intro k hk V
    refine le_trans ?_ (𝒰.boundedOverlap k hk V)
    have hsub : (S.image (𝒰.cover.assign k)).filter (fun j => ∃ i ∈ S,
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)
        ⊆ (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ u,
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_image] at hj ⊢
      obtain ⟨⟨i₀, hi₀, rfl⟩, i, hi, h1, h2⟩ := hj
      exact ⟨𝒰.cover.assign_mem k hk i₀ (hS hi₀), i, hS hi, h1, h2⟩
    exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsub)
  card_class_le := fun k hk j hj => (hhom.choose_spec k hk j hj).1
  le_card_class := fun k hk j hj => (hhom.choose_spec k hk j hj).2

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The restricted hierarchy has the **same nodes**, and its index sets only shrink — the two
clauses `Kakeya.ML2Core.pairProfile_mono_cover` consumes, in the step's own order. -/
theorem restrictOccupied_cover (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    {S : Finset ι} (hS : S ⊆ u) (hhom : IsClassHomogeneousOn 𝒰 S) :
    (∀ n ≤ Tube.ssfGridLen δ,
        (𝒰.restrictOccupied hS hhom).cover.indexSet n ⊆ 𝒰.cover.indexSet n) ∧
      (∀ n, (𝒰.restrictOccupied hS hhom).cover.tube n = 𝒰.cover.tube n) := by
  classical
  refine ⟨fun n hn j hj => ?_, fun n => by simp [Tube.UniformTubeSet.restrictOccupied]⟩
  simp only [Tube.UniformTubeSet.restrictOccupied, Finset.mem_image] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  exact 𝒰.cover.assign_mem n hn i (hS hi)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The ambient family is class-homogeneous on itself**, at its own branching profile — so the
clause is not vacuous and the descent's first trial discharges it for free. -/
theorem isClassHomogeneousOn_self (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) :
    IsClassHomogeneousOn 𝒰 u := by
  classical
  refine ⟨𝒰.branchingN, fun k hk j hj => ?_⟩
  have hj' : j ∈ 𝒰.cover.indexSet k := by
    simp only [Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    exact 𝒰.cover.assign_mem k hk i hi
  exact ⟨𝒰.card_class_le k hk j hj', 𝒰.le_card_class k hk j hj'⟩

end OneHierarchy

/-! ## `T-D5` — the loss ledger of the descent -/

section LossLedger

/-- `Φ_h`'s ceiling, plus the one extra power the induction pays, fits inside the *quadratic*
exponent `K(N+1)²` that `Kakeya.StickyKakeya.gridLoss` already carries — at a multiplier
`⌈4/h⌉₊ + 1` that is fixed **before** `δ`. -/
theorem potentialCeil_succ_le {h : ℝ} (D : ℝ) (δ : NNReal) :
    potentialCeil h D δ + 1 ≤ (⌈D / h⌉₊ + 1) * (Tube.ssfGridLen δ + 1) ^ 2 := by
  set N := Tube.ssfGridLen δ with hN
  have hhalf : N * (N + 1) / 2 ≤ (N + 1) ^ 2 := by
    have h1 : N * (N + 1) / 2 ≤ N * (N + 1) := Nat.div_le_self _ _
    nlinarith [Nat.le_add_left 0 N]
  calc potentialCeil h D δ + 1 = (N * (N + 1) / 2) * ⌈D / h⌉₊ + 1 := rfl
    _ ≤ (N + 1) ^ 2 * ⌈D / h⌉₊ + (N + 1) ^ 2 := by
        have : (N * (N + 1) / 2) * ⌈D / h⌉₊ ≤ (N + 1) ^ 2 * ⌈D / h⌉₊ :=
          Nat.mul_le_mul_right _ hhalf
        have h2 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos N)
        omega
    _ = (⌈D / h⌉₊ + 1) * (N + 1) ^ 2 := by ring

/-- **`T-D5`: the accumulated per-trial loss is absorbed.**

`Λ = (1 − log δ)^{K'}` is the shape of every per-trial loss in this tree (the source's
`Λ = (2 + log₂(1/δ))^K`).  Raised to the descent's own `P_max + 1`, it stays inside
`Kakeya.StickyKakeya.gridLoss 1 K''` at `K'' = K'·(⌈D/h⌉₊ + 1)` — a constant fixed **before** `δ` —
and `Kakeya.StickyKakeya.exists_threshold_gridLoss_le` absorbs it into any `δ^{-α}`.

**Firing control, and it is a typing fact rather than a proof-reading one.**
`exists_threshold_gridLoss_le` binds `K : ℕ` *before* `δ`, so a `δ`-dependent exponent — the
failure mode  asks to be excluded, e.g. `K′ · ssfGridLen δ` — cannot even be
written at that call.  What makes `K″` `δ`-free is
`Kakeya.ML2Core.potentialCeil_succ_le`: **all** of the `δ`-dependence of `P_max` is the
quadratic `(ssfGridLen δ + 1)²` that `gridLoss` already pays. -/
theorem exists_threshold_loss_pow_potentialCeil_le (K' : ℕ) {h : ℝ} (D α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
        ((1 - Real.log (δ : ℝ)) ^ K') ^ (potentialCeil h D δ + 1) ≤ (δ : ℝ) ^ (-α) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hgrid⟩ :=
    StickyKakeya.exists_threshold_gridLoss_le 1 le_rfl (K' * (⌈D / h⌉₊ + 1)) α hα
  refine ⟨δ₀, hδ₀, hδ₀1, fun {δ} hδ hδle => ?_⟩
  have hδ1 : δ ≤ 1 := hδle.trans hδ₀1
  have hW : (1 : ℝ) ≤ 1 - Real.log (δ : ℝ) := by
    have : Real.log (δ : ℝ) ≤ 0 := Real.log_nonpos (by positivity) (by exact_mod_cast hδ1)
    linarith
  have hexp : K' * (potentialCeil h D δ + 1)
      ≤ K' * (⌈D / h⌉₊ + 1) * (Tube.ssfGridLen δ + 1) ^ 2 := by
    have := potentialCeil_succ_le (h := h) D δ
    calc K' * (potentialCeil h D δ + 1)
        ≤ K' * ((⌈D / h⌉₊ + 1) * (Tube.ssfGridLen δ + 1) ^ 2) := Nat.mul_le_mul_left _ this
      _ = K' * (⌈D / h⌉₊ + 1) * (Tube.ssfGridLen δ + 1) ^ 2 := by ring
  calc ((1 - Real.log (δ : ℝ)) ^ K') ^ (potentialCeil h D δ + 1)
      = (1 - Real.log (δ : ℝ)) ^ (K' * (potentialCeil h D δ + 1)) := by rw [← pow_mul]
    _ ≤ (1 - Real.log (δ : ℝ)) ^ (K' * (⌈D / h⌉₊ + 1) * (Tube.ssfGridLen δ + 1) ^ 2) :=
        pow_le_pow_right₀ hW hexp
    _ = StickyKakeya.gridLoss 1 (K' * (⌈D / h⌉₊ + 1)) δ := by
        rw [StickyKakeya.gridLoss]
        simp
    _ ≤ (δ : ℝ) ^ (-α) := hgrid hδ hδle

/-- `T-D5` at the descent's own ceiling `Pmax = potentialCeil h 4 δ`. -/
theorem exists_threshold_loss_pow_Pmax_le (K' : ℕ) {h : ℝ} (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
        ((1 - Real.log (δ : ℝ)) ^ K') ^ (Pmax h δ + 1) ≤ (δ : ℝ) ^ (-α) :=
  exists_threshold_loss_pow_potentialCeil_le K' 4 α hα

end LossLedger

/-! ## The producer of `IsClassHomogeneousOn` -/

section ClassBandProducer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}

open scoped Classical in
omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The bridge from the existing dyadic class band to `Kakeya.ML2Core.IsClassHomogeneousOn`.**

`Kakeya.Homogenize.exists_classBand_pass_of_uniformTubeSet`
(`Kakeya/MultiScaleFac/Homogenize.lean`) returns, for a retained subfamily `S`, a dyadic profile
`cnt` with `2^{cnt a} ≤ #class ≤ 2·2^{cnt a}` on exactly the **occupied** nodes
`S.image (𝒰.cover.assign a)` — the same quantification `IsClassHomogeneousOn` uses, for the reason
`Kakeya.ML2Core.eq_empty_of_ambient_class_band` records.

Taking `bN := 2^{cnt}` turns it into `IsClassHomogeneousOn 𝒰 S` as soon as `2 ≤ Cu`: the upper half
is `#class ≤ 2·2^{cnt} ≤ Cu·2^{cnt}` and the lower is `2^{cnt} ≤ #class ≤ Cu·#class`.  So the band
comes at the source's **absolute constant `2`** — a loss, not a constant, exactly as
 specified the debt must be paid. -/
theorem isClassHomogeneousOn_of_classBand_pass
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (hCu : 2 ≤ Cu) {S : Finset ι}
    {cnt : ℕ → ℕ}
    (hband : ∀ a ≤ Tube.ssfGridLen δ, ∀ j ∈ S.image (𝒰.cover.assign a),
      2 ^ cnt a ≤ (Tube.coverClass S (𝒰.cover.assign a) j).card ∧
        (Tube.coverClass S (𝒰.cover.assign a) j).card ≤ 2 * 2 ^ cnt a) :
    IsClassHomogeneousOn 𝒰 S := by
  classical
  have hCu1 : (1 : NNReal) ≤ Cu := le_trans one_le_two hCu
  refine ⟨fun k => (2 : NNReal) ^ cnt k, fun k hk j hj => ?_⟩
  obtain ⟨hlow, hup⟩ := hband k hk j hj
  constructor
  · calc ((Tube.coverClass S (𝒰.cover.assign k) j).card : NNReal)
        ≤ ((2 * 2 ^ cnt k : ℕ) : NNReal) := by exact_mod_cast Nat.cast_le.mpr hup
      _ = 2 * (2 : NNReal) ^ cnt k := by push_cast; ring
      _ ≤ Cu * (2 : NNReal) ^ cnt k := mul_le_mul' hCu le_rfl
  · calc (2 : NNReal) ^ cnt k = ((2 ^ cnt k : ℕ) : NNReal) := by push_cast; ring
      _ ≤ ((Tube.coverClass S (𝒰.cover.assign k) j).card : NNReal) := by
          exact_mod_cast Nat.cast_le.mpr hlow
      _ ≤ Cu * ((Tube.coverClass S (𝒰.cover.assign k) j).card : NNReal) :=
          le_mul_of_one_le_left (by positivity) hCu1

open scoped Classical in
/-- **`(B)`'s hand-back clause is producible** — the per-trial debt of `C-D1`, discharged.

/§10 made `IsClassHomogeneousOn 𝒰 S'` a *conclusion* of `(B)` and named it the
descent's per-trial obligation.  This is its producer: the existing dyadic pass retains all but a
polylogarithmic share of the family and hands back exactly the two-sided class band, on the same
hierarchy `𝒰` and at the same constant `Cu` — **a loss, not a constant**, which is what `T-D6`
requires (`Kakeya.ML2Core.not_reentry_le` is what a constant would cost).

The loss `(1 − log δ)^{2(N+2)(N+1)}` is of the shape `Kakeya.StickyKakeya.gridLoss` absorbs
(`Kakeya.ML2Core.exists_threshold_loss_pow_potentialCeil_le`), so it fits the trial's own `Λ`. -/
theorem exists_classHomogeneous_subfamily (hn : Module.finrank ℝ E = 3) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (Cu : NNReal) (u : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (u : Set ι).Pairwise (fun i j => IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ∀ 𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu, 2 ≤ Cu →
      ∃ S' ⊆ u,
        (u.card : ℝ)
            ≤ (1 - Real.log (δ : ℝ))
                ^ (2 * ((Tube.ssfGridLen δ + 2) * (Tube.ssfGridLen δ + 1))) * (S'.card : ℝ) ∧
          IsClassHomogeneousOn 𝒰 S' := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hpass⟩ := Kakeya.Homogenize.exists_classBand_pass_of_uniformTubeSet.{u} hn
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro ι δ hδ hδle Cu u T hball hED 𝒰 hCu
  obtain ⟨S', hS'u, hloss, cnt, hband⟩ :=
    hpass hδ hδle (Tube.ssfGridLen δ) Cu u T hball hED 𝒰
  exact ⟨S', hS'u, hloss, isClassHomogeneousOn_of_classBand_pass 𝒰 hCu hband⟩

end ClassBandProducer

end Kakeya.ML2Core
