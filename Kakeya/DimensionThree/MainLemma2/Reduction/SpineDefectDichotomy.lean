/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectDescent
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTrial
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectExit
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountFloorObstruction
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorTerminal
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDichotomyInputs
public import Kakeya.DimensionThree.MainLemma2.Reduction.AssemblyPointwise

/-!
# `P3` — the descent, read at the family: from one trial to `Dichotomy`'s two disjuncts

`Kakeya.ML2Core.gain_of_trialDescent` is abstract in `(σ, Φ, P, lam, μ, A, B, Λ)`.  This file
instantiates it at the descent's actual state — a pair `(S, Z)` of a subfamily and its shading —
and produces the two disjuncts of `Kakeya.ML2Assembly.Dichotomy` at the top family, with the
accumulated `Λ ^ P` still in front.  The absorption of `Λ ^ P` is
`Kakeya.ML2Core.exists_threshold_loss_pow_potentialCeil_le` (`T-D5`) and is spent **once**, at the
top, in `Kakeya.ML2Core.dichotomy_disjuncts_of_trialDescent`.

## The two exit exponents are parameters — and why

`Kakeya.ML2Core.TrialOutcomeAt`'s exits are pinned at `ε₀ = β/2` and `g = 4·spineNu`, which are
`Dichotomy`'s own.  But the descent multiplies **both** by `Λ ^ P`, so the *per-trial* exits have to
sit a margin `α` inside `Dichotomy`'s: `β/2 − α` on the left and `4·spineNu + α` on the right.
`Kakeya.ML2Core.TrialOutcomeAtGain` is `TrialOutcomeAt` with those two exponents freed;
`Kakeya.ML2Core.trialOutcomeAt_eq_gain` is the `rfl` that says nothing else moved, so the statement
the floor block targets is untouched.

**Where `α` comes from, measured.**  `Kakeya.ML2Core.exists_dichotomyLeft_or_window_spine` proves
its left disjunct through the budget `hbud : 6ν + β/4 ≤ β/2`, i.e. with `β/4 − 6ν` of margin unused;
and `Kakeya.ML2Inputs.spineNu_le_div_48000` gives `ν ≤ β/48000`, so that margin is at least
`β/4 − 6β/48000 = β·(1/4 − 1/8000) > 0`.  Taking **`α := ν`** leaves the left exit at `β/2 − ν`,
still inside the budget with room to spare, and the right exit at `5ν`, which is what the descent
must be run at to land `Dichotomy`'s `4ν`.  `α` is spent **once**, at the top of the ladder, and
nowhere else.

## Contents

* `TrialOutcomeAtGain`, `trialOutcomeAt_eq_gain`;
* `descentState`, and the four monotonicity facts the descent needs of it;
* `dichotomy_disjuncts_of_trialDescent` — `P3`'s core, at one family;
* `dichotomy_disjuncts_of_trialDescent_absorbed` — the same with `Λ ^ P` spent.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core


/-! ## The descent's state, and the four facts it needs -/

section State

variable {ι : Type*} {δ : NNReal}

/-- **The descent's state**: the current subfamily, its shading, and its shading level.

`lam` is part of the state because `(B)` decays it — the refined source's
`λ(𝕊*,Z*) ≥ Λ⁻¹λ(𝕊,Z)` (l.5836) — and `Kakeya.ML2Core.gain_of_trialDescent`'s fullness ladder is
what carries that decay across the `P_max` trials while the trial's own *floor* stays fixed. -/
abbrev DescentState (ι : Type*) (δ : NNReal) : Type _ :=
  Finset ι × (ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) × NNReal

/-- The mass `μ(S,Z)`. -/
noncomputable def stateMass (x : DescentState ι δ) : ℝ≥0∞ := ∑ i ∈ x.1, volume (x.2.1 i).shade

/-- The fullness `λ(S,Z)`, as the descent's ladder reads it. -/
noncomputable def stateFullness (x : DescentState ι δ) : ℝ≥0∞ :=
  ShadedBody.fullness' x.1 (fun i => (x.2.1 i).toShadedBody)

/-- The sticky exit's right-hand side. -/
noncomputable def stateLeft (δ : NNReal) (ε₀ : ℝ) (x : DescentState ι δ) : ℝ≥0∞ :=
  (δ : ℝ≥0∞) ^ (-ε₀) * volume (⋃ i ∈ x.1, (x.2.1 i).shade)

/-- The terminal exit's right-hand side. -/
noncomputable def stateRight (δ : NNReal) (g β : ℝ) (x : DescentState ι δ) : ℝ≥0∞ :=
  (δ : ℝ≥0∞) ^ g * (x.1.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ x.1, (x.2.1 i).shade)

variable {S S' : Finset ι} {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

theorem iUnion_shade_subset (hS : S' ⊆ S) (hW : ∀ i, (W i).shade ⊆ (Z i).shade) :
    (⋃ i ∈ S', (W i).shade) ⊆ ⋃ i ∈ S, (Z i).shade := by
  intro y hy
  simp only [Set.mem_iUnion, exists_prop] at hy ⊢
  obtain ⟨i, hi, hyi⟩ := hy
  exact ⟨i, hS hi, hW i hyi⟩

theorem stateLeft_mono (ε₀ : ℝ) (lam lam' : NNReal) (hS : S' ⊆ S)
    (hW : ∀ i, (W i).shade ⊆ (Z i).shade) :
    stateLeft δ ε₀ ((S', W, lam') : DescentState ι δ)
      ≤ stateLeft δ ε₀ ((S, Z, lam) : DescentState ι δ) :=
  mul_le_mul' le_rfl (measure_mono (iUnion_shade_subset hS hW))

theorem stateRight_mono (g : ℝ) {β : ℝ} (hβ : 0 ≤ β) (lam lam' : NNReal) (hS : S' ⊆ S)
    (hW : ∀ i, (W i).shade ⊆ (Z i).shade) :
    stateRight δ g β ((S', W, lam') : DescentState ι δ)
      ≤ stateRight δ g β ((S, Z, lam) : DescentState ι δ) := by
  refine mul_le_mul' (mul_le_mul' le_rfl ?_) (measure_mono (iUnion_shade_subset hS hW))
  exact ENNReal.rpow_le_rpow (by exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hS)) hβ

end State

/-! ## `P3` -/

section Descent

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **`P3`, at one family: the descent produces `Dichotomy`'s two disjuncts, up to `Λ ^ P`.**

`Adm` is the trial's admissibility, left abstract: the producer (`Kakeya.ML2Core.IsTrialAt`)
supplies it.  `hclosed` is the **only** place where the descent needs to know anything about it —
that the triple `(B)` retains is admissible again — and it is therefore the exact home of the
re-entry obligation.

After  the accounting closes: seven of `IsTrialAt`'s binders transfer for free
(`Kakeya.ML2Core.trialAdmissible_of_step`), `IsClassHomogeneousOn 𝒰 S'` and
`ML2Shaded.HasDenseShading lam' S' W` are handed back by `(B)`,
`ML2Shaded.HasComparableDensities lam'⁻¹` is derived from them, the fixed floor is re-established by
the ladder, and the cardinality binder is about `u` and never moves. -/
theorem dichotomy_disjuncts_of_trialDescent
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {Adm : DescentState ι δ → Prop}
    {h ε₀ g β : ℝ} (hβ : 0 ≤ β) {Λ lam0 : ℝ≥0∞} (hΛ : 1 ≤ Λ) {P : ℕ}
    (hΦP : ∀ x, Adm x → potential h 𝒰 x.1 ≤ P)
    (hclosed : ∀ x, Adm x → ∀ S' ⊆ x.1,
      ∀ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∀ lam' : NNReal, S'.Nonempty →
      (∀ i, (W i).toTube = (x.2.1 i).toTube) → (∀ i, (W i).shade ⊆ (x.2.1 i).shade) →
      IsClassHomogeneousOn 𝒰 S' → 0 < lam' →
      ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody) →
      Adm ((S', W, lam') : DescentState ι δ))
    (htrial : ∀ x, Adm x →
      lam0 ≤ Λ ^ (P - potential h 𝒰 x.1) * stateFullness x →
      TrialOutcomeAtGain h ε₀ g β 𝒰 Λ x.2.2 x.1 x.2.1) :
    ∀ x, Adm x → lam0 ≤ stateFullness x →
      stateMass x ≤ Λ ^ P * stateLeft δ ε₀ x ∨ stateMass x ≤ Λ ^ P * stateRight δ g β x := by
  refine gain_of_trialDescent_top (Adm := Adm) (Φ := fun x => potential h 𝒰 x.1) (P := P)
    (lam := stateFullness) (μ := stateMass) (A := stateLeft δ ε₀) (B := stateRight δ g β)
    (Λ := Λ) (lam0 := lam0) hΛ hΦP ?_
  intro x hx hlad
  rcases htrial x hx hlad with hL | hR | ⟨S', hS'S, W, hS'ne, htube, hshade, hmass, hfull,
    hpot, hhom, lam', hlam'0, hlamΛ, hdense⟩
  · exact Or.inl (Or.inl hL)
  · exact Or.inl (Or.inr hR)
  · refine Or.inr ⟨((S', W, lam') : DescentState ι δ),
      hclosed x hx S' hS'S W lam' hS'ne htube hshade hhom hlam'0 hdense, hpot, hmass, hfull,
      ?_, ?_⟩
    · exact stateLeft_mono ε₀ x.2.2 lam' hS'S hshade
    · exact stateRight_mono g hβ x.2.2 lam' hS'S hshade

/-- **`P3` with `Λ ^ P` spent — once, at the top of the ladder.** -/
theorem dichotomy_disjuncts_of_trialDescent_absorbed
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {Adm : DescentState ι δ → Prop}
    {h ε₀ g ε₀' g' β : ℝ} (hβ : 0 ≤ β) {Λ lam0 : ℝ≥0∞} (hΛ : 1 ≤ Λ) {P : ℕ}
    (hΦP : ∀ x, Adm x → potential h 𝒰 x.1 ≤ P)
    (hclosed : ∀ x, Adm x → ∀ S' ⊆ x.1,
      ∀ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∀ lam' : NNReal, S'.Nonempty →
      (∀ i, (W i).toTube = (x.2.1 i).toTube) → (∀ i, (W i).shade ⊆ (x.2.1 i).shade) →
      IsClassHomogeneousOn 𝒰 S' → 0 < lam' →
      ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody) →
      Adm ((S', W, lam') : DescentState ι δ))
    (htrial : ∀ x, Adm x →
      lam0 ≤ Λ ^ (P - potential h 𝒰 x.1) * stateFullness x →
      TrialOutcomeAtGain h ε₀ g β 𝒰 Λ x.2.2 x.1 x.2.1)
    (habsL : Λ ^ P * (δ : ℝ≥0∞) ^ (-ε₀) ≤ (δ : ℝ≥0∞) ^ (-ε₀'))
    (habsR : Λ ^ P * (δ : ℝ≥0∞) ^ g ≤ (δ : ℝ≥0∞) ^ g') :
    ∀ x, Adm x → lam0 ≤ stateFullness x →
      stateMass x ≤ stateLeft δ ε₀' x ∨ stateMass x ≤ stateRight δ g' β x := by
  intro x hx hlam
  rcases dichotomy_disjuncts_of_trialDescent 𝒰 hβ hΛ hΦP hclosed htrial x hx hlam with hL | hR
  · refine Or.inl (hL.trans ?_)
    rw [stateLeft, stateLeft, ← mul_assoc]
    exact mul_le_mul' habsL le_rfl
  · refine Or.inr (hR.trans ?_)
    rw [stateRight, stateRight]
    calc Λ ^ P * ((δ : ℝ≥0∞) ^ g * (x.1.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ x.1, (x.2.1 i).shade))
        = (Λ ^ P * (δ : ℝ≥0∞) ^ g) * ((x.1.card : ℝ≥0∞) ^ β
            * volume (⋃ i ∈ x.1, (x.2.1 i).shade)) := by ring
      _ ≤ (δ : ℝ≥0∞) ^ g' * ((x.1.card : ℝ≥0∞) ^ β
            * volume (⋃ i ∈ x.1, (x.2.1 i).shade)) := mul_le_mul' habsR le_rfl
      _ = (δ : ℝ≥0∞) ^ g' * (x.1.card : ℝ≥0∞) ^ β
            * volume (⋃ i ∈ x.1, (x.2.1 i).shade) := by ring

end Descent

/-! ## The trial's admissibility, and the exact content of `hclosed` -/

section Admissible

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **`Kakeya.ML2Core.IsTrialAt`'s binder block, as a predicate on the descent's state.**

Exactly the nine clauses of `IsTrialAt`, read on the triple `(S, Z, lam)`; the tenth, the fixed
floor `δ^{ηin}/2 ≤ lam`, is deliberately absent — after  correction 2 it is
re-established at every step by `Kakeya.ML2Core.gain_of_trialDescent`'s ladder, not carried in the
state. -/
def TrialAdmissible (ηin : ℝ)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (x : DescentState ι δ) : Prop :=
  x.1 ⊆ u ∧ x.1.Nonempty ∧
    (∀ i, (x.2.1 i).toTube = (T i).toTube) ∧
    (∀ i, (x.2.1 i).shade ⊆ (T i).shade) ∧
    IsClassHomogeneousOn 𝒰 x.1 ∧
    (∀ i ∈ x.1, (x.2.1 i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
    Kakeya.maxDensity x.1 (fun i => (x.2.1 i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) ∧
    0 < x.2.2 ∧
    ML2Shaded.HasDenseShading x.2.2 x.1 (fun i => (x.2.1 i).toShadedBody)

/-- Equal tubes give equal bodies, hence equal carriers: a shaded tube's body is its tube's. -/
theorem toConvexSpaceBody_congr {A B : ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (h : A.toTube = B.toTube) : A.toConvexSpaceBody = B.toConvexSpaceBody := by
  rw [show A.toConvexSpaceBody = A.toTube.toConvexSpaceBody from rfl,
    show B.toConvexSpaceBody = B.toTube.toConvexSpaceBody from rfl, h]

theorem carrier_congr {A B : ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (h : A.toTube = B.toTube) :
    A.carrier = B.carrier := congrArg ConvexSpaceBody.carrier (toConvexSpaceBody_congr h)

/-- Every clause of `TrialAdmissible` transfers under a defect step.
Family containment, nonemptiness, tube and shade compatibility, the ball
condition, and the Katz-Tao bound transfer by restriction and monotonicity.
The defect step's remaining conjuncts supply class homogeneity, dense shading
and positivity of the new shading parameter. -/
theorem trialAdmissible_of_step {ηin : ℝ}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {x : DescentState ι δ} (hx : TrialAdmissible ηin 𝒰 x) {S' : Finset ι} (hS' : S' ⊆ x.1)
    {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {lam' : NNReal} (hne : S'.Nonempty)
    (htube : ∀ i, (W i).toTube = (x.2.1 i).toTube) (hshade : ∀ i, (W i).shade ⊆ (x.2.1 i).shade)
    (hhom : IsClassHomogeneousOn 𝒰 S') (hlam'0 : 0 < lam')
    (hdense : ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody)) :
    TrialAdmissible ηin 𝒰 ((S', W, lam') : DescentState ι δ) := by
  obtain ⟨hsu, -, hZtube, hZshade, -, hball, hmax, -, -⟩ := hx
  refine ⟨hS'.trans hsu, hne, fun i => (htube i).trans (hZtube i),
    fun i => (hshade i).trans (hZshade i), hhom, ?_, ?_, hlam'0, hdense⟩
  · intro i hi
    rw [carrier_congr (htube i)]
    exact hball i (hS' hi)
  · refine le_trans ?_ hmax
    refine le_trans (le_of_eq ?_) (Kakeya.maxDensity_mono _ hS')
    exact congrArg _ (funext fun i => toConvexSpaceBody_congr (htube i))

/-- **The trial at free exit exponents.**

`Kakeya.ML2Core.IsTrialAt`'s conclusion is `TrialOutcomeAt`, whose two exits are pinned at
`Dichotomy`'s own `β/2` and `4·spineNu`.  The descent multiplies **both** by `Λ ^ P`, so the exits
it can consume must sit one margin `α` inside `Dichotomy`'s: `β/2 − α` on the left and
`4·spineNu + α` on the right.  `IsTrialAtGain` is `IsTrialAt` with those two exponents freed;
`Kakeya.ML2Core.isTrialAtGain_of_isTrialAt` is the `α = 0` instance.  See
 the parameter comparison for the consequence. -/
def IsTrialAtGain (ε₀ g β h ηin : ℝ)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (Λ : ℝ≥0∞) : Prop :=
  ∀ S ⊆ u, ∀ Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∀ lam : NNReal,
    S.Nonempty →
    (∀ i, (Z i).toTube = (T i).toTube) →
    (∀ i, (Z i).shade ⊆ (T i).shade) →
    IsClassHomogeneousOn 𝒰 S →
    (∀ i ∈ S, (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
    Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
    ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody) →
    ML2Shaded.HasComparableDensities lam⁻¹ S (fun i => (Z i).toShadedBody) →
    (δ : NNReal) ^ ηin / 2 ≤ lam →
    (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
    TrialOutcomeAtGain h ε₀ g β 𝒰 Λ lam S Z

/-- **The specified `IsTrialAt` is `IsTrialAtGain` at margin `α = 0`.**

`rfl` at the definitional level, via `Kakeya.ML2Core.trialOutcomeAt_eq_gain`.  It is the only
instance of `IsTrialAtGain` the interface currently supplies, and  the parameter comparison
records why the descent needs `α > 0` on the **left**. -/
theorem isTrialAtGain_of_isTrialAt {β ϖ ε₁ h ηin : ℝ} {gain dens : ℝ → ℝ}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu} {Λ : ℝ≥0∞}
    (htrial : IsTrialAt β ϖ ε₁ h ηin gain dens 𝒰 Λ) :
    IsTrialAtGain (β / 2 - defectMargin β ϖ ε₁ gain dens)
      (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β h ηin 𝒰 Λ :=
  htrial

/-- **`Kakeya.ML2Core.IsTrialAt` feeds `P3`'s `htrial`.**

`ML2Shaded.HasComparableDensities lam⁻¹` is **derived** from the dense shading and `0 < lam`, and the fixed floor `δ^{ηin}/2 ≤ lam` is supplied by the
descent's ladder (correction 2), so it is a hypothesis here rather than a field of the state. -/
theorem trialOutcomeAtGain_of_isTrialAt {β ϖ ε₁ h ηin : ℝ} {gain dens : ℝ → ℝ}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu} {Λ : ℝ≥0∞}
    (htrial : IsTrialAt β ϖ ε₁ h ηin gain dens 𝒰 Λ)
    (hcard : (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)))
    (x : DescentState ι δ) (hx : TrialAdmissible ηin 𝒰 x)
    (hfloor : (δ : NNReal) ^ ηin / 2 ≤ x.2.2) :
    TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
      (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ
      x.2.2 x.1 x.2.1 := by
  obtain ⟨hsu, hne, hZtube, hZshade, hhom, hball, hmax, hlam0, hdense⟩ := hx
  exact htrial x.1 hsu x.2.1 x.2.2 hne hZtube hZshade hhom hball hmax hdense
    (hdense.hasComparableDensities hlam0) hfloor hcard

end Admissible

/-! ## The margin `α`, checked against the `(G₁)` budget -/

section Margin

/-- **The margin fits inside the `(G₁)` budget**.

`Kakeya.ML2Core.exists_dichotomyLeft_or_window_spine` proves its left disjunct through
`hbud : 6ν + β/4 ≤ β/2`, leaving `β/4 − 6ν` unused; `ML2Inputs.spineNu_le_div_48000` gives
`ν ≤ β/48000`, so `7ν ≤ 7β/48000 ≤ β/4` with room to spare and `α := ν` is inside the budget. -/
theorem defectMargin_le_budget {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ)
    (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    defectMargin β ϖ ε₁ gain dens
      ≤ β / 4 - 6 * ML2Spine.spineNu β ϖ ε₁ gain dens := by
  have hν := ML2Inputs.spineNu_le_div_48000 hβ hβ1 hϖ hε₁ hgain hdens
  have hν0 := ML2Spine.spineNu_pos hβ hϖ hε₁ hgain hdens
  simp only [defectMargin]
  linarith


end Margin

/-! ## `C-G1` — the interface body did not move -/

section CG1

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **`C-G1`: `Kakeya.ML2Core.TrialOutcomeAt`'s body, spelled out, is still exactly what it was.**

`Iff.rfl` against the *written* body, so that a later edit of `TrialOutcomeAt` — including one that
tried to move slack into `(B)`, which `C-G2` forbids — breaks this compatibility rather than passing
silently.  The `(B)` disjunct below is byte-for-byte the existing one, `IsClassHomogeneousOn`
conjunct included. -/
theorem trialOutcomeAt_body (β ϖ ε₁ h : ℝ) (gain dens : ℝ → ℝ)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (Λ : ℝ≥0∞) (lam : NNReal) (S : Finset ι)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) :
    TrialOutcomeAt β ϖ ε₁ h gain dens 𝒰 Λ lam S Z ↔
      ((∑ i ∈ S, volume (Z i).shade
          ≤ (δ : ℝ≥0∞) ^ (-(β / 2)) * volume (⋃ i ∈ S, (Z i).shade))
      ∨ (∑ i ∈ S, volume (Z i).shade
          ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens)
            * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade))
      ∨ (∃ S' ⊆ S, ∃ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
          S'.Nonempty ∧
          (∀ i, (W i).toTube = (Z i).toTube) ∧
          (∀ i, (W i).shade ⊆ (Z i).shade) ∧
          (∑ i ∈ S, volume (Z i).shade) ≤ Λ * ∑ i ∈ S', volume (W i).shade ∧
          ShadedBody.fullness' S (fun i => (Z i).toShadedBody)
            ≤ Λ * ShadedBody.fullness' S' (fun i => (W i).toShadedBody) ∧
          potential h 𝒰 S' + 1 ≤ potential h 𝒰 S ∧
          IsClassHomogeneousOn 𝒰 S' ∧
          ∃ lam' : NNReal, 0 < lam' ∧ lam ≤ Λ * lam' ∧
            ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody))) := Iff.rfl

/-- **`C-G2`: the generalisation touched the two exits and nothing else.**  The `(B)` disjunct of
`TrialOutcomeAtGain` is `TrialOutcomeAt`'s, whatever the exponents. -/
theorem trialOutcomeAtGain_defect_eq (h ε₀ g β : ℝ)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (Λ : ℝ≥0∞) (lam : NNReal) (S : Finset ι)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (ε₀' g' : ℝ) (hB : ∃ S' ⊆ S, ∃ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
      S'.Nonempty ∧
      (∀ i, (W i).toTube = (Z i).toTube) ∧
      (∀ i, (W i).shade ⊆ (Z i).shade) ∧
      (∑ i ∈ S, volume (Z i).shade) ≤ Λ * ∑ i ∈ S', volume (W i).shade ∧
      ShadedBody.fullness' S (fun i => (Z i).toShadedBody)
        ≤ Λ * ShadedBody.fullness' S' (fun i => (W i).toShadedBody) ∧
      potential h 𝒰 S' + 1 ≤ potential h 𝒰 S ∧
      IsClassHomogeneousOn 𝒰 S' ∧
      ∃ lam' : NNReal, 0 < lam' ∧ lam ≤ Λ * lam' ∧
        ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody)) :
    TrialOutcomeAtGain h ε₀ g β 𝒰 Λ lam S Z ∧ TrialOutcomeAtGain h ε₀' g' β 𝒰 Λ lam S Z :=
  ⟨Or.inr (Or.inr hB), Or.inr (Or.inr hB)⟩

end CG1

/-! ## `P4` — `GeometricCoreAt` from the descent -/

section TopLevel

universe u

/-- **The descent's two disjuncts, read as `Kakeya.ML2Assembly.Dichotomy`.**

`Kakeya.ML2Core.stateMass`, `stateLeft` and `stateRight` were chosen to be `Dichotomy`'s own three
expressions, so this is `Iff.rfl` and the bridge costs nothing. -/
theorem dichotomy_of_descentDisjuncts {β ε₀ g η : ℝ}
    (hdisj : ∀ᶠ (δ : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i => (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
        ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ η →
        (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
        stateMass (s, T, 1) ≤ stateLeft δ ε₀ (s, T, 1) ∨
          stateMass (s, T, 1) ≤ stateRight δ g β (s, T, 1)) :
    ML2Assembly.Dichotomy.{u} β ε₀ g η := hdisj

/-- **`P4`: `Kakeya.ML2Assembly.GeometricCoreAt` from the descent.**

Purely additive, and packaged exactly as `Kakeya.ML2Core.geometricCoreAt_of_rungMiddleFactor`
packages `dichotomy_of_rungFactors`: `GeometricCoreAt`, `Dichotomy` and `Cap/*` keep their texts.
The hypothesis is the descent's own output — the two disjuncts of
`Kakeya.ML2Core.dichotomy_disjuncts_of_trialDescent_absorbed`, at `Dichotomy`'s exponents, after the
margin `α` has been spent. -/
theorem geometricCoreAt_of_descent
    (hdesc : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
        ∀ᶠ (δ : NNReal) in nhdsWithin 0 (Set.Ioi 0),
          ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
            (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
            IsKatzTao s (fun i => (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
            ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ η →
            (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
            stateMass (s, T, 1) ≤ stateLeft δ (β / 2) (s, T, 1) ∨
              stateMass (s, T, 1)
                ≤ stateRight δ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) β (s, T, 1)) :
    ML2Assembly.GeometricCoreAt.{u} := by
  intro β ϖ gain dens hβ0 hβ1 hp hKT hF
  obtain ⟨ε₁, hε₁, η, hη0, hη1, hdisj⟩ := hdesc β ϖ gain dens hβ0 hβ1 hp hKT hF
  exact ⟨ε₁, hε₁, η, hη0, hη1, dichotomy_of_descentDisjuncts hdisj⟩

/-- **compatibility `T-D3`: at potential `0` the wrapper *is* the existing single-shot route.**

`Kakeya.ML2Core.geometricCoreAt_of_descent` asks for no more than
`Kakeya.ML2Assembly.GeometricCoreAt` itself already delivers: the round trip compiles, so the
wrapper's shape has not drifted from the existing one.  Together with
`Kakeya.ML2Core.gain_of_trialDescent_single` — the descent at `Φ ≡ 0`, `P = 0`, where `(B)` is
unavailable and no loss accumulates — this is the `P = 0` control in both halves, abstract and
concrete. -/
theorem geometricCoreAt_of_descent_of_geometricCoreAt
    (h : ML2Assembly.GeometricCoreAt.{u}) : ML2Assembly.GeometricCoreAt.{u} := by
  refine geometricCoreAt_of_descent (fun β ϖ gain dens hβ0 hβ1 hp hKT hF => ?_)
  obtain ⟨ε₁, hε₁, η, hη0, hη1, hdich⟩ := h β ϖ gain dens hβ0 hβ1 hp hKT hF
  exact ⟨ε₁, hε₁, η, hη0, hη1, hdich⟩

end TopLevel

/-! ## `P7` — the trichotomy, routed -/

section Trichotomy

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **`P7`: `lem:ml2-window-refinement`'s trichotomy, routed into the trial's three outcomes**
(refined source l.4392–4482).

The four routes of the source, in the order it takes them:

* the **sticky** alternative — `Kakeya.ML2Core.exists_dichotomyLeft_or_window_spine`'s left
  disjunct, at the accuracy `ε₀` — goes to `(G₁)`;
* **(F)**, the count floor and the four-factor defect product, goes to `(G₂)`;
* **(P)**, the eccentric plank exit, goes to `(G₂)` as well — so the two terminal routes are one
  hypothesis here, `hterm`, and the floor block owes exactly it;
* **(D)**, a *destroyed lower concentration*, goes to `(B)` — and this is the only route that does,
  which is compatibility `T-D1″`.

`(D)`'s data is the source's own: the retained pair `(S', W)` with the two ledgers and the class
band, together with the concentration bound `hafter` at exponent `τ/2` **after** the restrictions,
against `hbefore` at exponent `τ` **before** them.
`Kakeya.ML2Core.profileDrop_of_concentration_destroyed` turns that into the potential drop, so
`(B)` is assembled here and nowhere else.

**`T-D1″` is a typing fact, not a proof-reading one.**  The `(B)` disjunct of the conclusion can be
reached only through the `Or.inr (Or.inr …)` branch below, whose hypotheses include `hbefore` — the
window's level clause at exponent `τ`, *before* the restriction.  A family with no window therefore
cannot produce `(B)`: there is no other constructor. -/
theorem trial_of_trichotomy
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {h τ Θ ε₀ g β : ℝ} {Λ : ℝ≥0∞} {S : Finset ι}
    {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {lam : NNReal}
    (hh : 0 < h) (hΘ0 : 0 < Θ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hΘ2 : 2 ≤ Θ ^ (τ / 2))
    {a m : ℕ} (ham : a < m) (hm : m ≤ Tube.ssfGridLen δ)
    (hgap : 2 * h ≤ (τ / 2) * (Real.log Θ / Real.log (1 / (δ : ℝ))))
    (hbefore : ENNReal.ofReal (Θ ^ τ / 2) ≤ pairProfile 𝒰 S a m)
    (htri :
      (∑ i ∈ S, volume (Z i).shade
          ≤ (δ : ℝ≥0∞) ^ (-ε₀) * volume (⋃ i ∈ S, (Z i).shade))
      ∨ (∑ i ∈ S, volume (Z i).shade
          ≤ (δ : ℝ≥0∞) ^ g * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade))
      ∨ (∃ S' ⊆ S, ∃ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
          S'.Nonempty ∧
          (∀ i, (W i).toTube = (Z i).toTube) ∧
          (∀ i, (W i).shade ⊆ (Z i).shade) ∧
          (∑ i ∈ S, volume (Z i).shade) ≤ Λ * ∑ i ∈ S', volume (W i).shade ∧
          ShadedBody.fullness' S (fun i => (Z i).toShadedBody)
            ≤ Λ * ShadedBody.fullness' S' (fun i => (W i).toShadedBody) ∧
          IsClassHomogeneousOn 𝒰 S' ∧
          (∃ lam' : NNReal, 0 < lam' ∧ lam ≤ Λ * lam' ∧
            ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody)) ∧
          pairProfile 𝒰 S' a m ≤ ENNReal.ofReal (Θ ^ (τ / 2) / 2))) :
    TrialOutcomeAtGain h ε₀ g β 𝒰 Λ lam S Z := by
  rcases htri with hG₁ | hG₂ | ⟨S', hS'S, W, hne, htube, hshade, hmass, hfull, hhom, hshad,
    hafter⟩
  · exact Or.inl hG₁
  · exact Or.inr (Or.inl hG₂)
  · refine Or.inr (Or.inr ⟨S', hS'S, W, hne, htube, hshade, hmass, hfull, ?_, hhom, hshad⟩)
    exact profileDrop_of_concentration_destroyed 𝒰 hS'S hh hΘ0 hδ0 hδ1 ham hm hΘ2 hbefore hafter
      hgap

/-- **`T-D1″`, the structural half: without the `(D)` data there is no `(B)`.**

The same routing with the third alternative removed.  A producer that can only exhibit the sticky
exit or a terminal bound lands in the first two disjuncts, and the descent consults `(B)` nowhere —
so a family outside the window's reach gets no free passes.  Together with the floor block's
`Kakeya.ML2Core.not_levelClause_gridModel` (refined `T1`: the sticky grid family fails the window's
level clause), this is the anti-laundering control that  asks for on the descent's
side. -/
theorem trial_of_dichotomy_no_defect
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {h ε₀ g β : ℝ} {Λ : ℝ≥0∞} {lam : NNReal} {S : Finset ι}
    {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hdi :
      (∑ i ∈ S, volume (Z i).shade
          ≤ (δ : ℝ≥0∞) ^ (-ε₀) * volume (⋃ i ∈ S, (Z i).shade))
      ∨ (∑ i ∈ S, volume (Z i).shade
          ≤ (δ : ℝ≥0∞) ^ g * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade))) :
    TrialOutcomeAtGain h ε₀ g β 𝒰 Λ lam S Z :=
  hdi.imp id Or.inl

end Trichotomy

/-! ## `T-D1″` — the sticky grid family cannot reach `(B)` -/

section StickyGrid

/-- **The sticky grid family's two-level profile is bounded by the uniformity constant.**

Every level-`m` node of that family meets the central `ρ_m`-tube once `ρ_m ≥ δ + 6δK`, so there are
at most `C` of them (`Kakeya.ML2Core.gridModel_card_indexSet_le`), and `Δ_max ≤ #`.  The bound is
uniform in the subfamily `S` and in the coarse level `a`. -/
theorem pairProfile_le_of_gridModel {δ : NNReal} {K : ℕ} {C : NNReal}
    {s' : Finset (ULift.{u} ℕ)} (hs' : s' ⊆ gridIndex.{u} K) (hne : s'.Nonempty)
    (𝒰 : Tube.UniformTubeSet s' (fun n => (gridShaded.{u} δ K n).toTube) (Tube.ssfGridLen δ) C)
    {m : ℕ} (hm : m ≤ Tube.ssfGridLen δ)
    (hRm : (δ : ℝ) + 6 * δ * K ≤ Tube.gridScale δ (Tube.ssfGridLen δ) m)
    (S : Finset (ULift.{u} ℕ)) (a : ℕ) : pairProfile 𝒰 S a m ≤ (C : ℝ≥0∞) := by
  classical
  refine le_trans (pairProfile_le_card_footprint 𝒰 S a m) ?_
  have hsub : footprint 𝒰 S m ⊆ 𝒰.cover.indexSet m := Finset.filter_subset _ _
  have hcard : ((footprint 𝒰 S m).card : NNReal) ≤ C :=
    le_trans (by exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsub))
      (gridModel_card_indexSet_le hs' hne 𝒰 hm hRm)
  exact_mod_cast ENNReal.coe_le_coe.mpr hcard

/-- **`T-D1″`, the quantitative half: `(D)` cannot fire on the sticky grid family.**

`Kakeya.ML2Core.profileDrop_of_concentration_destroyed`'s `hbefore` — the *old* concentration,
larger than `½Θ^τ` — is **false** on that family as soon as `½Θ^τ` exceeds the uniformity constant,
which it does for every `Θ` the window supplies (`log Θ / log(1/δ) ≥ ε²/2` makes `Θ` a positive
power of `1/δ`, while `C` is `δ`-free).  So the family gets **no** free passes from the descent: it
has to exit through `(G)`, which is exactly where the source puts it.

This is the anti-laundering control in the form  specified — the original `T-D1`
(`potential = 0`) was rejected as very probably false, and it is not needed: what matters is that
`(B)` is unreachable there, not that the potential vanishes.  The structural half is
`Kakeya.ML2Core.trial_of_dichotomy_no_defect`; the floor block's
`Kakeya.ML2Core.not_levelClause_gridModel` is the third, independent, reason (the family fails the
window's level clause outright). -/
theorem not_defect_trigger_gridModel {δ : NNReal} {K : ℕ} {C : NNReal}
    {s' : Finset (ULift.{u} ℕ)} (hs' : s' ⊆ gridIndex.{u} K) (hne : s'.Nonempty)
    (𝒰 : Tube.UniformTubeSet s' (fun n => (gridShaded.{u} δ K n).toTube) (Tube.ssfGridLen δ) C)
    {m : ℕ} (hm : m ≤ Tube.ssfGridLen δ)
    (hRm : (δ : ℝ) + 6 * δ * K ≤ Tube.gridScale δ (Tube.ssfGridLen δ) m)
    (S : Finset (ULift.{u} ℕ)) (a : ℕ) {Θ τ : ℝ}
    (hbig : (C : ℝ≥0∞) < ENNReal.ofReal (Θ ^ τ / 2)) :
    ¬ ENNReal.ofReal (Θ ^ τ / 2) ≤ pairProfile 𝒰 S a m := fun hcon =>
  absurd (hcon.trans (pairProfile_le_of_gridModel hs' hne 𝒰 hm hRm S a)) (not_le.mpr hbig)

end StickyGrid

/-! ## The profile is a live quantity on real families -/

section Live

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}

omit [Nontrivial E] in
/-- **`Δ_max ≥ 1` as soon as one level-`l` cell of the footprint has positive volume.**

Together with `Kakeya.ML2Core.pairProfile_le_card_footprint` this brackets the profile between `1`
and the footprint's cardinality on every real family, so neither `Kakeya.ML2Core.profileExp`'s
`max 1` clamp nor its `⊤` branch is doing hidden work. -/
theorem one_le_pairProfile (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (S : Finset ι)
    {a m : ℕ} {j : ι} (hj : j ∈ footprint 𝒰 S a)
    (hpos : ∃ j' ∈ (footprint 𝒰 S m).filter
        (fun j' => (𝒰.cover.tube m j').toConvexSpaceBody ≤ (𝒰.cover.tube a j).toConvexSpaceBody),
      0 < volume (𝒰.cover.tube m j').carrier) :
    1 ≤ pairProfile 𝒰 S a m := by
  classical
  refine le_trans (Kakeya.one_le_maxDensity hpos) ?_
  exact Finset.le_sup (f := fun j => Kakeya.maxDensity
    ((footprint 𝒰 S m).filter
      (fun j' => (𝒰.cover.tube m j').toConvexSpaceBody ≤ (𝒰.cover.tube a j).toConvexSpaceBody))
    (fun j' => (𝒰.cover.tube m j').toConvexSpaceBody)) hj

end Live

/-! ## The descent's closure, with every still-open input as a named binder -/

section Closure

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **`P3` run on the *shading level* rather than on the aggregate fullness.**

 correction 2: what re-establishes the trial's fixed floor at every step is the
ladder on `lam` — the state's third component — and `(B)`'s `lam ≤ Λ · lam'` is exactly the ledger
it needs.  `Kakeya.ML2Core.dichotomy_disjuncts_of_trialDescent` runs the same induction on
`Kakeya.ML2Core.stateFullness`; both are available because `(B)` carries both ledgers. -/
theorem dichotomy_disjuncts_of_trialDescent_level
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {Adm : DescentState ι δ → Prop}
    {h ε₀ g β : ℝ} (hβ : 0 ≤ β) {Λ lam0 : ℝ≥0∞} (hΛ : 1 ≤ Λ) {P : ℕ}
    (hΦP : ∀ x, Adm x → potential h 𝒰 x.1 ≤ P)
    (hclosed : ∀ x, Adm x → ∀ S' ⊆ x.1,
      ∀ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)), ∀ lam' : NNReal, S'.Nonempty →
      (∀ i, (W i).toTube = (x.2.1 i).toTube) → (∀ i, (W i).shade ⊆ (x.2.1 i).shade) →
      IsClassHomogeneousOn 𝒰 S' → 0 < lam' →
      ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody) →
      Adm ((S', W, lam') : DescentState ι δ))
    (htrial : ∀ x, Adm x →
      lam0 ≤ Λ ^ (P - potential h 𝒰 x.1) * (x.2.2 : ℝ≥0∞) →
      TrialOutcomeAtGain h ε₀ g β 𝒰 Λ x.2.2 x.1 x.2.1) :
    ∀ x, Adm x → lam0 ≤ (x.2.2 : ℝ≥0∞) →
      stateMass x ≤ Λ ^ P * stateLeft δ ε₀ x ∨ stateMass x ≤ Λ ^ P * stateRight δ g β x := by
  refine gain_of_trialDescent_top (Adm := Adm) (Φ := fun x => potential h 𝒰 x.1) (P := P)
    (lam := fun x => (x.2.2 : ℝ≥0∞)) (μ := stateMass) (A := stateLeft δ ε₀)
    (B := stateRight δ g β) (Λ := Λ) (lam0 := lam0) hΛ hΦP ?_
  intro x hx hlad
  rcases htrial x hx hlad with hL | hR | ⟨S', hS'S, W, hS'ne, htube, hshade, hmass, hfull,
    hpot, hhom, lam', hlam'0, hlamΛ, hdense⟩
  · exact Or.inl (Or.inl hL)
  · exact Or.inl (Or.inr hR)
  · refine Or.inr ⟨((S', W, lam') : DescentState ι δ),
      hclosed x hx S' hS'S W lam' hS'ne htube hshade hhom hlam'0 hdense, hpot, hmass, hlamΛ,
      ?_, ?_⟩
    · exact stateLeft_mono ε₀ x.2.2 lam' hS'S hshade
    · exact stateRight_mono g hβ x.2.2 lam' hS'S hshade

/-- **The ladder re-establishes the trial's fixed floor** (refined l.5961–5962).

The source's arithmetic verbatim: the induction hypothesis carries `λ ≥ Λ^{P−P_max}δ^{η₀}`, and
`Λ^{P_max+1} ≤ δ^{-a₀}` upgrades it to the trial's own fixed `λ ≥ δ^{2η₀}`.  Here the upgrade is
the single hypothesis `hbase`, which is where the margin `α` is spent on the fullness side: with
`lam0 := δ^{ηin−α}/2` and `Λ^P ≤ δ^{-α}` it reads `Λ^P·δ^{ηin}/2 ≤ δ^{ηin−α}/2`. -/
theorem floor_of_ladder {Λ lam0 : ℝ≥0∞} (hΛ : 1 ≤ Λ) (hΛtop : Λ ≠ ⊤) {P k : ℕ} (hk : k ≤ P)
    {lam floor : NNReal}
    (hbase : Λ ^ P * (floor : ℝ≥0∞) ≤ lam0)
    (hlad : lam0 ≤ Λ ^ k * (lam : ℝ≥0∞)) : floor ≤ lam := by
  have hΛ0 : Λ ≠ 0 := fun h => by simp [h] at hΛ
  have hpow0 : Λ ^ P ≠ 0 := pow_ne_zero _ hΛ0
  have hpowtop : Λ ^ P ≠ ⊤ := ENNReal.pow_ne_top hΛtop
  have hmono : Λ ^ k * (lam : ℝ≥0∞) ≤ Λ ^ P * (lam : ℝ≥0∞) :=
    mul_le_mul' (pow_le_pow_right' hΛ hk) le_rfl
  have hchain : Λ ^ P * (floor : ℝ≥0∞) ≤ Λ ^ P * (lam : ℝ≥0∞) :=
    hbase.trans (hlad.trans hmono)
  exact_mod_cast (ENNReal.mul_le_mul_iff_right hpow0 hpowtop).mp hchain

/-- **The inputs of the descent's closure, as a named list.**

Every field is an obligation of a *named* owner, and the block is closed exactly when all of them
are discharged.  Nothing here is prose: the remaining work is this binder list.

* `loss_ne_top`, `loss_ge_one` — the per-trial loss is a real subpolynomial factor.  **Site.**
* `card` — the block's own cardinality binder `#u ≤ δ^{-4}`.  **Site**, and it is existing at every
  call of the reduction.
* `trial` — `Kakeya.ML2Core.IsTrialAt`: the trial itself.  **Floor block** for the two terminal
  routes ((F), still owing F4's H5; and (P), still owing F5), **this block** for the sticky exit
  `(G₁)` and for `(B)` via `Kakeya.ML2Core.profileDrop_of_concentration_destroyed`, and the **site**
  for the window package and the `CentredHandBack`-dependent factors that feed both.
* `top` — the top family is admissible.  **Site.**
* `ceiling` — `Φ_h ≤ P` on every admissible state; discharged by
  `Kakeya.ML2Core.potential_le_potentialCeil_five` from the site's `#u ≤ δ^{-4}` and `Cu ≤ δ^{-1}`.
* `base` — the ladder's base, `Λ^P·(δ^{ηin}/2) ≤ lam0`; discharged by
  `Kakeya.ML2Core.exists_threshold_loss_pow_potentialCeil_le` (`T-D5`) at the margin `α`.
* `ladder` — the top state is on the ladder.  **Site.**
* `absorbL`, `absorbR` — `Λ^P` spent once, on each exit; `T-D5` again, at `α := defectMargin`. -/
structure DescentInputs (ε₀ g β ηin h : ℝ) (Λ lam0 : ℝ≥0∞) (P : ℕ)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (x₀ : DescentState ι δ) : Prop where
  /-- The per-trial loss is at least one. -/
  loss_ge_one : 1 ≤ Λ
  /-- …and finite. -/
  loss_ne_top : Λ ≠ ⊤
  /-- The block's cardinality binder. -/
  card : (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ))
  /-- The trial: the floor block's two terminal routes, this block's `(G₁)` and `(B)`. -/
  trial : IsTrialAtGain ε₀ g β h ηin 𝒰 Λ
  /-- The top family is admissible. -/
  top : TrialAdmissible ηin 𝒰 x₀
  /-- The potential's ceiling on every admissible state. -/
  ceiling : ∀ x, TrialAdmissible ηin 𝒰 x → potential h 𝒰 x.1 ≤ P
  /-- The ladder's base: `Λ^P` fits inside the gap between `lam0` and the trial's fixed floor. -/
  base : Λ ^ P * (((δ : NNReal) ^ ηin / 2 : NNReal) : ℝ≥0∞) ≤ lam0
  /-- The top state is on the ladder. -/
  ladder : lam0 ≤ (x₀.2.2 : ℝ≥0∞)

/-- **The closure, at one family: the descent's two disjuncts from `Kakeya.ML2Core.DescentInputs`.**

Nothing is assumed beyond the eight fields.  `hclosed` is discharged outright by
`Kakeya.ML2Core.trialAdmissible_of_step`, the trial's fixed
floor by `Kakeya.ML2Core.floor_of_ladder`, and the comparable-densities clause is derived. -/
theorem descent_disjuncts_of_inputs {ε₀ g β ηin h : ℝ} {Λ lam0 : ℝ≥0∞} {P : ℕ}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {x₀ : DescentState ι δ} (hβ : 0 ≤ β)
    (H : DescentInputs ε₀ g β ηin h Λ lam0 P 𝒰 x₀) :
    stateMass x₀ ≤ Λ ^ P * stateLeft δ ε₀ x₀ ∨
      stateMass x₀ ≤ Λ ^ P * stateRight δ g β x₀ := by
  refine dichotomy_disjuncts_of_trialDescent_level (Adm := TrialAdmissible ηin 𝒰) 𝒰 hβ
    H.loss_ge_one H.ceiling ?_ ?_ x₀ H.top H.ladder
  · intro x hx S' hS' W lam' hne htube hshade hhom hlam'0 hdense
    exact trialAdmissible_of_step 𝒰 hx hS' hne htube hshade hhom hlam'0 hdense
  · intro x hx hlad
    have hfloor : ((δ : NNReal) ^ ηin / 2 : NNReal) ≤ x.2.2 :=
      floor_of_ladder H.loss_ge_one H.loss_ne_top (Nat.sub_le _ _) H.base hlad
    obtain ⟨hsu, hne, hZt, hZs, hhom, hball, hmax, hlam0, hdense⟩ := hx
    exact H.trial x.1 hsu x.2.1 x.2.2 hne hZt hZs hhom hball hmax hdense
      (hdense.hasComparableDensities hlam0) hfloor H.card

end Closure

/-! ## The floor block's `F7`, wired into the trial's conclusion -/

section FloorWiring

universe u

/-- **`F7` wired, by `exact`.**

`Kakeya.ML2Core.trialOutcome_middle_of_floorFactors` (the floor block's Stage 2a,
`Reduction/SpineFloorTerminal.lean`) concludes, at the eventual scale and on its own binders,

```lean
∀ Λ : ℝ≥0∞, TrialOutcomeAt β ϖ ε₁ h gain dens 𝒰 Λ lam S T
```

— the **whole** trichotomy, not merely its middle slot: it proves the terminal `(G₂)` bound and
injects it.  That conclusion is *definitionally* the trial's own, because
`Kakeya.ML2Core.trialOutcomeAt_eq_gain` is `rfl`; so the wiring is `exact hF7 Λ` and costs nothing.

`(G₁)` and `(B)` remain this block's: they are what
`Kakeya.ML2Core.trial_of_trichotomy` produces on the families where `F7`'s floor hypotheses do
**not** hold, and `(B)` is reachable only through
`Kakeya.ML2Core.profileDrop_of_concentration_destroyed` (compatibility `T-D1″`).

**Pointed at `_alpha`.**  `Kakeya.ML2Core.trialOutcome_middle_of_floorFactors_alpha` is the
floor block's terminal route at the margin-shifted exits, with its budget binder `hexp` at
`5ν`; its conclusion is exactly `Kakeya.ML2Core.IsTrialAt`'s after the  re-cut, so
this wiring now matches the trial's conclusion **on the nose** rather than at `α = 0`.  The `(G₁)`
side owed nothing to anyone: `Kakeya.ML2Core.stickyExit_pays_defectMargin` compiles that payment out
of the sticky exit's own budget. -/
theorem trialOutcomeAtGain_of_floorF7 {ι : Type u} {δ Cu : NNReal} {S : Finset ι}
    {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet S (fun i => (Z i).toTube) (Tube.ssfGridLen δ) Cu)
    {β ϖ ε₁ h : ℝ} {gain dens : ℝ → ℝ} {lam : NNReal}
    (hF7 : ∀ Λ : ℝ≥0∞, TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
      (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ lam S Z)
    (Λ : ℝ≥0∞) :
    TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
      (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ lam S Z :=
  hF7 Λ

end FloorWiring

/-! ## The `(G₁)` side pays the margin -/

section StickyPayment

/-- **The sticky exit pays `defectMargin` out of its own budget**.

`Kakeya.ML2Core.exists_dichotomyLeft_or_window_spine` proves its left disjunct through
`hbud : ν + ν + ν + ν + β/4 + ν + ν ≤ β/2`, i.e. the sticky exit really lands at `β/4 + 6ν`, and
`Kakeya.ML2Assembly.Dichotomy` only asks for `β/2`.  The descent needs it one margin stronger, at
`β/2 − α`; that is `β/4 + 6ν ≤ β/2 − ν`, i.e. `7ν ≤ β/4`, which
`Kakeya.ML2Core.defectMargin_le_budget` gives.

So the `(G₁)` half of the `α`-payment is **this block's, and it is free**: no producer has to be
re-derived on the left.  Only the two `(G₂)` routes owe `α` more gain, and 
measures both as payable. -/
theorem stickyExit_pays_defectMargin {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ)
    (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    β / 4 + 6 * ML2Spine.spineNu β ϖ ε₁ gain dens
      ≤ β / 2 - defectMargin β ϖ ε₁ gain dens := by
  have h := defectMargin_le_budget hβ hβ1 hϖ hε₁ hgain hdens
  linarith

end StickyPayment

end Kakeya.ML2Core
