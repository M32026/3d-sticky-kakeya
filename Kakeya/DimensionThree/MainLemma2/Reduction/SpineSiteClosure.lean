/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteProducer2

/-!
# The closing skeleton: `GeometricCoreAt` from the remaining producers

`Kakeya.ML2Core.geometricCoreAt_of_site` reduces `ML2Assembly.GeometricCoreAt` to a single
hypothesis `hsite` whose per-family conclusion is a twenty-one row existential
This file splits that hypothesis into exactly two named
obligations and discharges everything between them, so the run's remaining work is a list of
*producers*, not a list of rows.

## The split

* `Kakeya.ML2Core.SiteWitness` — the **selection**: given the block's family `s`, produce the
  retained `u' ⊆ s`, its hierarchy, its shading level, and the outer mass ledger.  Owner: the V-2
  witness hand.
* `Kakeya.ML2Core.TrialSupplier` — the **trial**, at the *ambient* hierarchy.  Owner: the floor
  block (`(F)` route) or the eccentric block (`(P)` route), through
  `Kakeya.ML2Core.htrial_of_floorData` / `Kakeya.ML2Core.htrial_of_eccentricData`.

Everything else — the four absorption rows, the two cardinality rows, the constant row, and the
filter's own `0 < δ < 1` — is discharged here from the arithmetic of
`Kakeya.ML2Core.absorb_of_loss_le` and `Kakeya.ML2Core.exists_threshold_loss_pow_potentialCeil_le`.

## The margin ledger, measured

The trial's exits are shifted by `Kakeya.ML2Core.defectMargin`, and the skeleton shows **where that
one margin is spent**.  Writing `aL` for the descent's own absorption exponent
(`Λ ^ potentialCeil h 5 δ ≤ δ ^ (-aL)`, which is `T-D5`), the four ledger rows collapse to

* `habsL`, `habsR` — spend `aL`, moving the trial's exits from `(β/2 − dm, 4ν + dm)` to
  `(β/2 − dm + aL, 4ν + dm − aL)`;
* `hKL`, `hKR` — spend the remainder, and **both reduce to the single condition**
  `K * δ ^ (dm − aL) ≤ 1`.

So `defectMargin` is a *budget split in two*, not a margin spent twice: the descent takes `aL`, the
outer transfer takes `dm − aL`, and `Kakeya.ML2Core.defectMargin_le_budget` is what says the sum
fits.  `SiteWitness` carries the second half as one row.

## Why the trial must be stated at the AMBIENT hierarchy

The existing
`Kakeya.ML2Core.trialOutcome_middle_of_floorFactors_alpha` concludes
`TrialOutcomeAtGain … 𝒰 Λ lam S T` with `𝒰` a hierarchy on `S` **itself**, freshly quantified with
the family.  `Kakeya.ML2Core.IsTrialAtGain` asks for the outcome at the *fixed ambient* `𝒰` on `u`,
for every `S ⊆ u`.  These are not interchangeable, and the gap does **not** close by restriction:

`Kakeya.ML2Core.potential` is built from `Kakeya.ML2Core.footprint`, which filters
`𝒰.cover.indexSet l`; `Tube.UniformTubeSet.restrictOccupied` shrinks that index set to
`S.image (𝒰.cover.assign l)`, so `Kakeya.ML2Core.pairProfile_mono_cover` gives only
`potential h (𝒰.restrictOccupied …) S' ≤ potential h 𝒰 S'` — one direction.  The descent disjunct
needs `potential h 𝒰 S' + 1 ≤ potential h 𝒰 S`, and a one-sided bound on the *smaller* side does
not deliver it.  (A node may contain a member of `S` without being assigned to one, which is
exactly why the footprint is stated on containment; see `Kakeya.ML2Core.footprint`.)

Hence `TrialSupplier` is stated at the ambient hierarchy, and the floor block owes the `C-D1`
re-cut — one hierarchy, `S ⊆ u` varying — rather than a bridge lemma that cannot exist.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Core

/-! ## The two named obligations -/

section Obligations

/-- **The selection the site discharge still waits on.**

Given the block's Katz-Tao family `s`, produce the retained subfamily `u' ⊆ s` together with its
hierarchy, its shading level and the outer mass ledger.  The last row is the outer half of the
`defectMargin` budget (see the module docstring): `K` is the transfer constant and `dm - aL` the
room left for it after the descent has taken `aL`.

**The admissible window for `aL` is `(0, min ηin dm]`, open at the left.**
`Kakeya.ML2Core.geometricCoreAt_of_witness_and_trial` needs `0 < aL` *strictly* — `0 ≤ aL` is
not enough: `T-D5` (`eventually_polylogLoss_pow_potentialCeil_le`) is instantiated at `aL` and
is vacuous at `aL = 0`.  `aL ≤ ηin` is what the lam-ladder row needs and `aL ≤ dm` what
the budget row needs; see `Kakeya.ML2Core.siteWitnessRows_of_trivial`. -/
def SiteWitness.{v} (η ηin dm aL : ℝ) (Cu₀ : NNReal) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      IsKatzTao s (fun i => (T i).toConvexSpaceBody) ((δ : ℝ≥0∞) ^ (-η)) →
      ShadedBody.fullness s (fun i => (T i).toShadedBody) ≥ δ ^ η →
      (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
      ∃ u' : Finset ι, u' ⊆ s ∧
      ∃ (Cu : NNReal) (_ : Tube.UniformTubeSet u' (fun i => (T i).toTube)
          (Tube.ssfGridLen δ) Cu) (lam : NNReal) (K : ℝ≥0∞),
        Cu ≤ Cu₀ ∧
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) ∧
        u'.Nonempty ∧
        Kakeya.maxDensity u' (fun i => (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) ∧
        0 < lam ∧
        ML2Shaded.HasDenseShading lam u' (fun i => (T i).toShadedBody) ∧
        (((δ : NNReal) ^ (ηin - aL) / 2 : NNReal) : ℝ≥0∞) ≤ (lam : ℝ≥0∞) ∧
        stateMass ((s, T, (1 : NNReal)) : DescentState ι δ)
          ≤ K * stateMass ((u', T, lam) : DescentState ι δ) ∧
        K * (δ : ℝ≥0∞) ^ (dm - aL) ≤ 1

/-- **The trial the site discharge still waits on, at the AMBIENT hierarchy.**

`Kakeya.ML2Core.htrial_of_floorData` and `Kakeya.ML2Core.htrial_of_eccentricData` conclude in this
slot.  The module docstring records why the ambient statement is the one that is needed and why the
subfamily-shaped `trialOutcome_middle_of_floorFactors_alpha` cannot be transported into it. -/
def TrialSupplier.{v} (β ϖ ε₁ ηin h : ℝ) (gain dens : ℝ → ℝ) (Cu₀ : NNReal)
    (Λf : NNReal → ℝ≥0∞) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type v} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (Cu : NNReal) (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu),
      Cu ≤ Cu₀ → (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
      IsTrialAtGain (β / 2 - defectMargin β ϖ ε₁ gain dens)
        (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β h ηin 𝒰 (Λf δ)

end Obligations

/-! ## The arithmetic the skeleton discharges -/

section Arithmetic

variable {δ : NNReal}

/-- `Λ ^ P` absorbs into the exponent through the `/2` the `lam` ladder carries. -/
theorem absorb_half_of_loss_le {Λ : ℝ≥0∞} {P : ℕ} {α x : ℝ} (hδ0 : 0 < δ)
    (hΛ : Λ ^ P ≤ (δ : ℝ≥0∞) ^ (-α)) :
    Λ ^ P * (((δ : NNReal) ^ x / 2 : NNReal) : ℝ≥0∞)
      ≤ (((δ : NNReal) ^ (x - α) / 2 : NNReal) : ℝ≥0∞) := by
  have hne : (δ : NNReal) ≠ 0 := hδ0.ne'
  have hcoe : ∀ y : ℝ, (((δ : NNReal) ^ y / 2 : NNReal) : ℝ≥0∞) = (δ : ℝ≥0∞) ^ y / 2 := by
    intro y
    rw [ENNReal.coe_div (by norm_num), ENNReal.coe_rpow_of_ne_zero hne]
    norm_num
  rw [hcoe, hcoe, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ← mul_assoc, mul_comm (Λ ^ P),
    mul_assoc]
  exact mul_le_mul' le_rfl (absorb_of_loss_le hδ0 hΛ)

/-- **The outer half of the margin budget, spent once.**

`hsite`'s two `K` rows are this lemma at `x = -(β/2)` and `x = 4ν`; the hypothesis
`K * δ ^ (dm - aL) ≤ 1` is the *only* thing either of them needs. -/
theorem absorbK_of_budget {K : ℝ≥0∞} {r x : ℝ} (hδ0 : 0 < δ)
    (hK : K * (δ : ℝ≥0∞) ^ r ≤ 1) :
    K * (δ : ℝ≥0∞) ^ (x + r) ≤ (δ : ℝ≥0∞) ^ x := by
  have hne : (δ : ℝ≥0∞) ≠ 0 := by simpa using hδ0.ne'
  calc K * (δ : ℝ≥0∞) ^ (x + r)
      = (K * (δ : ℝ≥0∞) ^ r) * (δ : ℝ≥0∞) ^ x := by
        rw [ENNReal.rpow_add _ _ hne ENNReal.coe_ne_top]; ring
    _ ≤ 1 * (δ : ℝ≥0∞) ^ x := mul_le_mul' hK le_rfl
    _ = (δ : ℝ≥0∞) ^ x := one_mul _

end Arithmetic

/-! ## The closing skeleton -/

section Closure

/-- **`ML2Assembly.GeometricCoreAt` from the two remaining producers.**

Everything between `SiteWitness` and `TrialSupplier` is discharged here: the two cardinality rows,
the hierarchy-constant row, the filter's `0 < δ < 1`, and all four absorption rows.  The exit
exponents are *chosen*, not assumed — `ε₀ = β/2 − dm`, `g = 4ν + dm`, and the primed pair is the
same shifted by the descent's own `aL` — which is what makes the two `K` rows collapse to
`SiteWitness`'s single budget row.

The conclusion is `ML2Assembly.GeometricCoreAt` and nothing weaker ((C)). -/
theorem geometricCoreAt_of_suppliers
    (hsup : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{v} β ϖ gain dens →
      KatzTaoEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ∃ (Cu₀ : NNReal) (ηin h aL : ℝ) (Λf : NNReal → ℝ≥0∞), 0 < h ∧
        (∀ δ : NNReal, 1 ≤ Λf δ ∧ Λf δ ≠ ⊤) ∧
        (∀ᶠ (δ : NNReal) in 𝓝[>] 0,
          Λf δ ^ potentialCeil h 5 δ ≤ (δ : ℝ≥0∞) ^ (-aL)) ∧
        SiteWitness.{v} η ηin (defectMargin β ϖ ε₁ gain dens) aL Cu₀ ∧
        TrialSupplier.{v} β ϖ ε₁ ηin h gain dens Cu₀ Λf) :
    ML2Assembly.GeometricCoreAt.{v} := by
  refine geometricCoreAt_of_site (fun β ϖ gain dens hβ0 hβ1 hp hKT hF => ?_)
  obtain ⟨ε₁, hε₁, η, hη0, hη1, Cu₀, ηin, h, aL, Λf, hh, hΛ, hloss, hwit, htri⟩ :=
    hsup β ϖ gain dens hβ0 hβ1 hp hKT hF
  refine ⟨ε₁, hε₁, η, hη0, hη1, Cu₀, ?_⟩
  obtain ⟨δ₀, hδ₀0, -, hCuρ⟩ := exists_threshold_const_le_rpow_neg_one Cu₀
  filter_upwards [hwit, htri, hloss,
    Ioo_mem_nhdsGT (show (0 : NNReal) < min 1 δ₀ from lt_min zero_lt_one hδ₀0)]
    with δ hw ht hl hδmem
  have hδ0 : 0 < δ := hδmem.1
  have hδ1 : δ < 1 := lt_of_lt_of_le hδmem.2 (min_le_left _ _)
  have hδle : δ ≤ δ₀ := le_of_lt (lt_of_lt_of_le hδmem.2 (min_le_right _ _))
  intro ι s T hball hKTs hfull hcard
  obtain ⟨u', hsub, Cu, 𝒰, lam, K, hCu0, hcards, hune, hmax, hlam0, hdense, hlamlow,
    houter, hK⟩ := hw s T hball hKTs hfull hcard
  have hcardu : (u'.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) := card_le_of_subset_of_card_le hsub hcards
  refine ⟨u', hsub, Cu, 𝒰, lam, Λf δ, K,
    β / 2 - defectMargin β ϖ ε₁ gain dens,
    4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens,
    β / 2 - defectMargin β ϖ ε₁ gain dens + aL,
    4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens - aL,
    ηin, h, aL, hCu0, hδ0, hδ1, hh, (hΛ δ).1, (hΛ δ).2, hcardu, hCuρ hδ0 hδle Cu hCu0, hune,
    hmax, hlam0, hdense, absorb_half_of_loss_le hδ0 hl, hlamlow,
    ht u' T Cu 𝒰 hCu0 hcardu, ?_, ?_, houter, ?_, ?_⟩
  · have := absorb_of_loss_le (δ := δ) (Λ := Λf δ) (P := potentialCeil h 5 δ) (α := aL)
      (x := -(β / 2 - defectMargin β ϖ ε₁ gain dens)) hδ0 hl
    have he : -(β / 2 - defectMargin β ϖ ε₁ gain dens) - aL
        = -(β / 2 - defectMargin β ϖ ε₁ gain dens + aL) := by ring
    rwa [he] at this
  · exact absorb_of_loss_le (δ := δ) (Λ := Λf δ) (P := potentialCeil h 5 δ) (α := aL)
      (x := 4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) hδ0 hl
  · have := absorbK_of_budget (δ := δ) (K := K)
      (r := defectMargin β ϖ ε₁ gain dens - aL) (x := -(β / 2)) hδ0 hK
    have he : -(β / 2) + (defectMargin β ϖ ε₁ gain dens - aL)
        = -(β / 2 - defectMargin β ϖ ε₁ gain dens + aL) := by ring
    rwa [he] at this
  · have := absorbK_of_budget (δ := δ) (K := K)
      (r := defectMargin β ϖ ε₁ gain dens - aL)
      (x := 4 * ML2Spine.spineNu β ϖ ε₁ gain dens) hδ0 hK
    have he : 4 * ML2Spine.spineNu β ϖ ε₁ gain dens + (defectMargin β ϖ ε₁ gain dens - aL)
        = 4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens - aL := by ring
    rwa [he] at this

end Closure

/-! ## compatibility: what the ledger caps the site's uniformisation exponent at -/

section UniformisationCap

variable {δ : NNReal}

/-- **The `K` row caps the site's uniformisation exponent at the MARGIN, not at `β/2`.**

If the retained subfamily is bought at loss `K = δ^(−α)` — which is what every uniformising producer
that returns a subfamily costs — then `hsite`'s row `K · δ^(−ε₀') ≤ δ^(−β/2)`, at the skeleton's own
`ε₀' = β/2 − dm + aL`, forces `α ≤ dm − aL`.

The `β/2` in the row is **not** the cap: it cancels.  What is left is the defect margin minus
whatever the descent already spent. -/
theorem uniformisation_exponent_le_of_absorbK {α dm aL β : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hK : (δ : ℝ≥0∞) ^ (-α) * (δ : ℝ≥0∞) ^ (-(β / 2 - dm + aL))
      ≤ (δ : ℝ≥0∞) ^ (-(β / 2))) :
    α ≤ dm - aL := by
  have hne : (δ : ℝ≥0∞) ≠ 0 := by simpa using hδ0.ne'
  have hlt : (δ : ℝ≥0∞) < 1 := by exact_mod_cast hδ1
  have hpos : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) := by simpa using hδ0
  rw [← ENNReal.rpow_add _ _ hne ENNReal.coe_ne_top] at hK
  by_contra hcon
  have hcon' : dm - aL < α := not_le.mp hcon
  have hlt2 : -α + -(β / 2 - dm + aL) < -(β / 2) := by linarith
  exact absurd (lt_of_le_of_lt hK (ENNReal.rpow_lt_rpow_of_exponent_gt hpos hlt hlt2))
    (lt_irrefl _)

/-- **The measured cap, in numbers**.

`Kakeya.ML2Core.defectMargin_eq` makes the margin `ML2Spine.spineNu`, and
`ML2Inputs.spineNu_le_div_48000` bounds that by `β/48000`.  So the site's producer must run at

  `α ≤ spineNu β ϖ ε₁ gain dens − aL ≤ β/48000`,

and a producer at `α = β/4` overshoots by more than four orders of magnitude at every `β > 0`. -/
theorem uniformisation_exponent_le_div_48000 {β ϖ ε₁ α aL : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hα : α ≤ defectMargin β ϖ ε₁ gain dens - aL) (haL : 0 ≤ aL) :
    α ≤ β / 48000 := by
  have hν := ML2Inputs.spineNu_le_div_48000 hβ hβ1 hϖ hε₁ hgain hdens
  rw [defectMargin_eq] at hα
  linarith

/-- **FIRING CONTROL for the cap: `α = β/4` is refuted at every `β > 0`.** -/
theorem not_uniformisation_exponent_quarter {β ϖ ε₁ aL : ℝ} {gain dens : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) (haL : 0 ≤ aL) :
    ¬ (β / 4 ≤ defectMargin β ϖ ε₁ gain dens - aL) := by
  intro hcon
  have := uniformisation_exponent_le_div_48000 (α := β / 4) hβ hβ1 hϖ hε₁ hgain hdens hcon haL
  linarith

end UniformisationCap

/-! ## Discharging three of the five hypotheses -/

section Discharge

/-- **`0 < h` at the site's own choice `Kakeya.ML2Core.defectH`.** -/
theorem defectH_pos {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hε₁ : 0 < ε₁) (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    0 < defectH β ϖ ε₁ gain dens := by
  have he : 0 < ML2Spine.spineDiv ϖ ε₁ := ML2Spine.spineDiv_pos hϖ hε₁
  have hsp := ML2Spine.spineRung_isSpine hβ0 hβ1 hϖ hε₁ hgain hdens
  have hτ₁ : 0 < ML2Spine.spineRung β ϖ ε₁ gain dens 1 := hsp.rung_pos 1
  unfold defectH
  positivity

/-- **The per-trial loss the descent can actually afford: polylogarithmic in `1/δ`.**

`StickyKakeya.gridLoss`'s own shape, with the `A ^ (ssfGridLen + 1)` factor dropped — see
`Kakeya.ML2Core.not_eventually_rpow_pow_potentialCeil_le` below for why nothing with a genuine
`δ`-power may be put here. -/
noncomputable def polylogLoss (K' : ℕ) (δ : NNReal) : ℝ≥0∞ :=
  ENNReal.ofReal (max 1 ((1 - Real.log (δ : ℝ)) ^ K'))

theorem one_le_polylog {δ : NNReal} (hδ1 : δ ≤ 1) (K' : ℕ) :
    (1 : ℝ) ≤ (1 - Real.log (δ : ℝ)) ^ K' := by
  have hlog : Real.log (δ : ℝ) ≤ 0 := Real.log_nonpos (by positivity) (by exact_mod_cast hδ1)
  exact one_le_pow₀ (by linarith)

/-- **`1 ≤ Λf δ` at EVERY `δ`** — the `max 1` is there precisely so that
`Kakeya.ML2Core.geometricCoreAt_of_suppliers`'s unconditional binder is met without moving it. -/
theorem one_le_polylogLoss (K' : ℕ) (δ : NNReal) : 1 ≤ polylogLoss K' δ := by
  rw [polylogLoss, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (le_max_left _ _)

theorem polylogLoss_ne_top (K' : ℕ) (δ : NNReal) : polylogLoss K' δ ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- **`T-D5`, in the skeleton's own slot.**

`Kakeya.ML2Core.exists_threshold_loss_pow_potentialCeil_le` is a threshold statement about a real
number; this is the same fact as the filter hypothesis `geometricCoreAt_of_suppliers` asks for.
Reduces `N` from 5 to 4. -/
theorem eventually_polylogLoss_pow_potentialCeil_le (K' : ℕ) {h : ℝ} {aL : ℝ} (haL : 0 < aL) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      polylogLoss K' δ ^ potentialCeil h 5 δ ≤ (δ : ℝ≥0∞) ^ (-aL) := by
  obtain ⟨δ₀, hδ₀0, hδ₀1, hbd⟩ :=
    exists_threshold_loss_pow_potentialCeil_le K' (h := h) 5 aL haL
  filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < min 1 δ₀ from lt_min zero_lt_one hδ₀0)]
    with δ hδ
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδ.2 (min_le_left _ _))
  have hδle : δ ≤ δ₀ := le_of_lt (lt_of_lt_of_le hδ.2 (min_le_right _ _))
  have hbase : (1 : ℝ) ≤ (1 - Real.log (δ : ℝ)) ^ K' := one_le_polylog hδ1 K'
  have hstep : ((1 - Real.log (δ : ℝ)) ^ K') ^ potentialCeil h 5 δ
      ≤ ((1 - Real.log (δ : ℝ)) ^ K') ^ (potentialCeil h 5 δ + 1) :=
    pow_le_pow_right₀ hbase (Nat.le_succ _)
  have hreal : ((1 - Real.log (δ : ℝ)) ^ K') ^ potentialCeil h 5 δ ≤ (δ : ℝ) ^ (-aL) :=
    hstep.trans (hbd hδ0 hδle)
  have hmax : max 1 ((1 - Real.log (δ : ℝ)) ^ K') = (1 - Real.log (δ : ℝ)) ^ K' :=
    max_eq_right hbase
  have hpow : polylogLoss K' δ ^ potentialCeil h 5 δ
      = ENNReal.ofReal (((1 - Real.log (δ : ℝ)) ^ K') ^ potentialCeil h 5 δ) := by
    rw [polylogLoss, hmax, ← ENNReal.ofReal_pow (by linarith)]
  have hrhs : ENNReal.ofReal ((δ : ℝ) ^ (-aL)) = (δ : ℝ≥0∞) ^ (-aL) := by
    rw [← ENNReal.ofReal_rpow_of_pos (show (0:ℝ) < (δ : ℝ) by exact_mod_cast hδ0)]
    simp
  rw [hpow, ← hrhs]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **compatibility: a per-trial loss carrying a genuine `δ`-power is NOT absorbable.**

`T-D6`'s verdict again, one level down.  The descent pays its loss `potentialCeil h 5 δ` times, and
that exponent is unbounded as `δ → 0` (`Kakeya.ML2Core.exists_threshold_le_Pmax`).  So a loss
`δ^(-η)` with `η > 0` — for instance a `Λf` that swallows the density factor `lam⁻¹ ≈ δ^(-ηin)` —
exceeds **every** fixed `δ^(-aL)` below a threshold, and the loss-bound hypothesis of
`Kakeya.ML2Core.geometricCoreAt_of_suppliers` is false for it.

Consequence for the site: the refinement's density loss must be paid **once**, inside `K` (where
`Kakeya.ML2Core.absorbK_of_budget` charges it), and must not enter the per-trial `Λf`. -/
theorem not_eventually_rpow_pow_potentialCeil_le {h η aL : ℝ} (hh : 0 < h) (hη : 0 < η) :
    ¬ (∀ (δ : NNReal), 0 < δ → δ < 1 →
        ((δ : ℝ≥0∞) ^ (-η)) ^ potentialCeil h 5 δ ≤ (δ : ℝ≥0∞) ^ (-aL)) := by
  intro hcon
  obtain ⟨M, hM⟩ := exists_nat_gt (aL / η)
  obtain ⟨δ₀, hδ₀0, hPmax⟩ := exists_threshold_le_Pmax hh M
  set δ : NNReal := min δ₀ (1 / 2) with hδdef
  have hδ0 : 0 < δ := lt_min hδ₀0 (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hMle : M ≤ Pmax h δ := hPmax δ hδ0 hδle
  have hPle : Pmax h δ ≤ potentialCeil h 5 δ := by
    rw [Pmax_eq_potentialCeil]
    refine Nat.mul_le_mul_left _ (Nat.ceil_le_ceil ?_)
    exact div_le_div_of_nonneg_right (by norm_num : (4:ℝ) ≤ 5) hh.le
  have hMle' : M ≤ potentialCeil h 5 δ := hMle.trans hPle
  have hpos : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) := by simpa using hδ0
  have hlt : (δ : ℝ≥0∞) < 1 := by exact_mod_cast hδ1
  have hcollapse : ((δ : ℝ≥0∞) ^ (-η)) ^ potentialCeil h 5 δ
      = (δ : ℝ≥0∞) ^ (-η * (potentialCeil h 5 δ : ℝ)) := by
    rw [← ENNReal.rpow_natCast ((δ : ℝ≥0∞) ^ (-η)) (potentialCeil h 5 δ),
      ← ENNReal.rpow_mul]
  have hK := hcon δ hδ0 hδ1
  rw [hcollapse] at hK
  have hexp : -aL ≤ -η * (potentialCeil h 5 δ : ℝ) := by
    by_contra hc
    have hc' : -η * (potentialCeil h 5 δ : ℝ) < -aL := not_le.mp hc
    exact absurd (lt_of_le_of_lt hK (ENNReal.rpow_lt_rpow_of_exponent_gt hpos hlt hc'))
      (lt_irrefl _)
  have hMR : (M : ℝ) ≤ (potentialCeil h 5 δ : ℝ) := by exact_mod_cast hMle'
  have hbig : aL / η < (potentialCeil h 5 δ : ℝ) := lt_of_lt_of_le hM hMR
  have hsmall : (potentialCeil h 5 δ : ℝ) ≤ aL / η := by
    rw [le_div_iff₀ hη]; linarith
  linarith


/-- **The reconciliation, : the floor MUST reserve a second margin in the exit.**

If the trial handed its right exit back at `4ν` — i.e. if F7's `hexp` ran at `5ν = 4ν + dm` with the
single `dm` spent inside the floor by `Λf` — then `hsite`'s row `K · δ^(g') ≤ δ^(4ν)` at
`g' = 4ν − aL` would ask for `K · δ^(−aL) ≤ 1`, which **no** transfer constant `K ≥ 1`
satisfies once the descent's own absorption is nontrivial (`aL > 0`).

So the floor's `6ν` is `4ν + dm(spent by `Λf`) + dm(reserved for the descent)`, and it does not
double-count.  See  the parameter comparison. -/
theorem not_absorbK_without_reservation {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {K : ℝ≥0∞} (hK1 : 1 ≤ K) {aL : ℝ} (haL : 0 < aL) :
    ¬ (K * (δ : ℝ≥0∞) ^ (-aL) ≤ 1) := by
  intro hcon
  have hpos : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) := by simpa using hδ0
  have hlt : (δ : ℝ≥0∞) < 1 := by exact_mod_cast hδ1
  have hone : (δ : ℝ≥0∞) ^ (0 : ℝ) < (δ : ℝ≥0∞) ^ (-aL) :=
    ENNReal.rpow_lt_rpow_of_exponent_gt hpos hlt (by linarith)
  rw [ENNReal.rpow_zero] at hone
  have : (1 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-aL) ≤ K * (δ : ℝ≥0∞) ^ (-aL) := mul_le_mul' hK1 le_rfl
  rw [one_mul] at this
  exact absurd (lt_of_lt_of_le hone (this.trans hcon)) (lt_irrefl _)


/-- **`ML2Assembly.GeometricCoreAt` from TWO producers.**

`Kakeya.ML2Core.geometricCoreAt_of_suppliers` asks for five hypotheses; three of them are the site's
own choices and are discharged here:

* `0 < h` at `h := Kakeya.ML2Core.defectH` — `Kakeya.ML2Core.defectH_pos`;
* `1 ≤ Λf δ` and `Λf δ ≠ ⊤` at `Λf := Kakeya.ML2Core.polylogLoss K'` — unconditional;
* the `T-D5` loss bound — `Kakeya.ML2Core.eventually_polylogLoss_pow_potentialCeil_le`.

What is left is **N = 2**: `Kakeya.ML2Core.SiteWitness` (the V-2 witness hand) and
`Kakeya.ML2Core.TrialSupplier` (the floor block, after the `C-D1` re-cut of `_alpha`).  Nothing else
stands between the tree and `ML2Assembly.GeometricCoreAt`. -/
theorem geometricCoreAt_of_witness_and_trial (K' : ℕ)
    (hsup : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{v} β ϖ gain dens →
      KatzTaoEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
      0 < ϖ ∧ (∀ ζ, 0 < ζ → 0 < gain ζ) ∧ (∀ ζ, 0 < ζ → 0 < dens ζ) ∧
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ∃ (Cu₀ : NNReal) (ηin aL : ℝ), 0 < aL ∧
        SiteWitness.{v} η ηin (defectMargin β ϖ ε₁ gain dens) aL Cu₀ ∧
        TrialSupplier.{v} β ϖ ε₁ ηin (defectH β ϖ ε₁ gain dens) gain dens Cu₀
          (polylogLoss K')) :
    ML2Assembly.GeometricCoreAt.{v} := by
  refine geometricCoreAt_of_suppliers (fun β ϖ gain dens hβ0 hβ1 hp hKT hF => ?_)
  obtain ⟨hϖ, hgain, hdens, ε₁, hε₁, η, hη0, hη1, Cu₀, ηin, aL, haL, hwit, htri⟩ :=
    hsup β ϖ gain dens hβ0 hβ1 hp hKT hF
  exact ⟨ε₁, hε₁, η, hη0, hη1, Cu₀, ηin, defectH β ϖ ε₁ gain dens, aL, polylogLoss K',
    defectH_pos hβ0 hβ1 hϖ hε₁ hgain hdens,
    fun δ => ⟨one_le_polylogLoss K' δ, polylogLoss_ne_top K' δ⟩,
    eventually_polylogLoss_pow_potentialCeil_le K' haL, hwit, htri⟩

end Discharge

/-! ## The `(F)` route, wired: `TrialSupplier` from the `C-D1` `_alpha` -/

section FloorRoute

/-- **The site's polylogarithmic loss is below every negative power.**

Same threshold as `Kakeya.ML2Core.eventually_polylogLoss_pow_potentialCeil_le`, at exponent one. -/
theorem eventually_polylogLoss_le (K' : ℕ) {α : ℝ} (hα : 0 < α) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, polylogLoss K' δ ≤ (δ : ℝ≥0∞) ^ (-α) := by
  obtain ⟨δ₀, hδ₀0, hδ₀1, hbd⟩ :=
    exists_threshold_loss_pow_potentialCeil_le K' (h := 1) 5 α hα
  filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < min 1 δ₀ from lt_min zero_lt_one hδ₀0)]
    with δ hδ
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ ≤ 1 := le_of_lt (lt_of_lt_of_le hδ.2 (min_le_left _ _))
  have hδle : δ ≤ δ₀ := le_of_lt (lt_of_lt_of_le hδ.2 (min_le_right _ _))
  have hbase : (1 : ℝ) ≤ (1 - Real.log (δ : ℝ)) ^ K' := one_le_polylog hδ1 K'
  have hstep : (1 - Real.log (δ : ℝ)) ^ K'
      ≤ ((1 - Real.log (δ : ℝ)) ^ K') ^ (potentialCeil 1 5 δ + 1) := by
    calc (1 - Real.log (δ : ℝ)) ^ K' = ((1 - Real.log (δ : ℝ)) ^ K') ^ 1 := (pow_one _).symm
      _ ≤ ((1 - Real.log (δ : ℝ)) ^ K') ^ (potentialCeil 1 5 δ + 1) :=
          pow_le_pow_right₀ hbase (Nat.succ_le_succ (Nat.zero_le _))
  have hreal : (1 - Real.log (δ : ℝ)) ^ K' ≤ (δ : ℝ) ^ (-α) := hstep.trans (hbd hδ0 hδle)
  have hmax : max 1 ((1 - Real.log (δ : ℝ)) ^ K') = (1 - Real.log (δ : ℝ)) ^ K' :=
    max_eq_right hbase
  have hrhs : ENNReal.ofReal ((δ : ℝ) ^ (-α)) = (δ : ℝ≥0∞) ^ (-α) := by
    rw [← ENNReal.ofReal_rpow_of_pos (show (0:ℝ) < (δ : ℝ) by exact_mod_cast hδ0)]
    simp
  rw [polylogLoss, hmax, ← hrhs]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **`hΛf`, produced.**  `C-D1` `_alpha`'s absorption row at the site's own `Λf`, so it is not a
named hypothesis of the closure. -/
theorem eventually_hΛf_polylogLoss (K' : ℕ) {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      polylogLoss K' δ * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
            + 2 * defectMargin β ϖ ε₁ gain dens)
        ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
            + defectMargin β ϖ ε₁ gain dens) := by
  have hdm : 0 < defectMargin β ϖ ε₁ gain dens := by
    rw [defectMargin_eq]; exact ML2Spine.spineNu_pos hβ0 hϖ hε₁ hgain hdens
  filter_upwards [eventually_polylogLoss_le K' hdm, self_mem_nhdsWithin] with δ hΛ hδ0
  have hδ0' : 0 < δ := hδ0
  have hne : (δ : ℝ≥0∞) ≠ 0 := by simpa using hδ0'.ne'
  calc polylogLoss K' δ * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
          + 2 * defectMargin β ϖ ε₁ gain dens)
      ≤ (δ : ℝ≥0∞) ^ (-defectMargin β ϖ ε₁ gain dens)
        * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
          + 2 * defectMargin β ϖ ε₁ gain dens) := mul_le_mul' hΛ le_rfl
    _ = (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
          + defectMargin β ϖ ε₁ gain dens) := by
        rw [← ENNReal.rpow_add _ _ hne ENNReal.coe_ne_top]; ring_nf

/-- **`Kakeya.ML2Core.TrialSupplier` from the `C-D1` floor block.**

`hF7` is `trialOutcome_middle_of_floorFactors_alpha`'s conclusion after  (ambient
`𝒰` on `u`, `S ⊆ u`); `hfloor` is the per-family `(F)` payload
(`Kakeya.ML2Core.FloorPayload`); `hΛf` is produced by
`Kakeya.ML2Core.eventually_hΛf_polylogLoss` at `Λf := Kakeya.ML2Core.polylogLoss K'`.

The proof is one positional `exact` — the floor owner's `M1PROBE_supplier` check, existing. -/
theorem trialSupplier_of_floorRoute.{w} {β ϖ ε₁ ηin η' h : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Cu₀ : NNReal} {Λf : NNReal → ℝ≥0∞}
    (hF7 : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type w} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (Cu : NNReal) (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (a b m : ℕ) (S : Finset ι) (hS : S ⊆ u)
        (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (lam : NNReal),
        S.Nonempty →
        ∀ (ht : ∀ i, (Z i).toTube = (T i).toTube),
        (∀ i, (Z i).shade ⊆ (T i).shade) →
        ∀ (hh : IsClassHomogeneousOn 𝒰 S),
        (∀ i ∈ S, (Z i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ S (fun i => (Z i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) →
        Cu ≤ Cu₀ →
        Λf δ * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
              + 2 * defectMargin β ϖ ε₁ gain dens)
            ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
              + defectMargin β ϖ ε₁ gain dens) →
        RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
          η' (Λf δ) ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m →
        ∀ Λ : ℝ≥0∞, TrialOutcomeAtGain h (β / 2 - defectMargin β ϖ ε₁ gain dens)
          (4 * ML2Spine.spineNu β ϖ ε₁ gain dens + defectMargin β ϖ ε₁ gain dens) β 𝒰 Λ lam S Z)
    (hΛf : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      Λf δ * (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
            + 2 * defectMargin β ϖ ε₁ gain dens)
          ≤ (δ : ℝ≥0∞) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens
            + defectMargin β ϖ ε₁ gain dens))
    (hfloor : FloorPayload.{w} (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf) :
    TrialSupplier.{w} β ϖ ε₁ ηin h gain dens Cu₀ Λf := by
  filter_upwards [hF7, hΛf, hfloor] with δ hδ hΛ hfl
  intro ι u T Cu 𝒰 hCu hcard S hS Z lam hne ht hs hh hb hmx hd hc hl hcard'
  obtain ⟨a, b, m, hf⟩ := hfl u T Cu 𝒰 S hS Z ht hh
  exact hδ u T Cu 𝒰 a b m S hS Z lam hne ht hs hh hb hmx hd hc hl hcard' hCu hΛ hf (Λf δ)


/-- **The three arithmetic rows of `Kakeya.ML2Core.SiteWitness` at the trivial instantiation.**

`u' := s`, `lam := 1`, `K := 1`.  Nothing in `SiteWitness` forces a proper subfamily, a shading
level below `1`, or a non-trivial transfer constant, so the nonvacuity witness may take all three
trivial; the lam-ladder row and the budget row then reduce to `aL ≤ ηin` and `aL ≤ dm`, and the
mass ledger is `le_rfl` because both sides are the same term.

**Caveat for the supplier** : the skeleton
`Kakeya.ML2Core.geometricCoreAt_of_witness_and_trial` needs `0 < aL`, strictly — `0 ≤ aL` is not
enough, because `T-D5` is instantiated at `aL`.  The admissible window is `aL ∈ (0, min ηin dm]`. -/
theorem siteWitnessRows_of_trivial {δ : NNReal} (hδ1 : δ ≤ 1) {ηin aL dm : ℝ}
    (hηin : aL ≤ ηin) (hdm : aL ≤ dm) {ι : Type*} (s : Finset ι)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) :
    (((δ : NNReal) ^ (ηin - aL) / 2 : NNReal) : ℝ≥0∞) ≤ ((1 : NNReal) : ℝ≥0∞) ∧
      stateMass ((s, T, (1 : NNReal)) : DescentState ι δ)
        ≤ 1 * stateMass ((s, T, (1 : NNReal)) : DescentState ι δ) ∧
      (1 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (dm - aL) ≤ 1 := by
  refine ⟨?_, by rw [one_mul], ?_⟩
  · have hle : (δ : NNReal) ^ (ηin - aL) ≤ 1 :=
      NNReal.rpow_le_one hδ1 (by linarith)
    have : ((δ : NNReal) ^ (ηin - aL) / 2 : NNReal) ≤ 1 :=
      le_trans (by simp) hle
    exact_mod_cast this
  · rw [one_mul]
    have h1 : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
    calc (δ : ℝ≥0∞) ^ (dm - aL) ≤ (δ : ℝ≥0∞) ^ (0 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_ge h1 (by linarith)
      _ = 1 := ENNReal.rpow_zero

end FloorRoute

/-! ## : the chain already has `2 ≤ Cu`; this exposes it -/

section ChainUniformConst

/-- **The chain's hierarchy constant is at least `4`.**

`Kakeya.ML2Core.exists_dichotomyLeft_or_window_spine_levels` hands its hierarchy back at the
*literal* constant `max C 4` (`SpineRungWiring.lean:381`, and `:532` for the `_window` sibling), so
the lower bound `exists_shadedRefinement_of_pass` asks for is already in the chain — it was simply
not exposed.  it is re-exported here rather than added as an `hsite` row. -/
theorem four_le_chainUniformConst (C : NNReal) : (4 : NNReal) ≤ max C 4 := le_max_right _ _

/-- **The projection tie.**

(c) rules that the **primitive** `4 ≤ Cu` is what gets exposed, not the derived
`2 ≤ Cu`: consumers weaken, and exporting the weaker fact would force a second re-export later.
`exists_shadedRefinement_of_pass`'s `2 ≤ Cu` is then `le_trans (by norm_num)` at the call site.

The binder is the chain's *own* hand-back type, so this can only be applied where the chain's
constant really appears — `exact four_le_of_chainHandBack 𝒲`.  It does **not** apply at an
arbitrary `Cu`, which is the tie's firing control. -/
theorem four_le_of_chainHandBack {ι : Type*} {δ : NNReal} {u' : Finset ι}
    {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {C : NNReal}
    (_𝒲 : ShadedTube.ShadedUniformTubeSet u' W (Tube.ssfGridLen δ) (max C 4)) :
    (4 : NNReal) ≤ max C 4 :=
  four_le_chainUniformConst C

end ChainUniformConst

/-! ## : pairwise essential distinctness is hereditary -/

section EssDistinctHeredity

/-- **Pairwise essential distinctness passes to every subfamily.**

(b): the chain already holds this fact on its `u`
(`SpineRungWiring.lean:118`, `hED` from `hinputs`; re-stated at `:126` as `hED'`), and hands back
`u' ⊆ u`, so every family the descent ever sees is pairwise ED — including each trial subfamily
`S ⊆ u`.  No `(D + 1)` subfamily fallback is needed and nothing is charged to `K`.

This is the heredity step the consumer applies once the chain's `_data` sibling exposes the fact on
`u`; it costs nothing. -/
theorem pairwise_essDistinct_of_subset {ι : Type*} {δ : NNReal} {u S : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hS : S ⊆ u)
    (hED : (u : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct ((T i).carrier) ((T j).carrier))) :
    (S : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) :=
  hED.mono (by exact_mod_cast hS)

/-- The same on the underlying tubes, the form `exists_shadedRefinement_of_pass` reads. -/
theorem pairwise_essDistinct_toTube_of_subset {ι : Type*} {δ : NNReal} {u S : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hS : S ⊆ u)
    (hED : (u : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (((T i).toTube).carrier) (((T j).toTube).carrier))) :
    (S : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (((T i).toTube).carrier) (((T j).toTube).carrier)) :=
  hED.mono (by exact_mod_cast hS)

end EssDistinctHeredity



end Kakeya.ML2Core

end
