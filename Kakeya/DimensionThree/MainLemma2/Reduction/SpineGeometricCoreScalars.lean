/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFourFactorRowsSite
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteWitnessProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineHfacProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDichotomyInputs

/-!
# The scalar ledger of `Kakeya.ML2Core.GeometricCoreSupplyAnalytic`

`Kakeya.ML2Core.GeometricCoreSupplyAnalytic` (`Reduction/SpineFourFactorRowsSite.lean:1834-1851`)
is a package of **sixteen** scalar conjuncts around **three** non-scalar rows.  This leaf
discharges every scalar conjunct by an explicit choice and discharges the
`Kakeya.ML2Core.SiteWitness` row by `Kakeya.ML2Core.siteWitness_of_scalars`, leaving exactly two
rows open:

* `Kakeya.ML2Core.SiteAnalyticRows`   -- the five analytic rows (outer package, inner factor,
  new-parent factor, middle factor, `hlead`);
* `Kakeya.ML2Core.RefinedFloorPayload` -- the payload row.

`Kakeya.ML2Core.GeometricCoreSupplySited` is deliberately **not** on this path: B15 shows
`Kakeya.ML2Core.FourFactorRowsAt`'s multiplicity rows are unsuppliable for every shading, so the
sited supply stays as the record and the closure runs through
`Kakeya.ML2Core.geometricCoreAt_of_analyticSupply`.

## The margin is the gain

`Kakeya.ML2Core.defectMargin β ϖ ε₁ gain dens = Kakeya.ML2Spine.spineNu β ϖ ε₁ gain dens` by
`rfl` (`Kakeya.ML2Core.defectMargin_eq`, `Reduction/SpineDefectPotential.lean:542-555`).  So the
budget margin `dm` of the site row and the gain `ν` of the loss ledger are the **same real
number**, and the whole assignment below can be written in `dm` alone.  This is what makes a
consistent choice possible at all: the `SiteWitness` row spends `η + aL` out of `dm`, while the
four-loss ledger spends `θ₂ + ηin + εf + εp + εc + κ'` out of `12ν/5` -- the same `ν`.

## The assignment

Refined source `260115_kakeyadetailedproofv3_revised_detailed.tex` l.5802-5814 fixes the data
first and only then chooses `ν₀, η₀`; -D records that the input Katz--Tao
exponent `η` is therefore chosen **after** the margin `dm`.  Accordingly `dm` is read off the
data and the two site exponents are cut out of it:

```
aL := dm / 2        η := dm / 4        Cu₀ := ShadedTube.ssfUniformConst 3
gm := fun X => 47 * X / 5
```

so that `η + aL = 3dm/4 < dm` with a quarter of the margin left unspent, and
`dm - aL = dm/2 = ν/2 ≤ β/96000 ≤ β/48000` sits strictly inside the `(G₁)` budget of
`Kakeya.ML2Core.defectMargin_le_budget`.  `aL < dm` is stated explicitly (-D) as the third
conjunct of `Kakeya.ML2Core.twoRows_scalar_ledger`.

## What stays open

`ε₁`, `C`, `Kl`, `cl`, `ηin`, `ηL`, `η'`, `εf`, `εp`, `εc`, `κc`, `κ'`, `θ₂` are **not** fixed
here.  They remain bound variables of the hypothesis `hrows`, because each of them is an argument
of one of the two open rows and instantiating them is the other hands' business.  Only `η`, `aL`,
`Cu₀` and `gm` -- the four scalars no row constrains from outside -- are chosen.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Core

section Ledger

/-- **The scalar ledger of the assignment `aL := dm/2`, `η := dm/4`.**

Every inequality the analytic supply asks of the two site exponents, at the chosen values, from
the positivity of the data alone.  The third conjunct is `aL < dm`, stated explicitly as
-D requires; the fourth is the `(G₁)` cap `dm - aL ≤ β/48000`
(`Kakeya.ML2Inputs.spineNu_le_div_48000`, `Reduction/SpineDichotomyInputs.lean:200`). -/
theorem twoRows_scalar_ledger {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ : ℝ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ : ℝ, 0 < ζ → 0 < dens ζ) :
    0 < defectMargin β ϖ ε₁ gain dens ∧
    0 < defectMargin β ϖ ε₁ gain dens / 2 ∧
    defectMargin β ϖ ε₁ gain dens / 2 < defectMargin β ϖ ε₁ gain dens ∧
    defectMargin β ϖ ε₁ gain dens - defectMargin β ϖ ε₁ gain dens / 2 ≤ β / 48000 ∧
    defectMargin β ϖ ε₁ gain dens / 4 + defectMargin β ϖ ε₁ gain dens / 2
      < defectMargin β ϖ ε₁ gain dens ∧
    0 < defectMargin β ϖ ε₁ gain dens / 4 ∧
    defectMargin β ϖ ε₁ gain dens / 4 ≤ 1 := by
  have hdm0 : 0 < defectMargin β ϖ ε₁ gain dens := defectMargin_pos hβ0 hϖ hε₁ hgain hdens
  have hν48 : ML2Spine.spineNu β ϖ ε₁ gain dens ≤ β / 48000 :=
    ML2Inputs.spineNu_le_div_48000 hβ0 hβ1 hϖ hε₁ hgain hdens
  rw [defectMargin_eq] at hdm0 ⊢
  refine ⟨hdm0, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

end Ledger

section ThreeRows

/-- **The analytic supply, with every scalar conjunct discharged and only two rows left.**

`Kakeya.ML2Core.geometricCoreAt_of_analyticSupply` (`SpineFourFactorRowsSite.lean:1855`) consumes
sixteen scalar conjuncts and three non-scalar rows.  Here the scalars are chosen -- and the
`Kakeya.ML2Core.SiteWitness` row produced by `Kakeya.ML2Core.siteWitness_of_scalars`
(`SpineSiteWitnessProducer.lean:198`) -- so that the hypothesis `hrows` carries the two
open rows and nothing else geometric.

The three conjuncts `0 < ϖ`, `0 < gain ζ`, `0 < dens ζ` are **not** hypotheses: they are read off
the `Kakeya.ML2Assembly.Lemma91ParamsAt` already in scope (`window_pos`, `gain_pos`, `dens_pos`,
`Reduction/AssemblyPointwise.lean:138-146`).  's C1 discipline forbids adding
positivity that the interface already supplies.

The three scalar side conditions on the open exponents are the only additions:

* `hsmall`, the four-loss ledger `θ₂ + ηin + εf + εp + εc + κ' ≤ 12ν/5` -- condition L2, at the sharp ambient gain `gm X = 47X/5`
  (`Kakeya.ML2Core.hexp_of_sharp_gain_four`, source l.4455-4459);
* `hladder`, `3dm/4 ≤ ηin` -- the `lam`-ladder row of `Kakeya.ML2Core.SiteWitness`, which needs
  `η + aL ≤ ηin` and at the chosen `η, aL` that is exactly `3dm/4 ≤ ηin`;
* `hηL`, `ηin ≤ ηL` -- B15's one new scalar row, relating the two exponents that
  `Kakeya.ML2Core.SiteAnalyticRows` itself binds.

All three are consequences the *other* hands must deliver alongside their rows, which is why they
sit under the same binders as the rows rather than at the top of the statement. -/
theorem geometricCoreAt_of_three_rows.{v'} (K' : ℕ)
    (hrows : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{v'} β ϖ gain dens →
      KatzTaoEstimate.{v'} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{v'} (EuclideanSpace ℝ (Fin 3)) β →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧
        ∃ (C : NNReal) (Kl cl : ℕ) (ηin ηL η' εf εp εc κc κ' θ₂ : ℝ),
          1 ≤ C ∧ 0 < κc ∧ 0 < κ' ∧ 0 < θ₂ ∧ 0 < εp ∧ ηin ≤ ηL ∧
          (∀ k : ℕ, k < ML2Spine.spineCount ϖ ε₁ →
            κc + ML2Spine.spineRung β ϖ ε₁ gain dens k ≤ 2 * η') ∧
          θ₂ + ηin + εf + εp + εc + κ'
            ≤ 12 * ML2Spine.spineNu β ϖ ε₁ gain dens / 5 ∧
          3 * defectMargin β ϖ ε₁ gain dens / 4 ≤ ηin ∧
          SiteAnalyticRows.{v'} β ϖ ε₁ ηin η' εf εp εc κc ηL (fun X => 47 * X / 5) gain dens
            (ShadedTube.ssfUniformConst 3) ∧
          RefinedFloorPayload.{v'} (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens
            (polylogLoss K')) :
    ML2Assembly.GeometricCoreAt.{v'} := by
  refine geometricCoreAt_of_analyticSupply.{v'} K' ?_
  intro β ϖ gain dens hβ0 hβ1 hp hKT hF
  obtain ⟨ε₁, hε₁, C, Kl, cl, ηin, ηL, η', εf, εp, εc, κc, κ', θ₂,
    hC, hκc, hκ', hθ₂, hεp, hηL, hres, hsmall, hladder, hsite, hpay⟩ :=
    hrows β ϖ gain dens hβ0 hβ1 hp hKT hF
  have hϖ : 0 < ϖ := hp.window_pos
  have hgain : ∀ ζ : ℝ, 0 < ζ → 0 < gain ζ := hp.gain_pos
  have hdens : ∀ ζ : ℝ, 0 < ζ → 0 < dens ζ := hp.dens_pos
  obtain ⟨hdm0, haL0, haLdm, hcap, hbudget, hη0, hη1⟩ :=
    twoRows_scalar_ledger hβ0 hβ1 hϖ hε₁ hgain hdens
  refine ⟨hϖ, hgain, hdens, ε₁, hε₁, defectMargin β ϖ ε₁ gain dens / 4, hη0, hη1,
    ShadedTube.ssfUniformConst 3, C, Kl, cl, ηin, defectMargin β ϖ ε₁ gain dens / 2, η',
    εf, εp, εc, κc, κ', θ₂, ηL, (fun X => 47 * X / 5), haL0, hC,
    ShadedTube.one_le_ssfUniformConst 3, hκc, hκ', hθ₂, hεp, hηL, hres, ?_, hsite, ?_, hpay⟩
  · -- the four-loss budget, at the sharp ambient gain
    simpa using hexp_of_sharp_gain_four (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain) (dens := dens)
      hsmall
  · -- the site witness, from the scalar producer
    exact siteWitness_of_scalars.{v'} hη1 haL0 (by linarith) hbudget

end ThreeRows

end Kakeya.ML2Core
