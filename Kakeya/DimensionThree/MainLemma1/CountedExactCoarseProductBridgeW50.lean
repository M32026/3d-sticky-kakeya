module

public import Kakeya.DimensionThree.MainLemma1.CountedExactCoarseW50

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50CountedExactCoarseProductBridge

noncomputable section

universe u v w z

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-! The algebraic port used by the counted endpoint assembly.  The first-pass estimate
is allowed to use an arbitrary index type; only the exact honest output is fixed. -/
theorem honestProduct_compose_first_pass_w50
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {α : Type z} [DecidableEq ι]
    {delta rho c productConstant A : NNReal}
    {F : ShadedBody.FactorFamily E ι κ}
    {T : ι → ShadedTube delta E} {Tρ : κ → Tube rho E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι → ShadedTube delta E}
    {coarseShade : κ → ShadedTube rho E} {parent : ι → κ}
    {S : Finset α} {VS : α → ShadedBody E}
    (hOut : Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
      (c := c) F T Tρ fineSet coarseSet fineShade coarseShade parent productConstant)
    (hfirst : ∀ j ∈ coarseSet,
      ShadedBody.multiplicity S VS ≤
        (A : ENNReal) * ShadedBody.multiplicity F.innerSet F.innerBody) :
    ∀ j ∈ coarseSet,
      ShadedBody.multiplicity S VS ≤
        (A : ENNReal) * (productConstant : ENNReal) *
          ShadedBody.multiplicity coarseSet
            (fun k ↦ (coarseShade k).toShadedBody) *
          ShadedBody.multiplicity
            (Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent j)
            (fun i ↦ (fineShade i).toShadedBody) := by
  intro j hj
  calc
    ShadedBody.multiplicity S VS ≤
        (A : ENNReal) * ShadedBody.multiplicity F.innerSet F.innerBody :=
      hfirst j hj
    _ ≤ (A : ENNReal) *
        ((productConstant : ENNReal) *
          ShadedBody.multiplicity coarseSet
            (fun k ↦ (coarseShade k).toShadedBody) *
          ShadedBody.multiplicity
            (Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent j)
            (fun i ↦ (fineShade i).toShadedBody)) := by
      exact mul_le_mul_left' (hOut.product j hj) (A : ENNReal)
    _ = (A : ENNReal) * (productConstant : ENNReal) *
          ShadedBody.multiplicity coarseSet
            (fun k ↦ (coarseShade k).toShadedBody) *
          ShadedBody.multiplicity
            (Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent j)
            (fun i ↦ (fineShade i).toShadedBody) := by ring

/-! Variant matching a first pass that has already named the source and fine factors.
The two supplied transport inequalities are intentionally explicit: this keeps the theorem
usable with either the raw source or a complete-fibre refinement, while the final witness is
still exactly the one carried by `hOut`. -/
theorem honestProduct_compose_first_pass_named_w50
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {α : Type z} [DecidableEq ι]
    {delta rho c productConstant A : NNReal}
    {F : ShadedBody.FactorFamily E ι κ}
    {T : ι → ShadedTube delta E} {Tρ : κ → Tube rho E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι → ShadedTube delta E}
    {coarseShade : κ → ShadedTube rho E} {parent : ι → κ}
    {S : Finset α} {VS : α → ShadedBody E}
    {source0 : Finset ι} {V0 : ι → ShadedBody E}
    {fine0 : Finset ι} {W0 : ι → ShadedBody E}
    (hOut : Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
      (c := c) F T Tρ fineSet coarseSet fineShade coarseShade parent productConstant)
    (hsource0 : ShadedBody.multiplicity source0 V0 ≤
      ShadedBody.multiplicity F.innerSet F.innerBody)
    (hfine0 : ∀ j ∈ coarseSet,
      ShadedBody.multiplicity fine0 W0 ≤
        (1 : ENNReal))
    (hfirst : ∀ j ∈ coarseSet,
      ShadedBody.multiplicity S VS ≤
        (A : ENNReal) * ShadedBody.multiplicity source0 V0 *
          ShadedBody.multiplicity fine0 W0) :
    ∀ j ∈ coarseSet,
      ShadedBody.multiplicity S VS ≤
        (A : ENNReal) * (productConstant : ENNReal) *
          ShadedBody.multiplicity coarseSet
            (fun k ↦ (coarseShade k).toShadedBody) *
          ShadedBody.multiplicity
            (Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent j)
            (fun i ↦ (fineShade i).toShadedBody) := by
  intro j hj
  have hfirst' : ShadedBody.multiplicity S VS ≤
      (A : ENNReal) * ShadedBody.multiplicity F.innerSet F.innerBody := by
    calc
      ShadedBody.multiplicity S VS ≤
          (A : ENNReal) * ShadedBody.multiplicity source0 V0 *
            ShadedBody.multiplicity fine0 W0 := hfirst j hj
      _ ≤ (A : ENNReal) * ShadedBody.multiplicity F.innerSet F.innerBody *
            (1 : ENNReal) := by
        gcongr
        exact hfine0 j hj
      _ = (A : ENNReal) * ShadedBody.multiplicity F.innerSet F.innerBody := by
        simp
  exact honestProduct_compose_first_pass_w50 hOut
    (fun k hk ↦ hfirst' ) j hj

end
end Kakeya.ml1Boot.W50CountedExactCoarseProductBridge

#print axioms Kakeya.ml1Boot.W50CountedExactCoarseProductBridge.honestProduct_compose_first_pass_w50
#print axioms Kakeya.ml1Boot.W50CountedExactCoarseProductBridge.honestProduct_compose_first_pass_named_w50
