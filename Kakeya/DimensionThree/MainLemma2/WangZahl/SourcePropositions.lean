/-
Wang--Zahl propositions and the assembly of the Katz--Tao estimate.

Source: `blueprint/src/WZ2/250224e_K3.tex`
  * `equivDE` (Proposition 1.6, Section `cEIffcDSec`)
  * `improvingProp` (Proposition 1.7, Section `Multi-scale analysis`)
  * `WolffHairbrush` (Proposition 1.10, Appendix `WolffHairbrushSec`)
  * `cDAndcEAreTrue` (Theorem 1.11)

The sigma descent of Theorem `cDAndcEAreTrue` is
`assertionD_zero_of_descent`; its omega closure is `assertionD_of_forall_gt`.
The passage from `AssertionD 0 0` to `KatzTaoEstimate` is
`katzTaoEstimate_of_assertionD_of_frostmanOrDone`.
-/
module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.CurrencyLowerBound
public import Kakeya.DimensionThree.MainLemma2.WangZahl.EquivDE
public import Kakeya.DimensionThree.MainLemma2.WangZahl.SigmaCalculus
public import Kakeya.DimensionThree.MainLemma2.WangZahl.WZMultiScale
public import Kakeya.DimensionThree.MainLemma2.WangZahl.WolffHairbrush
public import Kakeya.DimensionThree.MainLemma2.WangZahl.TopLevelWrapper

@[expose] public section

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### The remaining source obligations -/

/-- **Obligation 1** (elementary, Section 1.3 of the source).

The *lower* size bound on the Wang--Zahl currency `X = (#T)|T|^{1/2}`: a slab
of thickness `|T|^{1/2}` containing one tube of the family gives
`FS(T) (#T) |T|^{1/2} >= 1`, hence `X >= C⁻¹ delta^{eta}` under the Frostman
hypothesis `FS(T) <= delta^{-eta}`.

This is a one-line estimate in the source.  The two supporting pieces --
the construction of a `SlabTestSet` of thickness `delta` containing a
prescribed `delta`-tube of the unit ball, and the volume upper bound
`|W| <= W.thickness * |B(0,2)|` for `SlabTestSet.carrier` -- are proved in
`Kakeya.DimensionThree.MainLemma2.WangZahl.CurrencyLowerBound`.

The companion *upper* bound is `exists_currencyUpperBound`. -/
theorem exists_currencyLowerBound :
    ∃ C : NNReal, 1 ≤ C ∧ CurrencyLowerBound.{u} C :=
  exists_currencyLowerBound_aux.{u}

/-- Both currency bounds, from the proved upper bound and Obligation 1. -/
theorem exists_currencyBounds : ∃ C : NNReal, 1 ≤ C ∧ CurrencyBounds.{u} C := by
  obtain ⟨C₁, hC₁, hlow⟩ := exists_currencyLowerBound.{u}
  obtain ⟨C₂, hC₂, hup⟩ := exists_currencyUpperBound.{u}
  exact ⟨max C₁ C₂, le_trans hC₁ (le_max_left _ _),
    hlow.mono (le_max_left _ _), hup.mono (le_max_right _ _)⟩









/-! ### Everything below is proved from the five obligations -/











end

end Kakeya.WangZahl
