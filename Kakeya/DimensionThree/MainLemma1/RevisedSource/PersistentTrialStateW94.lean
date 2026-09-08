module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.LiteralDetailedTrialW94

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

/-- The base is fixed once after the independently paid initial normalization. -/
structure FixedBaseReserveW94 {iota : Type uI} {delta : NNReal}
    (B : Finset iota) (V : iota -> ShadedTube delta E) where
  nonempty : B.Nonempty
  delta_pos : 0 < delta
  delta_lt_one : delta < 1
  carrierVolume : ENNReal
  carrierVolume_pos : 0 < carrierVolume
  carrierVolume_finite : carrierVolume < ⊤
  common_volume : ∀ i ∈ B, volume (V i).carrier = carrierVolume
  ball : ∀ i ∈ B, (V i).carrier ⊆ Metric.closedBall 0 1
  lambda0 : ENNReal
  lambda0_pos : 0 < lambda0
  lambda0_finite : lambda0 < ⊤
  fullness : lambda0 <= fullness' B (fun i => (V i).toShadedBody)
  F0 : ENNReal
  F0_finite : F0 < ⊤
  frostman : frostmanConstIn B (fun i => (V i).toConvexSpaceBody)
    ConvexSpaceBody.closedUnitBall <= F0

/-- A real current family and its cumulative retained mass. There is no
fresh canonical net, arbitrary profile, or reset fullness exponent here. -/
structure RetainedStateW94 {iota : Type uI} {delta : NNReal}
    (B : Finset iota) (V : iota -> ShadedTube delta E) where
  active : Finset iota
  shading : iota -> ShadedTube delta E
  active_nonempty : active.Nonempty
  active_subset : active ⊆ B
  same_tube : ∀ i ∈ active, (shading i).toTube = (V i).toTube
  subshade : ∀ i ∈ active, (shading i).shade ⊆ (V i).shade
  retained : ENNReal
  retained_pos : 0 < retained
  retained_finite : retained < ⊤
  mass_retention : retained * (∑ i ∈ B, volume (V i).shade) <=
    ∑ i ∈ active, volume (shading i).shade

/-- All states are evaluated against this same externally fixed base net. -/
def persistentProfileW94 {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (state : RetainedStateW94 B V) (q ell : Fin (M + 1)) : Real :=
  literalProfileCoordW87 U0 state.active q ell

/-- The exact integer-ceil selection cost is kept, and prior trial loss is
paid separately. Thus neither the factor-eight comparison nor Ydagger loss
is hidden in a real-valued three-Lambda denominator. -/
def actualPaidPassCostW94 (delta d : NNReal) (M CM Ktr : Nat)
    (Cpass : NNReal) : ENNReal :=
  (Cpass : ENNReal) * fullPassDenominatorW87 delta M CM /
    trialRetainedFractionW94 d Ktr

/-- Output witness for P4-P5. Every payment is on the actual intermediate
fine family, and the decreasing coordinate uses the persistent base net. -/
structure PaidDropTransitionW94 {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (current next : RetainedStateW94 B V) (CM : Nat) (Cpass : NNReal)
    (cFlat : Real) where
  trialScale : NNReal
  trialScale_lower : delta <= trialScale
  trialScale_lt_one : trialScale < 1
  Ktr : Nat
  Ktr_pos : 1 <= Ktr
  daggerFamily : Finset iota
  Ydagger : iota -> ShadedTube delta E
  dagger_subset : daggerFamily ⊆ current.active
  dagger_same_tube : ∀ i ∈ daggerFamily, (Ydagger i).toTube = (current.shading i).toTube
  dagger_subshade : ∀ i ∈ daggerFamily, (Ydagger i).shade ⊆ (current.shading i).shade
  prior_trial_retention : trialRetainedFractionW94 trialScale Ktr *
    (∑ i ∈ current.active, volume (current.shading i).shade) <=
      ∑ i ∈ daggerFamily, volume (Ydagger i).shade
  next_subset : next.active ⊆ daggerFamily
  next_subshade : ∀ i ∈ next.active, (next.shading i).shade ⊆ (Ydagger i).shade
  selector_retention : ((Cpass : ENNReal) * fullPassDenominatorW87 delta M CM)⁻¹ *
    (∑ i ∈ daggerFamily, volume (Ydagger i).shade) <=
      ∑ i ∈ next.active, volume (next.shading i).shade
  coefficient_paid : current.retained /
    actualPaidPassCostW94 delta trialScale M CM Ktr Cpass <= next.retained
  drop_q : Fin (M + 1)
  drop_ell : Fin (M + 1)
  profile_drop : persistentProfileW94 U0 next drop_q drop_ell + cFlat <=
    persistentProfileW94 U0 current drop_q drop_ell

/-- A constructed trace may record these witnesses. No existence theorem
takes a supplied trace or universal pass callback as an outer input. -/
structure ActualDropTraceW94 {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (initial : RetainedStateW94 B V) (CM : Nat) (Cpass : NNReal) (cFlat : Real) where
  length : Nat
  state : Fin (length + 1) -> RetainedStateW94 B V
  head : state 0 = initial
  step : ∀ n : Fin length,
    PaidDropTransitionW94 U0 (state (Fin.castSucc n)) (state (Fin.succ n)) CM Cpass cFlat

end

end Kakeya.ml1Boot.TrialRestartW94
