import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.GeometricFullContainmentFibers
import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.PointwiseFullFiberUniformShading
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DilatedUniformTubeStructure

/-!
# Paper-facing refined Lemma 7.7

This module freezes the corrected statement of the multiscale decomposition
from Section 7.  It is intentionally independent of the historical recursive
implementation packages.

The historical generic all-real profile standing assumption is retained below
as a compatibility interface.  The final proposition is unconditional: its
implementation constructs all-real profiles directly from each final coherent
system created by the recursive proof.

The input and output covers use the Yosemite fixed-dilation API.  Their
paper-facing fibers are complete geometric containment fibers.  The auxiliary
parent maps inside `DilatedTubeCover` are used only to witness coverage; no
assigned fiber is exposed in a conclusion.

For each prescribed real scale in a bad interval, the statement constructs a
new exact-radius essentially-distinct family.  Different prescribed scales
may use independent families.  In particular, the statement neither renames a
nearby grid scale nor asks arbitrary all-real covers to form a partition or a
cross-scale hierarchy.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Fixed cover dilation used by the Section 2, Section 6, and Section 7
paper-facing interfaces. -/
def refinedLemmaSevenSevenCoverDilation : ℝ := 1000

/--
The strengthened all-real profile input used in the corrected proof.

The underlying `ApproxDilatedUniformTubeStructure` supplies actual
essentially-distinct covers and two-sided subpolynomial branching at every
real scale.  These two additional fields are precisely the accepted
Definition 2.1(iv) comparisons for complete geometric fibers.
-/
structure RefinedLemmaSevenSevenAllRealProfileInput
    {delta profileEpsilon : ℝ}
    (F : TubeFamily delta)
    (U : ApproxDilatedUniformTubeStructure
      (A := refinedLemmaSevenSevenCoverDilation)
      profileEpsilon F) : Prop where
  frostmanProfiles :
    ∀ rho : AdmissibleScale delta,
      GeometricFullContainmentFrostmanProfilesAreCUniform
        (A := refinedLemmaSevenSevenCoverDilation)
        F (U.raw.coarse rho)
        (Kakeya.realRpowENN delta (-profileEpsilon))
  deltaMaxProfiles :
    ∀ rho : AdmissibleScale delta,
      GeometricFullContainmentDeltaMaxProfilesAreCUniform
        (A := refinedLemmaSevenSevenCoverDilation)
        F (U.raw.coarse rho)
        (Kakeya.realRpowENN delta (-profileEpsilon))

/--
The all-real standing assumption used in the paper before refined Lemma 7.7.

It may be invoked on every later uniform family produced by the recursion,
not only on the original input family.  The premise is the public finite-grid
Definition 2.1 certificate on that exact family.  The conclusion supplies
actual Yosemite covers at every admissible real scale together with the
accepted Frostman and `deltaMax` profile comparisons for complete geometric
containment fibers.

The finite-grid profile exponent and root-scale threshold are chosen before
the runtime family.  A runtime finite-grid branching constant is accepted
only together with the displayed subpolynomial budget.  Thus the threshold
does not depend on a constant discovered after recursive refinement.
-/
def RefinedLemmaSevenSevenAllRealProfileStandingAssumption : Prop :=
  ∀ allRealEpsilon : ℝ, 0 < allRealEpsilon →
    ∃ gridProfileEpsilon delta₀ : ℝ,
      0 < gridProfileEpsilon ∧
      gridProfileEpsilon ≤ allRealEpsilon ∧
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : TubeFamily delta,
          F.Nonempty →
          F.IsInUnitBall →
          F.IsEssentiallyDistinct →
          ∀ hdelta_le_one : delta ≤ 1,
          ∀ branchingConstant : ENNReal,
            1 ≤ branchingConstant →
            branchingConstant ≠ ⊤ →
            branchingConstant ≤
                Kakeya.realRpowENN delta (-gridProfileEpsilon) →
              PaperGridFullFiberUniformTubeStructure
                  (A := refinedLemmaSevenSevenCoverDilation)
                  branchingConstant gridProfileEpsilon
                  F hdelta_le_one →
                ∃ U :
                    ApproxDilatedUniformTubeStructure
                      (A := refinedLemmaSevenSevenCoverDilation)
                      allRealEpsilon F,
                  RefinedLemmaSevenSevenAllRealProfileInput F U

/--
The bad Frostman alternative for one selected family.

The endpoint cover `tauToTheta` is an actual dilated cover.  At each prescribed
`rho`, `bottomToRho` makes the exact family a genuine scale-`rho` cover of the
selected bottom family, while `tauToRho` supplies the complete
`T_tau[T_rho]` fibers appearing in the paper conclusion.
-/
structure RefinedLemmaSevenSevenFrostmanBadPackage
    {N : ℕ}
    (eta : Fin (N + 1) → ℝ)
    {paperEpsilon lossEpsilon delta : ℝ}
    (F : TubeFamily delta)
    (U : ApproxDilatedUniformTubeStructure
      (A := refinedLemmaSevenSevenCoverDilation)
      lossEpsilon F) where
  level : Fin N
  tau : AdmissibleScale delta
  theta : AdmissibleScale delta
  tau_le_theta : tau.1 ≤ theta.1
  separated :
    tau.1 ≤ delta ^ paperEpsilon * theta.1
  tauToTheta :
    DilatedTubeCover refinedLemmaSevenSevenCoverDilation
      (U.raw.coarse tau) (U.raw.coarse theta)
  bottomFiberUpper :
    ∀ parent : Fin (U.raw.coarse tau).card,
      (U.raw.cover tau).fullContainmentFiberFrostmanConstant parent ≤
        Kakeya.realRpowENN delta (-lossEpsilon) *
          Kakeya.realRpowENN (tau.1 / delta)
            (eta level.castSucc)
  endpointFiberUpper :
    ∀ parent : Fin (U.raw.coarse theta).card,
      tauToTheta.fullContainmentFiberFrostmanConstant parent ≤
        Kakeya.realRpowENN delta (-lossEpsilon) *
          Kakeya.realRpowENN (theta.1 / tau.1)
            (eta level.castSucc)
  exactPrescribedLower :
    ∀ rho : AdmissibleScale delta,
      tau.1 * (theta.1 / tau.1) ^ paperEpsilon ≤ rho.1 →
      rho.1 ≤ theta.1 * (tau.1 / theta.1) ^ paperEpsilon →
        ∃ exactFamily : TubeFamily rho.1,
          exactFamily.IsEssentiallyDistinct ∧
          ∃ bottomToRho :
              DilatedTubeCover refinedLemmaSevenSevenCoverDilation
                F exactFamily,
            bottomToRho.FullContainmentFibersAreCUniform
                (Kakeya.realRpowENN delta (-lossEpsilon)) ∧
          ∃ tauToRho :
              DilatedTubeCover refinedLemmaSevenSevenCoverDilation
                (U.raw.coarse tau) exactFamily,
            ∀ parent : Fin exactFamily.card,
              Kakeya.realRpowENN delta lossEpsilon *
                  Kakeya.realRpowENN (rho.1 / tau.1)
                    (eta level.succ) ≤
                tauToRho.fullContainmentFiberFrostmanConstant parent

/--
The bad Katz--Tao alternative for one selected family.

For each prescribed `rho`, `rhoToTheta` is common to every `theta`-parent.
Thus the final quantifier order is literally
`forall rho; exists one exact family; forall T_theta`.
-/
structure RefinedLemmaSevenSevenKatzTaoBadPackage
    {N : ℕ}
    (eta : Fin (N + 1) → ℝ)
    {paperEpsilon lossEpsilon delta : ℝ}
    (F : TubeFamily delta)
    (U : ApproxDilatedUniformTubeStructure
      (A := refinedLemmaSevenSevenCoverDilation)
      lossEpsilon F) where
  level : Fin N
  tau : AdmissibleScale delta
  theta : AdmissibleScale delta
  tau_le_theta : tau.1 ≤ theta.1
  separated :
    tau.1 ≤ delta ^ paperEpsilon * theta.1
  tauToTheta :
    DilatedTubeCover refinedLemmaSevenSevenCoverDilation
      (U.raw.coarse tau) (U.raw.coarse theta)
  coarseEndpointUpper :
    (U.raw.coarse theta).toBodyFamily.deltaMax ≤
      Kakeya.realRpowENN delta (-lossEpsilon) *
        Kakeya.realRpowENN theta.1 (-(eta level.castSucc))
  endpointFiberUpper :
    ∀ parent : Fin (U.raw.coarse theta).card,
      tauToTheta.fullContainmentFiberDeltaMax parent ≤
        Kakeya.realRpowENN delta (-lossEpsilon) *
          Kakeya.realRpowENN (theta.1 / tau.1)
            (eta level.castSucc)
  exactPrescribedLower :
    ∀ rho : AdmissibleScale delta,
      tau.1 * (theta.1 / tau.1) ^ paperEpsilon ≤ rho.1 →
      rho.1 ≤ theta.1 * (tau.1 / theta.1) ^ paperEpsilon →
        ∃ exactFamily : TubeFamily rho.1,
          exactFamily.IsEssentiallyDistinct ∧
          ∃ bottomToRho :
              DilatedTubeCover refinedLemmaSevenSevenCoverDilation
                F exactFamily,
            bottomToRho.FullContainmentFibersAreCUniform
                (Kakeya.realRpowENN delta (-lossEpsilon)) ∧
          ∃ rhoToTheta :
              DilatedTubeCover refinedLemmaSevenSevenCoverDilation
                exactFamily (U.raw.coarse theta),
            ∀ parent : Fin (U.raw.coarse theta).card,
              Kakeya.realRpowENN delta lossEpsilon *
                  Kakeya.realRpowENN (theta.1 / rho.1)
                    (eta level.succ) ≤
                rhoToTheta.fullContainmentFiberDeltaMax parent

/-- Selected-family output of refined Lemma 7.7(A). -/
structure RefinedLemmaSevenSevenFrostmanOutput
    {N : ℕ}
    (eta : Fin (N + 1) → ℝ)
    {paperEpsilon lossEpsilon delta : ℝ}
    (F : TubeFamily delta) where
  selected : TubeSubfamily F
  selectedNonempty : selected.Nonempty
  cardinalityRetention :
    Kakeya.realRpowENN delta lossEpsilon * F.enncard ≤
      selected.family.enncard
  uniform :
    ApproxDilatedUniformTubeStructure
      (A := refinedLemmaSevenSevenCoverDilation)
      lossEpsilon selected.family
  profiles :
    RefinedLemmaSevenSevenAllRealProfileInput selected.family uniform
  conclusion :
    uniform.raw.IsFrostmanAtEveryScale
        (Kakeya.realRpowENN delta
          (-(5 * paperEpsilon + lossEpsilon))) ∨
      Nonempty
        (RefinedLemmaSevenSevenFrostmanBadPackage
          (paperEpsilon := paperEpsilon)
          eta selected.family uniform)

/-- Selected-family output of refined Lemma 7.7(B). -/
structure RefinedLemmaSevenSevenKatzTaoOutput
    {N : ℕ}
    (eta : Fin (N + 1) → ℝ)
    {paperEpsilon lossEpsilon delta : ℝ}
    (F : TubeFamily delta) where
  selected : TubeSubfamily F
  selectedNonempty : selected.Nonempty
  cardinalityRetention :
    Kakeya.realRpowENN delta lossEpsilon * F.enncard ≤
      selected.family.enncard
  uniform :
    ApproxDilatedUniformTubeStructure
      (A := refinedLemmaSevenSevenCoverDilation)
      lossEpsilon selected.family
  profiles :
    RefinedLemmaSevenSevenAllRealProfileInput selected.family uniform
  conclusion :
    uniform.raw.IsKatzTaoAtEveryScale
        (Kakeya.realRpowENN delta
          (-(5 * paperEpsilon + lossEpsilon))) ∨
      Nonempty
        (RefinedLemmaSevenSevenKatzTaoBadPackage
          (paperEpsilon := paperEpsilon)
          eta selected.family uniform)

/--
Stable free consequences carried by the self-uniformizing Frostman output.

The wrapper records only properties intrinsic to the public selected family
and its all-real structure.  It does not expose the recursive stopping-system
implementation used to construct them.
-/
structure RefinedLemmaSevenSevenSelfUniformizingFrostmanOutput
    {N : ℕ}
    (eta : Fin (N + 1) → ℝ)
    {paperEpsilon lossEpsilon delta : ℝ}
    (F : TubeFamily delta) where
  core :
    RefinedLemmaSevenSevenFrostmanOutput
      (paperEpsilon := paperEpsilon)
      (lossEpsilon := lossEpsilon) eta F
  selectedInUnitBall :
    core.selected.family.IsInUnitBall
  selectedEssentiallyDistinct :
    core.selected.family.IsEssentiallyDistinct
  selectedCardinalityUpper :
    core.selected.family.enncard ≤ F.enncard
  selectedBodyMassRetention :
    Kakeya.realRpowENN delta lossEpsilon *
        F.toBodyFamily.mass ≤
      core.selected.family.toBodyFamily.mass
  selectedBodyMassUpper :
    core.selected.family.toBodyFamily.mass ≤
      F.toBodyFamily.mass
  coarseNonempty :
    ∀ rho : AdmissibleScale delta,
      (core.uniform.raw.coarse rho).Nonempty
  fullContainmentUniform :
    core.uniform.raw.FullContainmentIsCUniformAtEveryScale
      (Kakeya.realRpowENN delta (-lossEpsilon))

/--
Stable free consequences carried by the self-uniformizing Katz--Tao output.
-/
structure RefinedLemmaSevenSevenSelfUniformizingKatzTaoOutput
    {N : ℕ}
    (eta : Fin (N + 1) → ℝ)
    {paperEpsilon lossEpsilon delta : ℝ}
    (F : TubeFamily delta) where
  core :
    RefinedLemmaSevenSevenKatzTaoOutput
      (paperEpsilon := paperEpsilon)
      (lossEpsilon := lossEpsilon) eta F
  selectedInUnitBall :
    core.selected.family.IsInUnitBall
  selectedEssentiallyDistinct :
    core.selected.family.IsEssentiallyDistinct
  selectedCardinalityUpper :
    core.selected.family.enncard ≤ F.enncard
  selectedBodyMassRetention :
    Kakeya.realRpowENN delta lossEpsilon *
        F.toBodyFamily.mass ≤
      core.selected.family.toBodyFamily.mass
  selectedBodyMassUpper :
    core.selected.family.toBodyFamily.mass ≤
      F.toBodyFamily.mass
  coarseNonempty :
    ∀ rho : AdmissibleScale delta,
      (core.uniform.raw.coarse rho).Nonempty
  fullContainmentUniform :
    core.uniform.raw.FullContainmentIsCUniformAtEveryScale
      (Kakeya.realRpowENN delta (-lossEpsilon))

/--
Self-uniformizing paper-facing Lemma 7.7.

No multiscale structure is required on the input family.  The conclusion
selects a large subfamily and constructs its all-real Yosemite structure and
complete-fiber profiles directly from the coherent stopping system.  The two
implications may select different large subfamilies.
-/
def RefinedLemmaSevenSevenSelfUniformizingStatement : Prop :=
  ∀ N : ℕ, 5 ≤ N →
  ∀ eta : Fin (N + 1) → ℝ,
    let paperEpsilon : ℝ := 1 / Real.sqrt N
    (∀ index, 0 < eta index) →
    (∀ index : Fin N,
      eta index.castSucc ≤
        (paperEpsilon / 100) * eta index.succ) →
    eta (Fin.last N) ≤ paperEpsilon →
    ∀ lossEpsilon : ℝ, 0 < lossEpsilon →
      ∃ delta₀ : ℝ,
        0 < delta₀ ∧
        delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : TubeFamily delta,
            F.Nonempty →
            F.IsInUnitBall →
            F.IsEssentiallyDistinct →
              (F.toBodyFamily.frostmanConstantIn unitBall.carrier ≤
                    Kakeya.realRpowENN delta (-(eta 0)) →
                Nonempty
                  (RefinedLemmaSevenSevenSelfUniformizingFrostmanOutput
                    (paperEpsilon := paperEpsilon)
                    (lossEpsilon := lossEpsilon) eta F)) ∧
              (F.toBodyFamily.IsCKatzTao
                    (Kakeya.realRpowENN delta (-(eta 0))) →
                Nonempty
                  (RefinedLemmaSevenSevenSelfUniformizingKatzTaoOutput
                    (paperEpsilon := paperEpsilon)
                    (lossEpsilon := lossEpsilon) eta F))

/--
Compatibility form of the corrected paper-facing Lemma 7.7.

The historical input all-real structure and its profiles are retained in the
interface, but the self-uniformizing conclusion constructs a new structure on
the selected output family and does not depend on those input witnesses.
-/
def RefinedLemmaSevenSevenStatement : Prop :=
  ∀ N : ℕ, 5 ≤ N →
  ∀ eta : Fin (N + 1) → ℝ,
    let paperEpsilon : ℝ := 1 / Real.sqrt N
    (∀ index, 0 < eta index) →
    (∀ index : Fin N,
      eta index.castSucc ≤
        (paperEpsilon / 100) * eta index.succ) →
    eta (Fin.last N) ≤ paperEpsilon →
    ∀ lossEpsilon : ℝ, 0 < lossEpsilon →
      ∃ profileEpsilon delta₀ : ℝ,
        0 < profileEpsilon ∧
        profileEpsilon ≤ lossEpsilon ∧
        0 < delta₀ ∧
        delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : TubeFamily delta,
            F.Nonempty →
            F.IsInUnitBall →
            F.IsEssentiallyDistinct →
            ∀ U :
                ApproxDilatedUniformTubeStructure
                  (A := refinedLemmaSevenSevenCoverDilation)
                  profileEpsilon F,
              RefinedLemmaSevenSevenAllRealProfileInput F U →
              (F.toBodyFamily.frostmanConstantIn unitBall.carrier ≤
                    Kakeya.realRpowENN delta (-(eta 0)) →
                Nonempty
                  (RefinedLemmaSevenSevenFrostmanOutput
                    (paperEpsilon := paperEpsilon)
                    (lossEpsilon := lossEpsilon) eta F)) ∧
              (F.toBodyFamily.IsCKatzTao
                    (Kakeya.realRpowENN delta (-(eta 0))) →
                Nonempty
                  (RefinedLemmaSevenSevenKatzTaoOutput
                    (paperEpsilon := paperEpsilon)
                    (lossEpsilon := lossEpsilon) eta F))

/--
Compatibility form of refined Lemma 7.7 with the historical generic
all-real-profile standing assumption.  The unconditional theorem no longer
uses this premise.
-/
def RefinedLemmaSevenSevenConditionalStatement : Prop :=
  RefinedLemmaSevenSevenAllRealProfileStandingAssumption →
    RefinedLemmaSevenSevenStatement

end Kakeya.Streamlined
