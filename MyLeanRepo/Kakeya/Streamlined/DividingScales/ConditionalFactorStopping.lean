import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalFactorStates

/-!
# Stopping logic for conditional factor lists

This module isolates the finite classical logic of the Section 7 stopping
time from its Frostman geometry.  A factor scope is either short, already has
the central lower profile required by the bad alternative, or has a concrete
central scale where the profile is small and the factor can be split.

The scalar `profile P q` is left abstract.  The geometric layer instantiates
it with a maximum over all represented conditional branches.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace FrostmanConditionalFactorScope

variable {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := C) F hdelta_le_one}

/-- A factor has the separated relative scale used by the bad alternative. -/
def IsSeparated
    (P : FrostmanConditionalFactorScope U)
    (epsilon : ℝ) : Prop :=
  P.fineScale ≤ delta ^ epsilon * P.coarseScale

/-- A factor is short enough for the terminal all-scale interpolation. -/
def IsShort
    (P : FrostmanConditionalFactorScope U)
    (epsilon : ℝ) : Prop :=
  delta ^ epsilon * P.coarseScale ≤ P.fineScale

/-- An intermediate absolute scale lies in the paper's central window. -/
def IsCentral
    (P : FrostmanConditionalFactorScope U)
    (epsilon : ℝ)
    (q : UniformScaleIndex delta) : Prop :=
  let xi := (uniformScale delta hdelta_le_one q).1
  P.fineScale ≤ xi ∧
    xi ≤ P.coarseScale ∧
    P.fineScale * (P.coarseScale / P.fineScale) ^ epsilon ≤ xi ∧
    xi ≤ P.coarseScale *
      (P.fineScale / P.coarseScale) ^ epsilon

/--
The central lower-profile obstruction on one factor scope.

The profile is abstract so this statement can be reused for assigned
Frostman constants and later for Katz--Tao `deltaMax`.
-/
def Stops
    (P : FrostmanConditionalFactorScope U)
    (profile :
      FrostmanConditionalFactorScope U →
        UniformScaleIndex delta → ENNReal)
    (nextExponent epsilon : ℝ) : Prop :=
  P.IsSeparated epsilon ∧
    ∀ q : UniformScaleIndex delta,
      P.IsCentral epsilon q →
        Kakeya.realRpowENN
            ((uniformScale delta hdelta_le_one q).1 / P.fineScale)
            nextExponent ≤
          profile P q

/-- One central scale at which the factor profile is small. -/
structure SplitCandidate
    (P : FrostmanConditionalFactorScope U)
    (profile :
      FrostmanConditionalFactorScope U →
        UniformScaleIndex delta → ENNReal)
    (nextExponent epsilon : ℝ) where
  middle : UniformScaleIndex delta
  central : P.IsCentral epsilon middle
  profile_small :
    profile P middle <
      Kakeya.realRpowENN
        ((uniformScale delta hdelta_le_one middle).1 / P.fineScale)
        nextExponent

/--
Every separated factor either stops with the central lower profile or has a
concrete central split candidate.
-/
lemma stops_or_splitCandidate
    (P : FrostmanConditionalFactorScope U)
    (profile :
      FrostmanConditionalFactorScope U →
        UniformScaleIndex delta → ENNReal)
    (nextExponent epsilon : ℝ)
    (hseparated : P.IsSeparated epsilon) :
    P.Stops profile nextExponent epsilon ∨
      Nonempty (P.SplitCandidate profile nextExponent epsilon) := by
  by_cases hcentral :
      ∀ q : UniformScaleIndex delta,
        P.IsCentral epsilon q →
          Kakeya.realRpowENN
              ((uniformScale delta hdelta_le_one q).1 / P.fineScale)
              nextExponent ≤
            profile P q
  · exact Or.inl ⟨hseparated, hcentral⟩
  · right
    push Not at hcentral
    rcases hcentral with ⟨q, hqcentral, hsmall⟩
    exact ⟨{
      middle := q
      central := hqcentral
      profile_small := hsmall
    }⟩

end FrostmanConditionalFactorScope

namespace FrostmanConditionalFactorState

variable {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := C) F hdelta_le_one}

/-- Every current factor is short. -/
def AllShort
    {level : ℕ}
    (S : FrostmanConditionalFactorState U level)
    (epsilon : ℝ) : Prop :=
  ∀ P ∈ S.factors, P.IsShort epsilon

/-- One current factor has already stopped with a central obstruction. -/
def HasStopped
    {level : ℕ}
    (S : FrostmanConditionalFactorState U level)
    (profile :
      FrostmanConditionalFactorScope U →
        UniformScaleIndex delta → ENNReal)
    (nextExponent epsilon : ℝ) : Prop :=
  ∃ P ∈ S.factors, P.Stops profile nextExponent epsilon

/-- One displayed factor has a concrete split candidate. -/
structure CanSplit
    {level : ℕ}
    (S : FrostmanConditionalFactorState U level)
    (profile :
      FrostmanConditionalFactorScope U →
        UniformScaleIndex delta → ENNReal)
    (nextExponent epsilon : ℝ) where
  before : List (FrostmanConditionalFactorScope U)
  selected : FrostmanConditionalFactorScope U
  after : List (FrostmanConditionalFactorScope U)
  factors_eq : S.factors = before ++ selected :: after
  separated : selected.IsSeparated epsilon
  candidate :
    selected.SplitCandidate profile nextExponent epsilon

/--
Every factor list is terminal-short, has a stopped factor, or has one
explicitly displayed factor that can be split.
-/
lemma allShort_or_hasStopped_or_canSplit
    {level : ℕ}
    (S : FrostmanConditionalFactorState U level)
    (profile :
      FrostmanConditionalFactorScope U →
        UniformScaleIndex delta → ENNReal)
    (nextExponent epsilon : ℝ) :
    S.AllShort epsilon ∨
      S.HasStopped profile nextExponent epsilon ∨
      Nonempty (S.CanSplit profile nextExponent epsilon) := by
  classical
  by_cases hall : S.AllShort epsilon
  · exact Or.inl hall
  · right
    rw [AllShort] at hall
    push Not at hall
    rcases hall with ⟨P, hP, hnotShort⟩
    have hseparated : P.IsSeparated epsilon := by
      exact le_of_not_ge hnotShort
    rcases P.stops_or_splitCandidate
        profile nextExponent epsilon hseparated with
      hstops | hcandidate
    · exact Or.inl ⟨P, hP, hstops⟩
    · right
      rcases hcandidate with ⟨candidate⟩
      rcases List.mem_iff_append.mp hP with
        ⟨before, after, hdecomp⟩
      exact ⟨{
        before := before
        selected := P
        after := after
        factors_eq := hdecomp
        separated := hseparated
        candidate := candidate
      }⟩

/-- A split candidate supplies the endpoint ordering required by `split`. -/
def splitOfCanSplit
    {level : ℕ}
    (S : FrostmanConditionalFactorState U level)
    (hdelta : 0 < delta)
    (hlevel : level < depth)
    (profile :
      FrostmanConditionalFactorScope U →
        UniformScaleIndex delta → ENNReal)
    (nextExponent epsilon : ℝ)
    (candidate : S.CanSplit profile nextExponent epsilon) :
    FrostmanConditionalFactorState U (level + 1) := by
  exact S.split hdelta hlevel
    candidate.before candidate.after candidate.selected
    candidate.factors_eq candidate.candidate.middle
    candidate.candidate.central.1
    candidate.candidate.central.2.1

end FrostmanConditionalFactorState

end Kakeya.Streamlined
