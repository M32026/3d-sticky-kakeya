import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.EpsilonAvoidance

/-!
# Simultaneous avoidance for the two directional shifts

Choose one directional amplitude that preserves the no-exact-tangency
certificate both when it is added to the white family and when it is
subtracted from the white family.
-/

namespace Kakeya.Cinematic

noncomputable section

local instance instDecidableEqC2FunctionShiftAvoid : DecidableEq C2Function :=
  Classical.decEq _

def BidirectionalShiftAvoidanceStatement : Prop :=
  ∀ (W B F : FiniteFunctionFamily) (I : ParameterInterval)
      (shift0 : C2Function → ℝ),
    F.carrier = W.carrier ∪ B.carrier →
    F.HasNoExactTangenciesOn I shift0 →
    ∀ epsilonLow epsilonHigh : ℝ,
      epsilonLow < epsilonHigh →
      ∃ epsilon : ℝ,
        epsilonLow < epsilon ∧
        epsilon < epsilonHigh ∧
        let shiftUp : C2Function → ℝ := fun f =>
          if f ∈ W.toFinset then epsilon + shift0 f else shift0 f
        let shiftDown : C2Function → ℝ := fun f =>
          if f ∈ W.toFinset then -epsilon + shift0 f else shift0 f
        F.HasNoExactTangenciesOn I shiftUp ∧
          F.HasNoExactTangenciesOn I shiftDown

end

end Kakeya.Cinematic
