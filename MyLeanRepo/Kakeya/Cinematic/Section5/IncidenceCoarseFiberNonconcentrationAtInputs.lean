import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceCoarseFiberNonconcentrationInputs

/-!
# Selected-incidence nonconcentration at one fixed ball scale

Lemma 47 is applied at the one ball radius consumed by the later cluster
pigeonhole.  This interface keeps the same regularized incidence double count
without imposing an impossible strict nonconcentration bound at arbitrarily
large radii.
-/

noncomputable section

namespace Kakeya.Cinematic

local instance incidenceCoarseFiberNonconcentrationAtDecidableEq :
    DecidableEq C2Function := Classical.decEq _

universe uβ uγ

def IncidenceCoarseFiberNonconcentrationAtStatement : Prop :=
  ∀ {β : Type uβ} {γ : Type uγ}
      [DecidableEq β] [DecidableEq γ] [Fintype β],
    IncidenceSupportDoubleCountStatement.{0, uβ, uγ} →
      ∀ (edges : Finset (C2Function × β)) (parent : β → γ)
        (level : ℕ),
        (∀ function coarse,
          incidenceDegree edges parent function coarse = 0 ∨
            (2 ^ level ≤
                incidenceDegree edges parent function coarse ∧
              incidenceDegree edges parent function coarse <
                2 ^ (level + 1))) →
        ∀ (coarse : γ),
          (incidenceRectangleSupport edges parent coarse).Nonempty →
          ∀ (testCenter : C2Function) (radius : ℝ),
            ∀ {mu₁ mu₂ coefficient logLoss : ℝ},
              0 < mu₂ →
              0 ≤ coefficient →
              1 ≤ logLoss →
              mu₁ ≤ coefficient * mu₂ →
              ((incidenceRectangleSupport edges parent coarse).card : ℝ) *
                  mu₂ ≤
                logLoss *
                  (incidenceCountOverParent edges parent coarse
                    (incidenceFunctionSupport edges parent coarse) : ℝ) →
              (∀ rectangle ∈
                  incidenceRectangleSupport edges parent coarse,
                (((incidenceRectangleFiber edges rectangle :
                      Set C2Function) ∩
                    c2Ball testCenter radius).ncard : ℝ) ≤
                  mu₁) →
              (((incidenceSupportFamily edges parent coarse).carrier ∩
                    c2Ball testCenter radius).ncard : ℝ) ≤
                (2 * logLoss) * coefficient *
                  ((incidenceSupportFamily edges parent coarse).card : ℝ)

end Kakeya.Cinematic
