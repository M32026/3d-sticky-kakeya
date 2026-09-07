import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceSupportDoubleCountInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Non-concentration from a regularized incidence graph

This is the direct interface between the selected function--fine-rectangle
incidence graph and the abstract counting core of PYZ Lemma 47.  The
regularized degree is kept distinct from both the earlier retained fine-fiber
lower bound and the later common coarse tangent lower bound.
-/

noncomputable section

namespace Kakeya.Cinematic

local instance : DecidableEq C2Function := Classical.decEq _

universe uβ uγ

def incidenceSupportFamily
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (edges : Finset (C2Function × β)) (parent : β → γ)
    (coarse : γ) : FiniteFunctionFamily where
  carrier := incidenceFunctionSupport edges parent coarse
  finite := (incidenceFunctionSupport edges parent coarse).finite_toSet

def incidenceActiveRectangle
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (edges : Finset (C2Function × β)) (parent : β → γ)
    (coarse : γ)
    (index : Fin (incidenceRectangleSupport edges parent coarse).card) : β :=
  ((Finset.equivFin
    (incidenceRectangleSupport edges parent coarse)).symm index).val

def incidenceActiveFiberFamily
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (edges : Finset (C2Function × β)) (parent : β → γ)
    (coarse : γ)
    (index : Fin (incidenceRectangleSupport edges parent coarse).card) :
    FiniteFunctionFamily where
  carrier :=
    incidenceRectangleFiber edges
      (incidenceActiveRectangle edges parent coarse index)
  finite :=
    (incidenceRectangleFiber edges
      (incidenceActiveRectangle edges parent coarse index)).finite_toSet

def IncidenceCoarseFiberNonconcentrationStatement : Prop :=
  ∀ {β : Type uβ} {γ : Type uγ}
      [DecidableEq β] [DecidableEq γ] [Fintype β],
    IncidenceSupportDoubleCountStatement.{0, uβ, uγ} →
      CoarseFiberNonconcentrationStatement →
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
              ∀ center radius,
                (((incidenceRectangleFiber edges rectangle : Set C2Function) ∩
                    c2Ball center radius).ncard : ℝ) ≤ mu₁) →
            ∀ center radius,
              (((incidenceSupportFamily edges parent coarse).carrier ∩
                  c2Ball center radius).ncard : ℝ) ≤
                (2 * logLoss) * coefficient *
                  ((incidenceSupportFamily edges parent coarse).card : ℝ)

end Kakeya.Cinematic
