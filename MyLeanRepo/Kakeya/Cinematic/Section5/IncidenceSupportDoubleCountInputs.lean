import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceDegreeRegularizationInputs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Coarse incidence supports and double counting

After regularizing the `(function, coarse parent)` incidence degree, this
module packages the retained support over one coarse parent and records the
exact edge double count.  No disjointness of the original pointwise function
fibers is assumed.
-/

namespace Kakeya.Cinematic

def incidenceFunctionSupport
    {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (edges : Finset (α × β)) (parent : β → γ)
    (coarse : γ) : Finset α :=
  (edges.filter fun edge => parent edge.2 = coarse).image Prod.fst

def incidenceRectangleFiber
    {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (edges : Finset (α × β)) (rectangle : β) : Finset α :=
  (edges.filter fun edge => edge.2 = rectangle).image Prod.fst

def incidenceRectangleSupport
    {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (edges : Finset (α × β)) (parent : β → γ)
    (coarse : γ) : Finset β :=
  (edges.filter fun edge => parent edge.2 = coarse).image Prod.snd

def incidenceCountOverParent
    {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [Fintype β]
    (edges : Finset (α × β)) (parent : β → γ)
    (coarse : γ) (test : Finset α) : ℕ :=
  (incidenceRectangleSupport edges parent coarse).sum fun rectangle =>
    ((incidenceRectangleFiber edges rectangle) ∩ test).card

def IncidenceSupportDoubleCountStatement : Prop :=
  ∀ {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype β],
    ∀ (edges : Finset (α × β)) (parent : β → γ) (level : ℕ),
      (∀ function coarse,
        incidenceDegree edges parent function coarse = 0 ∨
          (2 ^ level ≤ incidenceDegree edges parent function coarse ∧
            incidenceDegree edges parent function coarse <
              2 ^ (level + 1))) →
      ∀ (coarse : γ) (test : Finset α),
        (∀ function,
          function ∈ incidenceFunctionSupport edges parent coarse ↔
            0 < incidenceDegree edges parent function coarse) ∧
        incidenceCountOverParent edges parent coarse test =
          (incidenceFunctionSupport edges parent coarse ∩ test).sum
            (fun function =>
              incidenceDegree edges parent function coarse) ∧
        2 ^ level *
              (incidenceFunctionSupport edges parent coarse ∩ test).card ≤
          incidenceCountOverParent edges parent coarse test ∧
        ∀ bound : ℕ,
          (∀ rectangle ∈
              incidenceRectangleSupport edges parent coarse,
            ((incidenceRectangleFiber edges rectangle) ∩ test).card ≤
              bound) →
          incidenceCountOverParent edges parent coarse test ≤
            (incidenceRectangleSupport edges parent coarse).card * bound

end Kakeya.Cinematic
