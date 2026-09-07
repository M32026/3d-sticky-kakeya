import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Lenses

/-!
# Indexed graph-lens counting input

This is the finite packaging layer used after one directional lens has been
chosen for every retained rectangle. Pairwise non-overlap forces the indexed
lens map to be injective, so the Marcus--Tardos lens bound controls the number
of retained indices with the same constant.
-/

namespace Kakeya.Cinematic

def IndexedGraphLensCountStatement : Prop :=
  ∀ {C : ℝ},
    (∀ curves : Finset C2Function,
      IsGraphPseudoCircleFamily curves →
      ∀ lenses : Finset GraphLens,
        (∀ L ∈ lenses, L.f ∈ curves ∧ L.g ∈ curves) →
        (∀ L₁ ∈ lenses, ∀ L₂ ∈ lenses,
          L₁ ≠ L₂ → L₁.Nonoverlap L₂) →
        (lenses.card : ℝ) ≤
          C * Real.rpow curves.card (3 / 2 : ℝ) *
            Real.log (curves.card + 1)) →
    ∀ {ι : Type*} [DecidableEq ι],
      ∀ (S : Finset ι) (curves : Finset C2Function),
        IsGraphPseudoCircleFamily curves →
        ∀ lens : S → GraphLens,
          (∀ i, (lens i).f ∈ curves ∧ (lens i).g ∈ curves) →
          (∀ i j, i ≠ j → (lens i).Nonoverlap (lens j)) →
          (S.card : ℝ) ≤
            C * Real.rpow curves.card (3 / 2 : ℝ) *
              Real.log (curves.card + 1)

end Kakeya.Cinematic
