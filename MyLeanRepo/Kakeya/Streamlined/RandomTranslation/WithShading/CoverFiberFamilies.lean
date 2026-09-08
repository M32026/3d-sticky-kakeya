import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.SharedCoverFiberMass
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.Submultiplicativity
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Tube families carried by the fibers of a cover

At one scale of the general-`M` construction, the many-family probability
theorem is applied simultaneously to the actual parent fibers of one tube
cover.  This module freezes those families and their restricted shadings as
canonical data rather than rebuilding their finite reindexing in each
consumer.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined
namespace TubeCover

variable {δ ρ : ℝ} {fine : TubeFamily δ} {coarse : TubeFamily ρ}

/-- Fine indices assigned to one coarse parent. -/
def fiberIndexSet (P : TubeCover fine coarse) (j : Fin coarse.card) :
    Finset (Fin fine.card) :=
  Finset.univ.filter fun i => P.parent i = j

/-- The fine tube family assigned to one coarse parent. -/
def fiberSubfamily (P : TubeCover fine coarse) (j : Fin coarse.card) :
    TubeSubfamily fine :=
  TubeSubfamily.fromFinset fine (P.fiberIndexSet j)

/-- Restrict a fine shading to one cover fiber. -/
def fiberShading (P : TubeCover fine coarse)
    (Y : TubeShading fine) (j : Fin coarse.card) :
    TubeShading (P.fiberSubfamily j).family :=
  (P.fiberSubfamily j).restrictShading Y

/--
Canonical package of facts about every cover fiber.

The support conclusion uses the actual coarse parent carrier.  Consumers may
compose it with a separate bounded-support theorem.
-/
def CoverFiberFamiliesStatement : Prop :=
  ∀ {δ ρ : ℝ},
    ∀ {fine : TubeFamily δ} {coarse : TubeFamily ρ},
    ∀ (P : TubeCover fine coarse),
    ∀ (Y : TubeShading fine),
    ∀ j : Fin coarse.card,
      let S := P.fiberSubfamily j
      let Z := P.fiberShading Y j
      S.Nonempty ∧
      S.family.enncard = P.toFactoring.fiberCount j ∧
      S.family.nominalMass = P.toFactoring.fiberMass j ∧
      Z.mass =
        ∑ i ∈ P.fiberIndexSet j, volume (Y.carrier i) ∧
      (∀ i, (S.family.tube i).carrier ⊆
        (coarse.tube j).carrier) ∧
      S.family.toBodyFamily.deltaMax ≤
        fine.toBodyFamily.deltaMax

end TubeCover
end Kakeya.Streamlined

end
