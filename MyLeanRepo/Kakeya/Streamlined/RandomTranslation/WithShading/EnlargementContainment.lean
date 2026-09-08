import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.ResidualAbsorption
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.SameAxisEnlargementConflictDegree.Proof

/-!
# Enlargement containment and conflict degree

Combines residual-shift absorption via coaxial enlargement with the
conflict-degree bound on the enlarged family.  This is the geometric input
for per-scale ED coarse selection in the multiscale random-translation argument.

## Main results

- `enlargement_containment`: a residual-shifted fine tube is contained in the
  coaxial ρ-enlargement of its σ-scale parent.
- `enlargement_containment_family`: family version for all copy indices.
- `enlarged_family_conflict_degree`: conflict degree bound on the enlarged
  family of a UTS coarse family.
- `enlargement_containment_and_conflict`: combined corollary for the UTS setting.
-/

noncomputable section

open Kakeya.Streamlined.GeometricLemmas

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- A residual-shifted fine tube is contained in the coaxial enlargement of
its coarse parent. -/
lemma enlargement_containment
    {δ σ ρ : ℝ} {fine : TubeFamily δ} {coarse : TubeFamily σ}
    (P : TubeCover fine coarse)
    (hsigma : 0 ≤ σ) (hsigma_rho : σ ≤ ρ)
    (vRem : Point3) (hv : ‖vRem‖ ≤ ρ - σ)
    (i : Fin fine.card) :
    (translateTube (fine.tube i) vRem).carrier ⊆
      ((sameAxisEnlargedFamily (rho := ρ) coarse).tube (P.parent i)).carrier :=
  translate_contained_in_same_axis_enlargement
    hsigma hsigma_rho (fine.tube i) (coarse.tube (P.parent i))
    (P.nested i) vRem hv

/-- Family version: for every copy index and fine tube index. -/
lemma enlargement_containment_family
    {δ σ ρ : ℝ} {fine : TubeFamily δ} {coarse : TubeFamily σ}
    {J : ℕ}
    (P : TubeCover fine coarse)
    (hsigma : 0 ≤ σ) (hsigma_rho : σ ≤ ρ)
    (vRem : Fin J → Point3)
    (hv : ∀ j, ‖vRem j‖ ≤ ρ - σ) :
    ∀ (j : Fin J) (i : Fin fine.card),
      (translateTube (fine.tube i) (vRem j)).carrier ⊆
        ((sameAxisEnlargedFamily (rho := ρ) coarse).tube (P.parent i)).carrier :=
  fun j i => enlargement_containment P hsigma hsigma_rho (vRem j) (hv j) i

/-- Conflict degree bound on the coaxial enlargement of a UTS coarse family. -/
lemma enlarged_family_conflict_degree
    {δ : ℝ} (hδ : 0 < δ)
    {fine : TubeFamily δ} (hfine_ball : fine.IsInUnitBall)
    (U : UniformTubeStructure fine)
    (sigma rho : AdmissibleScale δ)
    (hsigma_rho : sigma.1 ≤ rho.1) :
    ∃ (C : ℝ), 0 < C ∧
      ∀ (j : Fin (U.coarse sigma).card),
        tubeConflictDegree
          (sameAxisEnlargedFamily (rho := rho.1) (U.coarse sigma)) j ≤
          Nat.ceil (C * (rho.1 / sigma.1) ^ 4) := by
  rcases same_axis_enlargement_conflict_degree with ⟨C, hC_pos, hC_bound⟩
  refine ⟨C, hC_pos, ?_⟩
  exact hC_bound hδ fine hfine_ball U sigma rho hsigma_rho

/-- Combined enlargement containment and conflict degree bound for a UTS
coarse family at scale `sigma` enlarged to scale `rho`. -/
lemma enlargement_containment_and_conflict
    {δ : ℝ} (hδ : 0 < δ)
    {fine : TubeFamily δ} (hfine_ball : fine.IsInUnitBall)
    (U : UniformTubeStructure fine)
    (sigma rho : AdmissibleScale δ)
    (hsigma_rho : sigma.1 ≤ rho.1) :
    ∃ (C : ℝ), 0 < C ∧
      (∀ {J : ℕ} (vRem : Fin J → Point3),
        (∀ j, ‖vRem j‖ ≤ rho.1 - sigma.1) →
        ∀ (j : Fin J) (i : Fin fine.card),
          (translateTube (fine.tube i) (vRem j)).carrier ⊆
            ((sameAxisEnlargedFamily (rho := rho.1) (U.coarse sigma)).tube
              ((U.cover sigma).parent i)).carrier) ∧
      ∀ (j : Fin (U.coarse sigma).card),
        tubeConflictDegree
          (sameAxisEnlargedFamily (rho := rho.1) (U.coarse sigma)) j ≤
          Nat.ceil (C * (rho.1 / sigma.1) ^ 4) := by
  rcases enlarged_family_conflict_degree hδ hfine_ball U sigma rho hsigma_rho
    with ⟨C, hC_pos, hC_conflict⟩
  refine ⟨C, hC_pos, ?_⟩
  have hsigma : 0 ≤ sigma.1 := by
    have h1 : δ ≤ sigma.1 := sigma.2.1
    linarith
  constructor
  · intro J vRem hv j i
    exact enlargement_containment (U.cover sigma) hsigma hsigma_rho
      (vRem j) (hv j) i
  · exact hC_conflict

end Kakeya.Streamlined.RandomTranslation.WithShading

end
