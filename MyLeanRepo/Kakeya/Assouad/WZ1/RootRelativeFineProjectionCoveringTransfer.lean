import MyLeanRepo.Kakeya.Assouad.WZ1.RootRelativeFineProjectionPullback
import MyLeanRepo.Kakeya.Assouad.WZ1.GeneralizedThickening

/-!
# Root-relative fine projection covering transfer

Convert the explicit coarse-to-fine projection containment into a covering
number estimate. This module is purely metric: the coarse projection bound
over the enlarged ball remains an explicit premise.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

/--
A covering bound transfers through containment in a closed thickening, with
the explicit shift-grid factor supplied by `GeneralizedThickening`.
-/
lemma externalCoveringNumber_of_subset_cthickening
    {fine source : Set ℝ} {rho epsilon : ℝ} {bound : ENNReal}
    (hrho : 0 < rho) (hepsilon : 0 < epsilon)
    (hsubset : fine ⊆ cthickening epsilon source)
    (hsource :
      (↑(externalCoveringNumber (Real.toNNReal rho) source) : ENNReal) ≤
        bound) :
    (↑(externalCoveringNumber (Real.toNNReal rho) fine) : ENNReal) ≤
      (2 * Nat.ceil (epsilon / rho) + 2 : ENNReal) * bound := by
  have hrhoNN : Real.toNNReal rho = ⟨rho, hrho.le⟩ :=
    Real.toNNReal_of_nonneg hrho.le
  have hmono :
      externalCoveringNumber (Real.toNNReal rho) fine ≤
        externalCoveringNumber (Real.toNNReal rho)
          (cthickening epsilon source) :=
    externalCoveringNumber_mono_set hsubset
  have hthick :=
    externalCoveringNumber_cthickening_general
      hepsilon hrho (S := source)
  rw [← hrhoNN] at hthick
  have hthickENN :
      (↑(externalCoveringNumber (Real.toNNReal rho)
        (cthickening epsilon source)) : ENNReal) ≤
        (2 * Nat.ceil (epsilon / rho) + 2 : ENNReal) *
          (↑(externalCoveringNumber
            (Real.toNNReal rho) source) : ENNReal) := by
    exact_mod_cast hthick
  have hmonoENN :
      (↑(externalCoveringNumber (Real.toNNReal rho) fine) : ENNReal) ≤
        (↑(externalCoveringNumber (Real.toNNReal rho)
          (cthickening epsilon source)) : ENNReal) := by
    exact_mod_cast hmono
  exact hmonoENN.trans (hthickENN.trans (by gcongr))

/--
Transfer a uniform enlarged-ball Property-Three projection bound to the local
projection of the retained fine shading.

The conclusion retains the exact thickening factor. No Córdoba estimate or
parameter absorption is hidden in this theorem.
-/
lemma wz1_root_relative_fine_projection_covering_transfer
    {delta sigma epsilon₁ epsilon₂ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {scaleCount depth : ℕ}
    {schedule : Fin scaleCount →
      Kakeya.Streamlined.AdmissibleScale delta}
    (cover : WZ1RootRelativeBalancedCoverData
      (sigma := sigma) (epsilon := epsilon₁)
      U Y schedule depth)
    (coordinate : Fin scaleCount)
    (propertyThree : Kakeya.Streamlined.TubeShading
      (U.coarse (schedule coordinate)))
    (hpropertyThree : IsSubshading propertyThree
      (cover.atScale coordinate).coarseShading)
    (fine : WZ1Lemma17FineParentCellPullbackData
      (epsilon₂ := epsilon₂)
      (cover.toBalancedCoverData coordinate) propertyThree)
    (plane : WZ1PlaneMapData Y)
    (tau : ℝ)
    (bound : ENNReal)
    (hcoarse :
      ∀ q ∈ propertyThree.union,
        (↑(externalCoveringNumber
          (Real.toNNReal (schedule coordinate).1)
          (scalarProjection
            (plane.planeMap
              ((cover.atScale coordinate).representative
                ((cover.atScale coordinate).cell q)))
            (propertyThree.union ∩
              closedBall q
                (tau + 4 * (schedule coordinate).1)))) : ENNReal) ≤
          bound) :
    ∀ p ∈ fine.fineShading.union,
      (↑(externalCoveringNumber
        (Real.toNNReal (schedule coordinate).1)
        (scalarProjection (plane.planeMap p)
          (fine.fineShading.union ∩ closedBall p tau))) : ENNReal) ≤
        (2 * Nat.ceil
            ((4 * max 1 (plane.lipschitzConstant : ℝ) *
                (schedule coordinate).1) /
              (schedule coordinate).1) + 2 : ENNReal) *
          bound := by
  intro p hp
  rcases wz1_root_relative_fine_projection_pullback
      cover coordinate propertyThree hpropertyThree fine plane tau p hp with
    ⟨q, hq, _hcell, hsubset⟩
  have hrho : 0 < (schedule coordinate).1 :=
    (cover.atScale coordinate).coarse_extremal.1
  have hepsilon :
      0 < 4 * max 1 (plane.lipschitzConstant : ℝ) *
        (schedule coordinate).1 := by
    have hmax : 0 < max 1 (plane.lipschitzConstant : ℝ) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    positivity
  exact
    externalCoveringNumber_of_subset_cthickening
      hrho hepsilon hsubset (hcoarse q hq)

/--
Specialization of the fine covering transfer to a doubled coarse spatial
radius.

The condition `4 * rho ≤ tau` gives
`B(q, tau + 4 * rho) ⊆ B(q, 2 * tau)`. Thus a Córdoba projection estimate at
the actual doubled schedule scale can feed the fine local projection at
radius `tau`, without changing the cell normal.
-/
lemma wz1_root_relative_fine_projection_covering_transfer_of_doubled_ball
    {delta sigma epsilon₁ epsilon₂ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {scaleCount depth : ℕ}
    {schedule : Fin scaleCount →
      Kakeya.Streamlined.AdmissibleScale delta}
    (cover : WZ1RootRelativeBalancedCoverData
      (sigma := sigma) (epsilon := epsilon₁)
      U Y schedule depth)
    (coordinate : Fin scaleCount)
    (propertyThree : Kakeya.Streamlined.TubeShading
      (U.coarse (schedule coordinate)))
    (hpropertyThree : IsSubshading propertyThree
      (cover.atScale coordinate).coarseShading)
    (fine : WZ1Lemma17FineParentCellPullbackData
      (epsilon₂ := epsilon₂)
      (cover.toBalancedCoverData coordinate) propertyThree)
    (plane : WZ1PlaneMapData Y)
    (tau : ℝ)
    (bound : ENNReal)
    (hfour : 4 * (schedule coordinate).1 ≤ tau)
    (hcoarse :
      ∀ q ∈ propertyThree.union,
        (↑(externalCoveringNumber
          (Real.toNNReal (schedule coordinate).1)
          (scalarProjection
            (plane.planeMap
              ((cover.atScale coordinate).representative
                ((cover.atScale coordinate).cell q)))
            (propertyThree.union ∩
              closedBall q (2 * tau)))) : ENNReal) ≤
          bound) :
    ∀ p ∈ fine.fineShading.union,
      (↑(externalCoveringNumber
        (Real.toNNReal (schedule coordinate).1)
        (scalarProjection (plane.planeMap p)
          (fine.fineShading.union ∩ closedBall p tau))) : ENNReal) ≤
        (2 * Nat.ceil
            ((4 * max 1 (plane.lipschitzConstant : ℝ) *
                (schedule coordinate).1) /
              (schedule coordinate).1) + 2 : ENNReal) *
          bound := by
  apply wz1_root_relative_fine_projection_covering_transfer
    cover coordinate propertyThree hpropertyThree fine plane tau bound
  intro q hq
  have hsubset :
      propertyThree.union ∩
          closedBall q
            (tau + 4 * (schedule coordinate).1) ⊆
        propertyThree.union ∩ closedBall q (2 * tau) := by
    intro x hx
    exact ⟨hx.1, Metric.closedBall_subset_closedBall (by linarith) hx.2⟩
  have hmono :
      externalCoveringNumber
          (Real.toNNReal (schedule coordinate).1)
          (scalarProjection
            (plane.planeMap
              ((cover.atScale coordinate).representative
                ((cover.atScale coordinate).cell q)))
            (propertyThree.union ∩
              closedBall q
                (tau + 4 * (schedule coordinate).1))) ≤
        externalCoveringNumber
          (Real.toNNReal (schedule coordinate).1)
          (scalarProjection
            (plane.planeMap
              ((cover.atScale coordinate).representative
                ((cover.atScale coordinate).cell q)))
            (propertyThree.union ∩ closedBall q (2 * tau))) :=
    externalCoveringNumber_mono_set (Set.image_mono hsubset)
  have hmonoENN :
      (↑(externalCoveringNumber
        (Real.toNNReal (schedule coordinate).1)
        (scalarProjection
          (plane.planeMap
            ((cover.atScale coordinate).representative
              ((cover.atScale coordinate).cell q)))
          (propertyThree.union ∩
            closedBall q
              (tau + 4 * (schedule coordinate).1)))) : ENNReal) ≤
        (↑(externalCoveringNumber
          (Real.toNNReal (schedule coordinate).1)
          (scalarProjection
            (plane.planeMap
              ((cover.atScale coordinate).representative
                ((cover.atScale coordinate).cell q)))
            (propertyThree.union ∩ closedBall q (2 * tau)))) : ENNReal) := by
    exact_mod_cast hmono
  exact hmonoENN.trans (hcoarse q hq)

end Kakeya.Assouad
