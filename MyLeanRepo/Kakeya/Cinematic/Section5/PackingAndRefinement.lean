import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulAssemblyInputs

attribute [local instance] Classical.propDecidable

/-!
# Packing bounds and rectangle refinement

This module combines the paper-facing rectangle packing and maximal
incomparable-subfamily inputs used in the faithful Section 5 assembly.
-/

namespace Kakeya.Cinematic

/-- Apply the rectangle packing theorem using the curvature and interval
control supplied by a cinematic family. -/
lemma fine_packing_bound_of_controlled
    (hPacking : RectanglePackingStatement)
    {K D : ℝ} (hK : 1 ≤ K)
    {family : Set C2Function}
    (hfamily : IsCinematicFamily family K D)
    {I : ParameterInterval}
    (hI_controlled : I.IsControlled K)
    {delta t lambda : ℝ}
    (hdelta : 0 < delta)
    (hdelta_t : delta ≤ t)
    (ht_one : t ≤ 1)
    (hlambda : 100 ≤ lambda)
    (center : C2Function)
    {R : RectangleFamily delta t}
    (hR_centers : R.CentersIn family)
    (hR_central : R.IsOverCentralQuarterOf I)
    (hR_incomp : R.IsPairwiseIncomparable family 100)
    (hcenter_bound :
      ∀ i, c2Distance center (R.rectangle i).function ≤ 3 * t)
    {U : CurvilinearRectangle (lambda * delta) t}
    (hU_contains : ∀ i, (R.rectangle i).carrier ⊆ U.carrier) :
    ∃ C : ℝ, 0 < C ∧
      (R.card : ℝ) ≤ C * Real.rpow lambda (5 / 2 : ℝ) := by
  rcases hPacking K hK with ⟨C, hC_pos, hMain⟩
  have hCurvature : HasCinematicCurvature family K :=
    ⟨hfamily.1, hfamily.2.2⟩
  have hI_short : I.IsShort K := hI_controlled.2
  exact ⟨C, hC_pos,
    hMain family hCurvature I hI_short delta t lambda hdelta
      hdelta_t ht_one hlambda center R hR_centers hR_central
      hR_incomp hcenter_bound U hU_contains⟩

/-- Refine a fine rectangle family to a `C`-incomparable subfamily while
retaining the original packing bound and a comparable parent for every
discarded rectangle. -/
lemma refine_and_pack
    (hSelection : RectangleSubfamilySelectionStatement)
    (hPacking : RectanglePackingStatement)
    {K D : ℝ} (hK : 1 ≤ K)
    {family : Set C2Function}
    (hfamily : IsCinematicFamily family K D)
    {I : ParameterInterval}
    (hI_controlled : I.IsControlled K)
    {delta t lambda : ℝ}
    (hdelta : 0 < delta)
    (hdelta_t : delta ≤ t)
    (ht_one : t ≤ 1)
    (hlambda : 100 ≤ lambda)
    (center : C2Function)
    {R : RectangleFamily delta t}
    (hR_centers : R.CentersIn family)
    (hR_central : R.IsOverCentralQuarterOf I)
    (hR_incomp : R.IsPairwiseIncomparable family 100)
    (hcenter_bound :
      ∀ i, c2Distance center (R.rectangle i).function ≤ 3 * t)
    {U : CurvilinearRectangle (lambda * delta) t}
    (hU_contains : ∀ i, (R.rectangle i).carrier ⊆ U.carrier)
    (C : ℝ)
    (hC : 100 ≤ C) :
    ∃ (S : RectangleSubfamily R) (C_pack : ℝ),
      S.family.CentersIn family ∧
      S.family.IsPairwiseIncomparable family C ∧
      0 < C_pack ∧
      (R.card : ℝ) ≤ C_pack * Real.rpow lambda (5 / 2 : ℝ) ∧
      ∀ i : Fin R.card,
        ∃ j : Fin S.card,
          i = S.embedding j ∨
            (R.rectangle i).AreLambdaComparable
              (S.family.rectangle j) family C := by
  rcases hSelection delta t family C hC R hR_centers with
    ⟨S, hS_centers, hS_incomp, hcoverage⟩
  rcases fine_packing_bound_of_controlled hPacking hK hfamily
      hI_controlled hdelta hdelta_t ht_one hlambda center
      hR_centers hR_central hR_incomp hcenter_bound hU_contains with
    ⟨C_pack, hC_pack_pos, hR_bound⟩
  exact ⟨S, C_pack, hS_centers, hS_incomp, hC_pack_pos,
    hR_bound, hcoverage⟩

end Kakeya.Cinematic
