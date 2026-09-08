module

public import Kakeya.Factoring.DilatedTubePresentation
public import Kakeya.Factoring.WeightedFullness
public import Kakeya.DimensionThree.MainLemma1.Factoring

/-!
# Whole-fibre bridge for the reordered honest coarse producer

The raw factor is run only after the parent family has been refined.  Its support identity then
deletes whole parent fibres, so every retained active fibre is literally the original factor
fibre.  This file packages that equality, the resulting branch-cardinality bracket, and the
carrier-weighted choice of a retained fibre with at least average fullness.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya.ml1CoarseHonestW45

universe u v w

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- Regard the retained fine family as a factor family over the raw dilated parents.  This is
only an averaging device: the final coarse witnesses remain the honest presented tubes. -/
noncomputable def HonestDilateProductOutput.fineFactorFamily
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {δ ρ c : NNReal}
    {F : ShadedBody.FactorFamily E ι κ} {T : ι → ShadedTube δ E}
    {Tρ : κ → Tube ρ E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι → ShadedTube δ E} {coarseShade : κ → ShadedTube ρ E}
    {parent : ι → κ} {productConstant : NNReal}
    (h : HonestDilateProductOutput (c := c) F T Tρ fineSet coarseSet fineShade coarseShade
      parent productConstant) :
    ShadedBody.FactorFamily E ι κ where
  innerSet := fineSet
  innerBody := fun i ↦ (fineShade i).toShadedBody
  outerSet := coarseSet
  outerBody := fun j ↦ Tube.dilate (Tρ j) (c : ℝ)
  parent := parent
  parent_mem := h.parent_mem
  inner_le_parent := by
    intro i hi
    exact (congrArg (fun U : Tube δ E ↦ U.toConvexSpaceBody) (h.fine_tube i)).trans_le
      (h.raw_parent_containment i hi)

/-- The fibre of the averaging factor family is exactly the active fibre used in the product. -/
@[simp]
theorem HonestDilateProductOutput.fineFactorFamily_fiber
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {δ ρ c : NNReal}
    {F : ShadedBody.FactorFamily E ι κ} {T : ι → ShadedTube δ E}
    {Tρ : κ → Tube ρ E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι → ShadedTube δ E} {coarseShade : κ → ShadedTube ρ E}
    {parent : ι → κ} {productConstant : NNReal}
    (h : HonestDilateProductOutput (c := c) F T Tρ fineSet coarseSet fineShade coarseShade
      parent productConstant) (j : κ) :
    h.fineFactorFamily.fiber j = activeFibre fineSet parent j := by
  ext i
  simp only [fineFactorFamily, ShadedBody.FactorFamily.fiber, activeFibre,
    Finset.mem_filter]

/-- Once a parent survives, the raw factor's support filter retains its entire original fibre. -/
theorem HonestDilateProductOutput.activeFibre_eq_factorFiber
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {δ ρ c : NNReal}
    {F : ShadedBody.FactorFamily E ι κ} {T : ι → ShadedTube δ E}
    {Tρ : κ → Tube ρ E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι → ShadedTube δ E} {coarseShade : κ → ShadedTube ρ E}
    {parent : ι → κ} {productConstant : NNReal}
    (h : HonestDilateProductOutput (c := c) F T Tρ fineSet coarseSet fineShade coarseShade
      parent productConstant) {j : κ} (hj : j ∈ coarseSet) :
    activeFibre fineSet parent j = F.fiber j := by
  rw [h.fine_eq_filter, h.parent_eq]
  ext i
  simp only [activeFibre, ShadedBody.FactorFamily.fiber, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hi, _⟩, hp⟩
    exact ⟨hi, hp⟩
  · rintro ⟨hi, hp⟩
    exact ⟨⟨hi, hp ▸ hj⟩, hp⟩

/-- A dyadic cardinality band on the already-refined parent fibres transfers verbatim to every
active product fibre.  The relative-retention clause costs nothing because the fibres are equal. -/
theorem HonestDilateProductOutput.activeFibre_branch_card
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {σ ρ c : NNReal}
    {F : ShadedBody.FactorFamily E ι κ} {T : ι → ShadedTube σ E}
    {Tρ : κ → Tube ρ E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι → ShadedTube σ E} {coarseShade : κ → ShadedTube ρ E}
    {parent : ι → κ} {productConstant N : NNReal}
    (h : HonestDilateProductOutput (c := c) F T Tρ fineSet coarseSet fineShade coarseShade
      parent productConstant)
    {δ : NNReal} (hδ1 : δ ≤ 1) {eps' : ℝ} (heps' : 0 ≤ eps')
    (hband : ∀ j ∈ F.outerSet,
      (N : ENNReal) ≤ ((F.fiber j).card : ENNReal) ∧
      ((F.fiber j).card : ENNReal) ≤ 2 * (N : ENNReal)) :
    ∀ j ∈ coarseSet,
      (N : ENNReal) ≤ ((activeFibre fineSet parent j).card : ENNReal) ∧
      ((activeFibre fineSet parent j).card : ENNReal) ≤ 2 * (N : ENNReal) ∧
      (δ : ENNReal) ^ (2 * eps') * ((F.fiber j).card : ENNReal) ≤
        ((activeFibre fineSet parent j).card : ENNReal) := by
  have hfibreEq (j : κ) :
      Kakeya.ml1Boot.fibre F.innerSet F.parent j = F.fiber j := by
    ext i
    simp only [Kakeya.ml1Boot.fibre, ShadedBody.FactorFamily.fiber, Finset.mem_filter]
  have hband' : ∀ j ∈ coarseSet,
      (N : ENNReal) ≤ ((Kakeya.ml1Boot.fibre F.innerSet F.parent j).card : ENNReal) ∧
      ((Kakeya.ml1Boot.fibre F.innerSet F.parent j).card : ENNReal) ≤ 2 * (N : ENNReal) := by
    intro j hj
    rw [hfibreEq]
    exact hband j (h.coarse_subset hj)
  have hraw := Kakeya.ml1Boot.branch_card_filter_parent hδ1 heps'
    F.innerSet F.parent coarseSet N hband'
  intro j hj
  have hactiveEq :
      Kakeya.ml1Boot.fibre (F.innerSet.filter fun i ↦ F.parent i ∈ coarseSet)
          F.parent j = activeFibre fineSet parent j := by
    rw [h.fine_eq_filter, h.parent_eq]
    ext i
    simp only [activeFibre, Kakeya.ml1Boot.fibre, Finset.mem_filter]
  rw [← hactiveEq, ← hfibreEq]
  exact hraw j hj

/-- Positive retained shade mass supplies a retained parent whose complete active fibre has at
least the average fullness of the whole retained fine family. -/
theorem HonestDilateProductOutput.exists_fullness_le_activeFibre
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {δ ρ c : NNReal}
    {F : ShadedBody.FactorFamily E ι κ} {T : ι → ShadedTube δ E}
    {Tρ : κ → Tube ρ E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι → ShadedTube δ E} {coarseShade : κ → ShadedTube ρ E}
    {parent : ι → κ} {productConstant : NNReal}
    (h : HonestDilateProductOutput (c := c) F T Tρ fineSet coarseSet fineShade coarseShade
      parent productConstant)
    (hmass : 0 < ∑ i ∈ fineSet, volume (fineShade i).shade) :
    ∃ j ∈ coarseSet,
      (fullness fineSet (fun i ↦ (fineShade i).toShadedBody) : ENNReal) ≤
        (fullness (activeFibre fineSet parent j)
          (fun i ↦ (fineShade i).toShadedBody) : ENNReal) := by
  have hmass_le : (∑ i ∈ fineSet, volume (fineShade i).shade) ≤
      ∑ i ∈ fineSet, volume (fineShade i).carrier := by
    apply Finset.sum_le_sum
    intro i _
    exact measure_mono (fineShade i).shade_subset
  have hcarrier0 : (∑ i ∈ fineSet, volume (fineShade i).carrier) ≠ 0 :=
    ne_of_gt (hmass.trans_le hmass_le)
  obtain ⟨j, hj, hfull⟩ :=
    ShadedBody.exists_fullness_le_fiber h.fineFactorFamily h.coarse_nonempty hcarrier0
  have hfib : h.fineFactorFamily.fiber j = activeFibre fineSet parent j :=
    h.fineFactorFamily_fiber j
  rw [hfib] at hfull
  exact ⟨j, hj, hfull⟩

/-- The product's quantitative fine refinement turns positive source shade mass into positive
retained mass. -/
theorem HonestDilateProductOutput.fine_mass_pos
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {δ ρ c : NNReal}
    {F : ShadedBody.FactorFamily E ι κ} {T : ι → ShadedTube δ E}
    {Tρ : κ → Tube ρ E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι → ShadedTube δ E} {coarseShade : κ → ShadedTube ρ E}
    {parent : ι → κ} {productConstant : NNReal}
    (h : HonestDilateProductOutput (c := c) F T Tρ fineSet coarseSet fineShade coarseShade
      parent productConstant)
    (hproductConstant : 0 < productConstant)
    (hsourceMass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    0 < ∑ i ∈ fineSet, volume (fineShade i).shade := by
  have hcoeff : (0 : ENNReal) < ((productConstant⁻¹ : NNReal) : ENNReal) := by
    exact ENNReal.coe_pos.mpr (inv_pos.mpr hproductConstant)
  exact (ENNReal.mul_pos hcoeff.ne' hsourceMass.ne').trans_le h.fine_refinement.2

/-- Exact endpoint of the "refine first" ordering: choose one retained parent whose active fibre
simultaneously has the required fullness and the complete branch-cardinality bracket. -/
theorem HonestDilateProductOutput.exists_fullness_and_branch_card
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {σ ρ c : NNReal}
    {F : ShadedBody.FactorFamily E ι κ} {T : ι → ShadedTube σ E}
    {Tρ : κ → Tube ρ E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι → ShadedTube σ E} {coarseShade : κ → ShadedTube ρ E}
    {parent : ι → κ} {productConstant N : NNReal}
    (h : HonestDilateProductOutput (c := c) F T Tρ fineSet coarseSet fineShade coarseShade
      parent productConstant)
    (hproductConstant : 0 < productConstant)
    (hsourceMass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    {δ : NNReal} (hδ1 : δ ≤ 1) {eps' : ℝ} (heps' : 0 ≤ eps')
    (hband : ∀ j ∈ F.outerSet,
      (N : ENNReal) ≤ ((F.fiber j).card : ENNReal) ∧
      ((F.fiber j).card : ENNReal) ≤ 2 * (N : ENNReal)) :
    ∃ j ∈ coarseSet,
      (fullness fineSet (fun i ↦ (fineShade i).toShadedBody) : ENNReal) ≤
          (fullness (activeFibre fineSet parent j)
            (fun i ↦ (fineShade i).toShadedBody) : ENNReal) ∧
      (N : ENNReal) ≤ ((activeFibre fineSet parent j).card : ENNReal) ∧
      ((activeFibre fineSet parent j).card : ENNReal) ≤ 2 * (N : ENNReal) ∧
      (δ : ENNReal) ^ (2 * eps') * ((F.fiber j).card : ENNReal) ≤
        ((activeFibre fineSet parent j).card : ENNReal) := by
  obtain ⟨j, hj, hfull⟩ := h.exists_fullness_le_activeFibre
    (h.fine_mass_pos hproductConstant hsourceMass)
  exact ⟨j, hj, hfull, h.activeFibre_branch_card hδ1 heps' hband j hj⟩

end Kakeya.ml1CoarseHonestW45

end

#print axioms Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput.activeFibre_eq_factorFiber
#print axioms Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput.activeFibre_branch_card
#print axioms Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput.exists_fullness_le_activeFibre
#print axioms Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput.exists_fullness_and_branch_card
