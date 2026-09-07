import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalYSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23YLayerSelection

/-!
# Separated residue selection of fixed-line parent y-layers
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceHorizontalFixedBinYResidueData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    (selection : PureWZ2SourceHorizontalFixedBinYSelection parents) where
  residue : Fin 512
  selected : Finset (ℤ × ℤ × ℤ)
  selected_eq :
    selected = selection.selected.filter fun parent =>
      let value := parent.2.1 % (512 : ℤ)
      value.toNat = residue
  selected_subset : selected ⊆ selection.selected
  selected_nonempty : selected.Nonempty
  card_fraction : selection.selected.card ≤ 512 * selected.card
  residue_eq :
    ∀ parent ∈ selected, parent.2.1 % (512 : ℤ) = (residue : ℤ)
  y_separated :
    ∀ first ∈ selected, ∀ second ∈ selected,
      first.2.1 = second.2.1 ∨
        (512 : ℤ) ≤ |first.2.1 - second.2.1|

theorem PureWZ2SourceHorizontalFixedBinYSelection.selectResidueFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    (selection : PureWZ2SourceHorizontalFixedBinYSelection parents) :
    Nonempty (PureWZ2SourceHorizontalFixedBinYResidueData selection) := by
  let label : (ℤ × ℤ × ℤ) → Fin 512 := fun parent =>
    ⟨(parent.2.1 % (512 : ℤ)).toNat, by
      have hnonneg : 0 ≤ parent.2.1 % (512 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hlt : parent.2.1 % (512 : ℤ) < (512 : ℤ) :=
        Int.emod_lt_of_pos _ (by norm_num)
      omega⟩
  rcases wz1Lemma23_weighted_pigeonhole
      (n := 512) (by norm_num) selection.selected (fun _ => 1) label with
    ⟨residue, hcardRaw⟩
  let selected := selection.selected.filter fun parent => label parent = residue
  have hcard : selection.selected.card ≤ 512 * selected.card := by
    simpa [selected, Finset.sum_const] using hcardRaw
  have hselectedNonempty : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hselectedCard : selected.card = 0 := by
      rw [hselectedEmpty]
      simp
    have hallCard : selection.selected.card = 0 := by
      apply Nat.le_zero.mp
      simpa [hselectedCard] using hcard
    exact (Finset.card_ne_zero.mpr selection.selected_nonempty) hallCard
  have hresidue :
      ∀ parent ∈ selected, parent.2.1 % (512 : ℤ) = (residue : ℤ) := by
    intro parent hparent
    have hlabel := (Finset.mem_filter.mp hparent).2
    have hnonneg : 0 ≤ parent.2.1 % (512 : ℤ) :=
      Int.emod_nonneg _ (by norm_num)
    have hcast : ((label parent : ℕ) : ℤ) = parent.2.1 % (512 : ℤ) := by
      simp [label, Int.toNat_of_nonneg hnonneg]
    have hcastEq := congrArg (fun value : Fin 512 => (value : ℤ)) hlabel
    rwa [hcast] at hcastEq
  have hseparated :
      ∀ first ∈ selected, ∀ second ∈ selected,
        first.2.1 = second.2.1 ∨
        (512 : ℤ) ≤ |first.2.1 - second.2.1| := by
    intro first hfirst second hsecond
    by_cases heq : first.2.1 = second.2.1
    · exact Or.inl heq
    · right
      have hmod : (first.2.1 - second.2.1) % (512 : ℤ) = 0 := by
        rw [Int.sub_emod, hresidue first hfirst, hresidue second hsecond]
        simp
      have hdiv : (512 : ℤ) ∣ first.2.1 - second.2.1 := by
        rwa [Int.dvd_iff_emod_eq_zero]
      exact Int.le_abs_of_dvd (sub_ne_zero.mpr heq) hdiv
  exact
    ⟨{ residue := residue
       selected := selected
       selected_eq := by
         apply Finset.ext
         intro parent
         simp only [selected, Finset.mem_filter]
         constructor
         · intro h
           exact ⟨h.1, by
             have hnonneg : 0 ≤ parent.2.1 % (512 : ℤ) :=
               Int.emod_nonneg _ (by norm_num)
             have hcast := congrArg (fun value : Fin 512 => (value : ℕ)) h.2
             simpa [label, Int.toNat_of_nonneg hnonneg] using hcast⟩
         · intro h
           refine ⟨h.1, ?_⟩
           apply Fin.ext
           simpa [label] using h.2
       selected_subset := Finset.filter_subset _ _
       selected_nonempty := hselectedNonempty
       card_fraction := hcard
       residue_eq := hresidue
       y_separated := hseparated }⟩

/-- Backwards-compatible residue data on the maximal global bin. -/
abbrev PureWZ2SourceHorizontalYResidueData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    (selection : PureWZ2SourceHorizontalYSelection parents) :=
  PureWZ2SourceHorizontalFixedBinYResidueData selection

/-- Compatibility wrapper for the former maximal-bin residue API. -/
theorem PureWZ2SourceHorizontalYSelection.selectResidue
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    (selection : PureWZ2SourceHorizontalYSelection parents) :
    Nonempty (PureWZ2SourceHorizontalYResidueData selection) :=
  selection.selectResidueFixedBin

end Kakeya.Assouad
