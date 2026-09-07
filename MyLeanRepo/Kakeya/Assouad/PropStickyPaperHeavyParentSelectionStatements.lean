import MyLeanRepo.Kakeya.Assouad.PropStickySelectedHitCover
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.WeightBinning

/-!
# Select a mass-comparable family of coarse parents

Apply dyadic weight binning to the shaded masses of the canonical full
geometric fibers.  Keep every fine tube whose parent lies in the selected
bin.  The resulting restricted cover retains a polylogarithmic fraction of
the total shaded mass, and every one of its full fibers has mass in one common
interval `[c, 2c]`.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperHeavyParentSelectionData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine) where
  bins : ℕ
  bins_eq :
    bins = Nat.log 2 (2 * coarse.card) + 1
  selectedParents : Finset (Fin coarse.card)
  selectedParents_nonempty : selectedParents.Nonempty
  parentMassLevel : ENNReal
  parentMassLevel_pos : 0 < parentMassLevel
  parent_mass_band :
    ∀ parent ∈ selectedParents,
      parentMassLevel ≤
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) shading).mass ∧
        (restrictPaperShading
            (cover.fullFiberSubfamily parent) shading).mass ≤
          2 * parentMassLevel
  selectedFineIndices : Finset (Fin fine.card)
  selectedFineIndices_eq :
    selectedFineIndices =
      Finset.univ.filter fun source =>
        cover.parent source ∈ selectedParents
  selected : Kakeya.Streamlined.TubeSubfamily fine
  selected_eq :
    selected =
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        fine selectedFineIndices
  selectedShading : WZ1PaperTubeShading selected.family
  selectedShading_eq :
    selectedShading =
      restrictPaperShading selected shading
  hitParentIndices_eq :
    cover.hitParentIndices selected = selectedParents
  retained_mass :
    shading.mass ≤
      2 * (bins : ENNReal) * selectedShading.mass
  full_fiber_complete :
    ∀ parent :
        Fin (cover.hitParentSubfamily selected).family.card,
      Finset.image selected.embedding
          (wz2PaperFullFiberIndices
            selected.family
            (cover.hitParentSubfamily selected).family
            parent) =
        wz2PaperFullFiberIndices fine coarse
          ((cover.hitParentSubfamily selected).embedding parent)
  selected_parent_mass_band :
    ∀ parent :
        Fin (cover.hitParentSubfamily selected).family.card,
      parentMassLevel ≤
          (restrictPaperShading
            ((cover.restrictToHitParents selected).fullFiberSubfamily
              parent)
            selectedShading).mass ∧
        (restrictPaperShading
            ((cover.restrictToHitParents selected).fullFiberSubfamily
              parent)
            selectedShading).mass ≤
          2 * parentMassLevel

def WZ2PaperHeavyParentSelectionStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      fine.Nonempty →
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ (cover : WZ2PaperPartitioningCover fine coarse),
          ∀ (shading : WZ1PaperTubeShading fine),
            0 < shading.mass →
            shading.mass ≠ ⊤ →
              Nonempty
                (WZ2PaperHeavyParentSelectionData cover shading)

end Kakeya.Assouad

end
