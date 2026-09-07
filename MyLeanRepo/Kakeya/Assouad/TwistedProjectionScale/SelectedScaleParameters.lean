import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.FixedBlockFamily
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeParameters

/-!
# Parameters of selected-scale block families

Whole-line provenance identifies every flattened coarse parameter tuple with
that of its source representative.  Thus the existing radius-four source
parameter box remains valid even though the modeled coarse segment basepoints
lie in the radius-five window.
-/

noncomputable section

namespace Kakeya.Assouad

namespace SelectedScaleFourBlockData

/-- Every flattened coarse member has its representative's line parameters. -/
lemma coarse_tubeParams_eq_representative
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (hsourceVertical : IsInVerticalChart fine)
    (q : Fin data.coarse.card) :
    tubeParamsOfTube (data.coarse.tube q) =
      tubeParams
        (F := fine)
        (data.selected.equivFin.symm (fixedBlockIndex q)).1 := by
  let source :=
    fine.tube
      (data.selected.equivFin.symm (fixedBlockIndex q)).1
  have hsourceVertical' :
      source.direction (2 : Fin 3) ≠ 0 := by
    have h :=
      hsourceVertical
        (data.selected.equivFin.symm (fixedBlockIndex q)).1
    exact abs_ne_zero.mp (by linarith)
  have hcoarseVertical :
      (data.coarse.tube q).direction (2 : Fin 3) ≠ 0 := by
    have h := data.coarse_isInVerticalChart hsourceVertical q
    exact abs_ne_zero.mp (by linarith)
  have haxis := data.coarse_axis q
  exact tubeParamsOfTube_eq_of_axis_eq
    source (data.coarse.tube q)
    hsourceVertical' hcoarseVertical haxis

/-- Source radius-four parameter bounds transfer unchanged to the coarse blocks. -/
lemma coarse_tubeParams_bounds
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (hbase : HasBoundedBase fine 4)
    (hvertical : IsInVerticalChart fine)
    (q : Fin data.coarse.card) :
    |(tubeParamsOfTube (data.coarse.tube q)).a| ≤ 12 ∧
      |(tubeParamsOfTube (data.coarse.tube q)).b| ≤ 12 ∧
      |(tubeParamsOfTube (data.coarse.tube q)).c| ≤ 2 ∧
      |(tubeParamsOfTube (data.coarse.tube q)).d| ≤ 2 := by
  rw [data.coarse_tubeParams_eq_representative hvertical q]
  exact tubeParams_bounds hbase hvertical
    (data.selected.equivFin.symm (fixedBlockIndex q)).1

end SelectedScaleFourBlockData

end Kakeya.Assouad
