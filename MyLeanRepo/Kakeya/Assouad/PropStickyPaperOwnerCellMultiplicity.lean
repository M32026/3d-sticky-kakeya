import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers

/-! # Point multiplicity of owner-cell coarse shadings -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem wz2_paper_owner_cell_pointMultiplicity_le_one
    {rho : ℝ} {α : Type*}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (shading : WZ1PaperTubeShading coarse)
    (cells : Finset WZ2PaperCellIndex)
    (parentEmbedding : Fin coarse.card ↪ α)
    (owner : WZ2PaperCellIndex → α)
    (carrier_iff :
      ∀ parent point,
        point ∈ shading.carrier parent ↔
          ∃ cell ∈ cells,
            parentEmbedding parent = owner cell ∧
              point ∈ wz1PaperGridCube rho cell) :
    ∀ point,
      (shading.pointMultiplicity point : ENNReal) ≤ 1 := by
  intro point
  have natBound : shading.pointMultiplicity point ≤ 1 := by
    simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
    apply Finset.card_le_one.mpr
    intro first first_mem second second_mem
    have point_first : point ∈ shading.carrier first := by
      simpa [Finset.mem_filter] using first_mem
    have point_second : point ∈ shading.carrier second := by
      simpa [Finset.mem_filter] using second_mem
    rcases (carrier_iff first point).mp point_first with
      ⟨firstCell, firstCell_mem, first_owner, point_first_cell⟩
    rcases (carrier_iff second point).mp point_second with
      ⟨secondCell, secondCell_mem, second_owner, point_second_cell⟩
    have cells_eq : firstCell = secondCell := by
      have h1 : wz1PaperGridIndex rho point = firstCell :=
        (mem_wz1PaperGridCube rho firstCell point).mp point_first_cell
      have h2 : wz1PaperGridIndex rho point = secondCell :=
        (mem_wz1PaperGridCube rho secondCell point).mp point_second_cell
      exact h1.symm.trans h2
    apply parentEmbedding.injective
    rw [first_owner, second_owner, cells_eq]
  exact_mod_cast natBound

theorem wz2_paper_owner_cell_mass_eq_union_volume
    {rho : ℝ} {α : Type*}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (shading : WZ1PaperTubeShading coarse)
    (cells : Finset WZ2PaperCellIndex)
    (parentEmbedding : Fin coarse.card ↪ α)
    (owner : WZ2PaperCellIndex → α)
    (carrier_iff :
      ∀ parent point,
        point ∈ shading.carrier parent ↔
          ∃ cell ∈ cells,
            parentEmbedding parent = owner cell ∧
              point ∈ wz1PaperGridCube rho cell) :
    shading.mass = volume shading.union :=
  mass_eq_union_volume_of_pointMultiplicity_le_one
    (wz2_paper_owner_cell_pointMultiplicity_le_one
      shading cells parentEmbedding owner carrier_iff)

end Kakeya.Assouad

end
