import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FixedGridBoundaryMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PaperShadingMassFinite

/-!
# Proposition 6.2 source shading mass

This module packages positivity and finiteness of the source shading mass.
Positivity is deduced from aggregate density and the paper body-family mass
lower bound, without selecting a tube or proving positivity tube by tube.
-/

noncomputable section

namespace Kakeya.Assouad

theorem pureWZ2_prop62_source_body_mass_pos
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLe : delta ≤ 1 / 100)
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceNonempty : source.Nonempty)
    (sourceLine : WZ1PaperIsLineClass source) :
    0 < (wz1PaperBodyFamily source).mass := by
  have sourceEnncardPos : 0 < source.enncard := by
    rw [Kakeya.Streamlined.TubeFamily.enncard]
    exact_mod_cast sourceNonempty
  have scaleMassPos : 0 < Kakeya.realRpowENN delta 2 :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos deltaPos 2)
  exact
    (ENNReal.mul_pos sourceEnncardPos.ne' scaleMassPos.ne').trans_le
      (pureWZ2_prop62_paper_body_mass_lower
        deltaPos (deltaLe.trans (by norm_num)) sourceLine)

theorem pureWZ2_prop62_source_shading_mass_pos
    (A : ℕ)
    (eta : ℝ)
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLe : delta ≤ 1 / 100)
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceNonempty : source.Nonempty)
    (sourceLine : WZ1PaperIsLineClass source)
    (shading : WZ1PaperTubeShading source)
    (sourceDense :
      shading.IsLambdaDense
        (Kakeya.realRpowENN delta ((A : ℝ) * eta))) :
    0 < shading.mass := by
  have densityPos :
      0 < Kakeya.realRpowENN delta ((A : ℝ) * eta) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos deltaPos _)
  have bodyMassPos : 0 < (wz1PaperBodyFamily source).mass :=
    pureWZ2_prop62_source_body_mass_pos
      deltaPos deltaLe sourceNonempty sourceLine
  exact
    (ENNReal.mul_pos densityPos.ne' bodyMassPos.ne').trans_le sourceDense

theorem pureWZ2_prop62_source_shading_mass_ne_top
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source) :
    shading.mass ≠ ⊤ :=
  wz1PaperTubeShading_mass_ne_top shading

structure PureWZ2Prop62SourceShadingMassData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source) : Prop where
  mass_pos : 0 < shading.mass
  mass_ne_top : shading.mass ≠ ⊤

theorem pureWZ2_prop62_source_shading_mass
    (A : ℕ)
    (eta : ℝ)
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLe : delta ≤ 1 / 100)
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceNonempty : source.Nonempty)
    (sourceLine : WZ1PaperIsLineClass source)
    (shading : WZ1PaperTubeShading source)
    (sourceDense :
      shading.IsLambdaDense
        (Kakeya.realRpowENN delta ((A : ℝ) * eta))) :
    PureWZ2Prop62SourceShadingMassData shading where
  mass_pos :=
    pureWZ2_prop62_source_shading_mass_pos
      A eta deltaPos deltaLe sourceNonempty sourceLine shading sourceDense
  mass_ne_top :=
    pureWZ2_prop62_source_shading_mass_ne_top shading

end Kakeya.Assouad

end
