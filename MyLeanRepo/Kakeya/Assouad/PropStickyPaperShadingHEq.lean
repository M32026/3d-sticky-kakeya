import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements

/-!
# Transport paper-shading mass and union volume across heterogeneous equality
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem paperShading_mass_eq_of_heq
    {delta : ℝ}
    {firstFamily secondFamily : Kakeya.Streamlined.TubeFamily delta}
    {first : WZ1PaperTubeShading firstFamily}
    {second : WZ1PaperTubeShading secondFamily}
    (hFamily : firstFamily = secondFamily)
    (h : HEq first second) :
    first.mass = second.mass := by
  subst secondFamily
  have hEq : first = second := eq_of_heq h
  subst second
  rfl

theorem paperShading_union_volume_eq_of_heq
    {delta : ℝ}
    {firstFamily secondFamily : Kakeya.Streamlined.TubeFamily delta}
    {first : WZ1PaperTubeShading firstFamily}
    {second : WZ1PaperTubeShading secondFamily}
    (hFamily : firstFamily = secondFamily)
    (h : HEq first second) :
    volume first.union = volume second.union := by
  subst secondFamily
  have hEq : first = second := eq_of_heq h
  subst second
  rfl

end Kakeya.Assouad

end
