import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# Reassemble the tangency geometry package
-/

namespace Kakeya.Cinematic

theorem tangency_geometry_assembly :
    TangencyGeometryAssemblyStatement := by
  intro hSublevel hExtension K D hK hD
  rcases hSublevel K D hK hD with ⟨C₁, hC₁, hSublevelMain⟩
  rcases hExtension K D hK hD with ⟨C₂, hC₂, hExtensionMain⟩
  let C : ℝ := max C₁ C₂
  have hC : 0 < C := lt_of_lt_of_le hC₁ (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro family hfamily I hI f hf g hg hfg delta hdelta hscale
  have hSub := hSublevelMain family hfamily I hI f hf g hg hfg
    delta hdelta hscale
  have hExt := hExtensionMain family hfamily I hI f hf g hg hfg
    delta hdelta hscale
  constructor
  · rcases hSub with ⟨pieces, hcard, hunion, hlengths, hlower⟩
    refine ⟨pieces, hcard, hunion, ?_, ?_⟩
    · intro j
      have hC₁C : C₁ ≤ C := le_max_left _ _
      have hscale_nonneg :
          0 ≤ Real.sqrt
            ((tangencyParameterOn I f g + delta) *
              c2Distance f g) :=
        Real.sqrt_nonneg _
      exact (hlengths j).trans <|
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC₁C hdelta.le)
          hscale_nonneg
    · intro x hx
      rcases hlower x hx with ⟨j, hj, hlowerj⟩
      refine ⟨j, hj, hlowerj.trans ?_⟩
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂)
          (Real.sqrt_nonneg _))
        (ParameterInterval.length_nonneg (pieces.interval j))
  · intro J hJ hclose lambda hlambda x hxI hxJ
    have hbound := hExt J hJ hclose lambda hlambda x hxI hxJ
    exact hbound.trans <|
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂)
          (sq_nonneg lambda))
        hdelta.le

end Kakeya.Cinematic
