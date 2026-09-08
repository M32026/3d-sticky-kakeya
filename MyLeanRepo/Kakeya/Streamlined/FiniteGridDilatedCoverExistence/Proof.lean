import MyLeanRepo.Kakeya.Streamlined.FiniteGridDilatedCoverExistence

/-!
# Finite grid dilated cover existence
-/

namespace Kakeya.Streamlined

theorem finite_grid_dilated_cover_existence_main :
    FiniteGridDilatedCoverExistenceStatement := by
  rcases single_scale_tube_cover_main with ⟨A, hA_one, h_main⟩
  refine ⟨A, hA_one, ?_⟩
  intro delta hdelta hdelta_le_one F hF_nonempty hF_ball hF_ed
  let H (k : UniformScaleIndex delta) :
      ∃ (coarse : TubeFamily (uniformScale delta hdelta_le_one k).1),
        ∃ (cover : DilatedTubeCover A F coarse), coarse.IsEssentiallyDistinct := by
    let rho : AdmissibleScale delta := uniformScale delta hdelta_le_one k
    exact h_main delta rho.1 hdelta rho.2.1 rho.2.2 F hF_nonempty hF_ball hF_ed
  let coarse (k : UniformScaleIndex delta) := (H k).choose
  let cover (k : UniformScaleIndex delta) := (H k).choose_spec.choose
  have h_ed : ∀ k, (coarse k).IsEssentiallyDistinct := by
    intro k
    exact (H k).choose_spec.choose_spec
  exact ⟨coarse, cover, h_ed⟩

end Kakeya.Streamlined
