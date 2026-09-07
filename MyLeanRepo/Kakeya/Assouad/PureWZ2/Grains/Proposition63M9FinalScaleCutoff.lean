import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RobustTailSchedule

/-! # Pull the final power-rescaled radius below a prescribed cutoff -/

noncomputable section
namespace Kakeya.Assouad.PureWZ2

/-- Pre-runtime cutoff ensuring that the final mild-rescaled scale
`delta^(1-scaleLoss)` lies below the caller's requested ceiling. -/
theorem exists_proposition63_m9_final_scale_cutoff
    {scaleLoss target : ℝ} (hscaleLoss : scaleLoss < 1)
    (htarget : 0 < target) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        proposition63M9PowerScale delta scaleLoss * delta ≤ target := by
  have exponentPos : 0 < 1 - scaleLoss := by linarith
  rcases pure_wz2_exists_delta₀_rpow_le htarget exponentPos with
    ⟨delta₀, delta₀Pos, delta₀One, bound⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro delta deltaPos deltaLe
  rw [proposition63M9PowerScale_mul_delta deltaPos]
  exact bound delta deltaPos deltaLe

end Kakeya.Assouad.PureWZ2
end
