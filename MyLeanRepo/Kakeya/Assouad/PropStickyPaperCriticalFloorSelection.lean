import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCriticalFloorSelectionStatements

/-! # Select the WZ2 critical-floor structural parameter -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_critical_floor_selection :
    WZ2PaperCriticalFloorSelectionStatement := by
  intro sigma floorLoss structuralBudget hfloorLoss hbudget hCritical
  rcases
      hCritical floorLoss structuralBudget hfloorLoss hbudget with
    ⟨structuralLoss, delta₀, hstructuralLoss, hstructuralBudget,
      hdelta₀, hdelta₀One, hFloor⟩
  exact
    ⟨{
      structuralLoss := structuralLoss
      structuralLoss_pos := hstructuralLoss
      structuralLoss_le := hstructuralBudget
      delta₀ := delta₀
      delta₀_pos := hdelta₀
      delta₀_le_one := hdelta₀One
      volume_floor := hFloor
    }⟩

end Kakeya.Assouad

end
