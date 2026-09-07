import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.StickyRobustCloseCount

/-!
# Proposition 6.3 M9: robust degree cutoff

This family-independent certificate absorbs the fixed robust direction-packing
constant before the runtime scale and tube family are chosen.  Its runtime
variable is the coarse scale of the first rich Proposition 6.2 call.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- A pre-runtime cutoff forcing the first rich terminal's fine degree floor
above the fixed `96 * stickyCoarseCloseCount` target. -/
structure Proposition63M9RobustDegreeCutoffData
    (sigma outputLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_small : delta₀ ≤ 1 / 10000
  degree_absorb : ∀ {rho : ℝ}, 0 < rho → rho ≤ delta₀ →
    (12 * ((96 : ENNReal) * stickyCoarseCloseCount)) *
        ENNReal.ofReal Real.pi ≤
      Kakeya.realRpowENN rho (-sigma + 4 * outputLoss)

/-- Freeze the robust degree threshold before any runtime family is known. -/
theorem proposition63_m9_robust_degree_cutoff
    (sigma outputLoss : ℝ)
    (hgap : 4 * outputLoss < sigma) :
    Nonempty (Proposition63M9RobustDegreeCutoffData
      sigma outputLoss) := by
  let target : ENNReal :=
    (12 * ((96 : ENNReal) * stickyCoarseCloseCount)) *
      ENNReal.ofReal Real.pi
  have target_ne_top : target ≠ ⊤ := by
    dsimp only [target, stickyCoarseCloseCount]
    finiteness
  have gap_pos : 0 < sigma - 4 * outputLoss := by
    linarith
  rcases exists_delta_realRpowENN_bound target target_ne_top gap_pos with
    ⟨raw, raw_pos, raw_le_one, bound⟩
  let delta₀ : ℝ := min raw (1 / 10000)
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min raw_pos (by norm_num)
    delta₀_le_one := (min_le_left _ _).trans raw_le_one
    delta₀_le_small := min_le_right _ _
    degree_absorb := ?_ }⟩
  intro rho hrho hrhoLe
  simpa only [target, show -(sigma - 4 * outputLoss) =
      -sigma + 4 * outputLoss by ring] using
    bound rho hrho (hrhoLe.trans (min_le_left _ _))

end Kakeya.Assouad.PureWZ2

end
