import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.FixedDepthPowerGridData.Proof

/-!
# Increasing view of the fixed-depth power grid

The random-tail induction uses the paper's descending order from `1` to
`delta`.  `GridScaleData` uses the opposite order.  This module records the
exact dependent reversal once, independently of any selection theorem.
-/

noncomputable section

open Kakeya.Streamlined

namespace Kakeya.Streamlined.RandomTranslation.WithShading

namespace FixedDepthPowerGrid

variable {delta : ℝ} {N : ℕ}

/-- The same power grid, indexed increasingly from `delta` to `1`. -/
def increasingScale (grid : FixedDepthPowerGrid delta N) :
    Fin (N + 1) → AdmissibleScale delta :=
  fun i => grid.scale i.rev

lemma increasingScale_strict
    (grid : FixedDepthPowerGrid delta N) (i : Fin N) :
    (grid.increasingScale (Fin.castSucc i)).1 <
      (grid.increasingScale (Fin.succ i)).1 := by
  simpa only [increasingScale, Fin.rev_castSucc, Fin.rev_succ] using
    grid.hstrict i.rev

@[simp]
lemma increasingScale_zero
    (grid : FixedDepthPowerGrid delta N) :
    (grid.increasingScale 0).1 = delta := by
  rw [increasingScale, Fin.rev_zero]
  exact grid.hlast

@[simp]
lemma increasingScale_last
    (grid : FixedDepthPowerGrid delta N) :
    (grid.increasingScale (Fin.last N)).1 = 1 := by
  rw [increasingScale, Fin.rev_last]
  exact grid.hfirst

lemma increasingScale_ratio
    (grid : FixedDepthPowerGrid delta N) (i : Fin N) :
    ENNReal.ofReal
        (grid.increasingScale (Fin.succ i)).1 =
      Kakeya.realRpowENN delta (-(1 / (N : ℝ))) *
        ENNReal.ofReal
          (grid.increasingScale (Fin.castSucc i)).1 := by
  simpa only [increasingScale, Fin.rev_succ, Fin.rev_castSucc] using
    grid.hratio i.rev

end FixedDepthPowerGrid

end Kakeya.Streamlined.RandomTranslation.WithShading

end
