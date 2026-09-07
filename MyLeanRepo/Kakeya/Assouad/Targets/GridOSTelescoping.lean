import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSTelescopingStatement

/-!
WZ2 Proposition 7.1: telescope finitely many corrected grid OS projection
comparisons.

## Proof route

Induct on `steps`. In the base case the ratio `scale 0 / scale 0` is `1` and
`6889 ^ 0 = 1`. In the inductive step, split

`scale 0 / scale (steps + 1) = (scale 0 / scale steps) * (scale steps / scale (steps + 1))`

and use `realRpowENN_mul_base` to distribute the power over the product.
Multiply the one-step bound at `index = steps` with the inductive hypothesis
and reassociate the constant `6889`.
-/

namespace Kakeya.Assouad

/-- Distribute `realRpowENN` over a product of positive bases. -/
private lemma realRpowENN_mul_base {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (e : ℝ) :
    Kakeya.realRpowENN (x * y) e =
      Kakeya.realRpowENN x e * Kakeya.realRpowENN y e := by
  have h1 : Real.rpow (x * y) e = Real.rpow x e * Real.rpow y e :=
    Real.mul_rpow hx.le hy.le
  have h2 : 0 ≤ Real.rpow x e := Real.rpow_nonneg hx.le e
  simp only [Kakeya.realRpowENN, h1, ENNReal.ofReal_mul h2]

theorem grid_os_telescoping :
    GridOSTelescopingStatement := by
  intro epsilon steps scale projectedVolume
  induction steps with
  | zero =>
    intro h_scale _
    have h_pos0 : 0 < scale 0 := h_scale 0 (by norm_num)
    have h1 : scale 0 / scale 0 = 1 := div_self (ne_of_gt h_pos0)
    rw [h1]
    have h2 : Kakeya.realRpowENN (1 : ℝ) epsilon = 1 := by
      simp [Kakeya.realRpowENN]
    rw [h2]
    simp
  | succ steps ih =>
    intro h_scale h_step
    have h_scale' : ∀ index, index ≤ steps → 0 < scale index :=
      fun index h => h_scale index (by linarith)
    have h_step' : ∀ index, index < steps →
        Kakeya.realRpowENN (scale index / scale (index + 1)) epsilon *
        projectedVolume (index + 1) ≤ (6889 : ENNReal) * projectedVolume index :=
      fun index h => h_step index (by linarith)
    have ih' := ih h_scale' h_step'
    have h_steps_pos : 0 < scale steps := h_scale steps (by linarith)
    have h_next_pos : 0 < scale (steps + 1) := h_scale (steps + 1) (by linarith)
    have h0_pos : 0 < scale 0 := h_scale 0 (by linarith)
    have h_steps_ne : scale steps ≠ 0 := ne_of_gt h_steps_pos
    have h_next_ne : scale (steps + 1) ≠ 0 := ne_of_gt h_next_pos
    have h_pos0 : 0 < scale 0 / scale steps := div_pos h0_pos h_steps_pos
    have h_pos1 : 0 < scale steps / scale (steps + 1) := div_pos h_steps_pos h_next_pos
    have h_ratio : scale 0 / scale (steps + 1) =
        (scale 0 / scale steps) * (scale steps / scale (steps + 1)) := by
      field_simp [h_steps_ne, h_next_ne]
    have h_rpow : Kakeya.realRpowENN (scale 0 / scale (steps + 1)) epsilon =
        Kakeya.realRpowENN (scale 0 / scale steps) epsilon *
        Kakeya.realRpowENN (scale steps / scale (steps + 1)) epsilon := by
      rw [h_ratio]
      exact realRpowENN_mul_base h_pos0 h_pos1 epsilon
    have h_one_step : Kakeya.realRpowENN (scale steps / scale (steps + 1)) epsilon *
        projectedVolume (steps + 1) ≤ (6889 : ENNReal) * projectedVolume steps :=
      h_step steps (by linarith)
    rw [h_rpow]
    calc
      (Kakeya.realRpowENN (scale 0 / scale steps) epsilon *
       Kakeya.realRpowENN (scale steps / scale (steps + 1)) epsilon) *
       projectedVolume (steps + 1)
        = Kakeya.realRpowENN (scale 0 / scale steps) epsilon *
          (Kakeya.realRpowENN (scale steps / scale (steps + 1)) epsilon *
           projectedVolume (steps + 1)) := by ring
      _ ≤ Kakeya.realRpowENN (scale 0 / scale steps) epsilon *
          ((6889 : ENNReal) * projectedVolume steps) := by gcongr
      _ = (6889 : ENNReal) *
          (Kakeya.realRpowENN (scale 0 / scale steps) epsilon *
           projectedVolume steps) := by ring
      _ ≤ (6889 : ENNReal) * ((6889 : ENNReal) ^ steps * projectedVolume 0) := by
          gcongr
      _ = (6889 : ENNReal) ^ (steps + 1) * projectedVolume 0 := by
          rw [pow_succ]; ac_rfl

end Kakeya.Assouad
