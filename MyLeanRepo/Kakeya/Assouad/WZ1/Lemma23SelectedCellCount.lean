import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedPreparedGeometry

/-!
# Selected actual cell count from retained volume in WZ1 Lemma 23

The y-residue package retains a weighted share of the actual exact-slice
cells.  Its volume estimate, together with the stride bound and the exact
spatial grid side, gives

`volume(Y.union) <= 8 * rho^(5/2) * #selectedCells`.

This module turns any retained-volume lower bound into the corresponding
selected-cell lower bound.  The upstream one-scale geometric producer remains
responsible for the paper's lower bound
`volume(Y.union) >= rho^(1 + sigma/2 + O(eta))`.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory

/--
Convert a retained shaded-volume lower bound into a lower bound for the
actual y-residue cell count.
-/
theorem WZ1Lemma23YResiduePackage.cell_count_from_volume
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    (package : WZ1Lemma23YResiduePackage globalPackage)
    (hrho_one : rho ≤ 1)
    (volumeLower : ℝ) (hvolumeLower : 0 ≤ volumeLower)
    (hvolume :
      ENNReal.ofReal volumeLower ≤ volume Y.union) :
    volumeLower /
        (8 * (package.extraCost : ℝ) *
          Real.rpow rho (5 / 2 : ℝ)) ≤
      (package.cells.card : ℝ) := by
  have hrho := globalPackage.rho_pos
  let upper : ENNReal :=
    (((package.volumeCost * package.cells.card : ℕ) : ENNReal) *
      ENNReal.ofReal (gridSide (rho / 2))) *
      (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi)
  have hupper : volume Y.union ≤ upper := by
    simpa [upper] using package.volume_cell_bound
  have hupperFinite : upper ≠ ⊤ := by
    dsimp only [upper]
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top
        (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
    · exact ENNReal.mul_ne_top
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top
  have hlowerUpper :
      ENNReal.ofReal volumeLower ≤ upper :=
    hvolume.trans hupper
  have hlowerReal :
      volumeLower ≤ upper.toReal := by
    have h :=
      (ENNReal.toReal_le_toReal
        ENNReal.ofReal_ne_top hupperFinite).mpr hlowerUpper
    simpa [ENNReal.toReal_ofReal hvolumeLower] using h
  have hside :
      gridSide (rho / 2) = rho / Real.sqrt 3 := by
    simp [gridSide]
    ring
  have hupperReal :
      upper.toReal =
        ((package.volumeCost : ℝ) *
          (package.cells.card : ℝ)) *
          (rho / Real.sqrt 3) *
          (rho ^ 2 * Real.pi) := by
    dsimp only [upper]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by
        rw [hside]
        positivity),
      ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hrho.le,
      ENNReal.toReal_ofReal Real.pi_pos.le]
    rw [hside]
    push_cast
    ring
  have hsqrt : 0 < Real.sqrt rho :=
    Real.sqrt_pos.mpr hrho
  have hsqrt3 : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.mpr (by norm_num)
  have hstride :
      (wz1Lemma23YStride rho : ℝ) ≤
        2 * Real.sqrt 3 / Real.sqrt rho :=
    package.stride_bound
  have hvolumeCost :
      (package.volumeCost : ℝ) ≤
        (wz1Lemma23YStride rho : ℝ) * package.extraCost := by
    exact_mod_cast package.volumeCost_bound
  have hcoefficient :
      (package.volumeCost : ℝ) *
          (rho / Real.sqrt 3) *
          (rho ^ 2 * Real.pi) ≤
        8 * (package.extraCost : ℝ) *
          Real.rpow rho (5 / 2 : ℝ) := by
    have hbase :
        (package.volumeCost : ℝ) *
            (rho / Real.sqrt 3) *
            (rho ^ 2 * Real.pi) ≤
          ((2 * Real.sqrt 3 / Real.sqrt rho) *
            (package.extraCost : ℝ)) *
            (rho / Real.sqrt 3) *
            (rho ^ 2 * 4) := by
      gcongr
      exact hvolumeCost.trans
        (mul_le_mul_of_nonneg_right hstride (by positivity))
      exact Real.pi_le_four
    have hsqrtEq :
        Real.sqrt rho = Real.rpow rho (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow rho
    have hrpowSplit :
        Real.rpow rho (5 / 2 : ℝ) =
          Real.sqrt rho * rho ^ 2 := by
      have htwo :
          Real.rpow rho (2 : ℝ) = rho ^ (2 : ℕ) := by
        simpa using Real.rpow_natCast rho 2
      calc
        Real.rpow rho (5 / 2 : ℝ) =
            Real.rpow rho (1 / 2 + 2 : ℝ) := by
          congr 1
          ring
        _ = Real.rpow rho (1 / 2 : ℝ) *
            Real.rpow rho (2 : ℝ) :=
          Real.rpow_add hrho (1 / 2 : ℝ) 2
        _ = Real.rpow rho (1 / 2 : ℝ) * rho ^ 2 := by
          rw [htwo]
        _ = Real.sqrt rho * rho ^ 2 := by
          rw [hsqrtEq]
    calc
      (package.volumeCost : ℝ) *
            (rho / Real.sqrt 3) *
            (rho ^ 2 * Real.pi)
          ≤ ((2 * Real.sqrt 3 / Real.sqrt rho) *
              (package.extraCost : ℝ)) *
              (rho / Real.sqrt 3) *
              (rho ^ 2 * 4) := hbase
      _ = 8 * (package.extraCost : ℝ) *
          Real.rpow rho (5 / 2 : ℝ) := by
        rw [hrpowSplit]
        have hsqrtSq : Real.sqrt rho * Real.sqrt rho = rho := by
          nlinarith [Real.sq_sqrt hrho.le]
        field_simp [hsqrt.ne', hsqrt3.ne']
        nlinarith [hsqrtSq, Real.sq_sqrt hrho.le]
  have hcountNonneg : 0 ≤ (package.cells.card : ℝ) := by
    positivity
  have hvolumeCount :
      volumeLower ≤
        (8 * (package.extraCost : ℝ) *
          Real.rpow rho (5 / 2 : ℝ)) *
          (package.cells.card : ℝ) := by
    rw [hupperReal] at hlowerReal
    calc
      volumeLower ≤
          ((package.volumeCost : ℝ) *
            (package.cells.card : ℝ)) *
            (rho / Real.sqrt 3) *
            (rho ^ 2 * Real.pi) := hlowerReal
      _ =
          ((package.volumeCost : ℝ) *
            (rho / Real.sqrt 3) *
            (rho ^ 2 * Real.pi)) *
            (package.cells.card : ℝ) := by ring
      _ ≤
          (8 * (package.extraCost : ℝ) *
            Real.rpow rho (5 / 2 : ℝ)) *
            (package.cells.card : ℝ) := by
        gcongr
  have hdenominator :
      0 < 8 * (package.extraCost : ℝ) *
          Real.rpow rho (5 / 2 : ℝ) := by
    exact mul_pos
      (mul_pos (by norm_num) (by exact_mod_cast package.extraCost_pos))
      (Real.rpow_pos_of_pos hrho _)
  exact (div_le_iff₀ hdenominator).2
    (by simpa [mul_comm] using hvolumeCount)

end

end Kakeya.Assouad
