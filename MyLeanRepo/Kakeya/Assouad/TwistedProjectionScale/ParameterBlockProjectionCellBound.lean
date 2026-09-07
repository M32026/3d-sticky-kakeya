import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionArithmeticStatement

/-!
# Linear globalization cost at the selected Lemma 7.10 scale

At a grid level comparable to `rho`, the cinematic corridor meets
`O_base(rho⁻¹)` cells and each cell has `rho`-thickening area
`O_base(rho²)`.  Their product is therefore `O_base(rho)`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Fixed second-coordinate factor in the cinematic corridor cell count. -/
def parameterBlockProjectionSlopeFactor (base : ℕ) : ℕ :=
  let radiusBlocks := parameterBlockProjectionRadiusBlocks base
  2 * (2 * radiusBlocks +
    131 * (1 + 2 * radiusBlocks) + 2) + 3

/-- Fixed base-dependent coefficient in the Lemma 7.12 globalization cost. -/
def parameterBlockProjectionCellConstant (base : ℕ) : ENNReal :=
  let radiusBlocks := parameterBlockProjectionRadiusBlocks base
  4 *
    ((base + 2 * radiusBlocks + 3 : ℕ) : ENNReal) *
    (parameterBlockProjectionSlopeFactor base : ENNReal) *
    ENNReal.ofReal
      (Real.pi * (2 * (base : ℝ) + 3) ^ 2)

/--
The full cinematic cell-count/thickening factor is bounded by one fixed
base-dependent constant times the selected radius.
-/
lemma parameterBlockProjection_cellFactor_le
    {delta eta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {f : SlopeFunction}
    (prepared :
      ProjectedFiberOSPreparationData (eta := eta) Y f)
    (base level : ℕ)
    (hbase : prepared.base = base)
    (cellSystem :
      ProjectedFiberOSLevelCellSystemData
        (rho := rho) prepared level)
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1) :
    4 *
        (projectedFiberOSCinematicCellBound
          prepared.base level 131
          (parameterBlockProjectionRadiusBlocks base) : ENNReal) *
        projectedFiberOSPreparedCellThickeningBound prepared rho ≤
      parameterBlockProjectionCellConstant base *
        ENNReal.ofReal rho := by
  let radiusBlocks := parameterBlockProjectionRadiusBlocks base
  let slopeFactor := parameterBlockProjectionSlopeFactor base
  let basePower : ℕ := prepared.base ^ level
  have hbase_pos : (0 : ℝ) < prepared.base := by
    exact_mod_cast
      (show 0 < prepared.base from
        lt_of_lt_of_le (by norm_num) prepared.base_ge_three)
  have hbasePower_pos : (0 : ℝ) < basePower := by
    exact_mod_cast
      (show 0 < basePower by
        dsimp only [basePower]
        exact pow_pos
          (show 0 < prepared.base from
            lt_of_lt_of_le (by norm_num)
              prepared.base_ge_three) level)
  have hbasePower_rho_real :
      (basePower : ℝ) * rho ≤ prepared.base := by
    have hstrict := cellSystem.rho_lt_coarse_mesh
    have hmultiply :=
      mul_lt_mul_of_pos_right hstrict hbasePower_pos
    have hcancel :
        ((prepared.base : ℝ) *
            (prepared.base ^ level : ℝ)⁻¹) *
              (basePower : ℝ) =
          prepared.base := by
      dsimp only [basePower]
      norm_cast
      field_simp
    rw [hcancel] at hmultiply
    linarith
  have hbasePower_rho :
      (basePower : ENNReal) * ENNReal.ofReal rho ≤
        (prepared.base : ENNReal) := by
    have hnonneg : 0 ≤ (basePower : ℝ) := hbasePower_pos.le
    have hproduct :
        (basePower : ENNReal) * ENNReal.ofReal rho =
          ENNReal.ofReal ((basePower : ℝ) * rho) := by
      rw [show (basePower : ENNReal) =
        ENNReal.ofReal (basePower : ℝ) by simp,
        ← ENNReal.ofReal_mul hnonneg]
    rw [hproduct]
    simpa using ENNReal.ofReal_mono hbasePower_rho_real
  have hrho_enn :
      ENNReal.ofReal rho ≤ 1 := by
    simpa using ENNReal.ofReal_mono hrho_one
  have hfirst :
      ((basePower : ENNReal) +
          (2 * radiusBlocks + 3 : ℕ)) *
          ENNReal.ofReal rho ≤
        (base + 2 * radiusBlocks + 3 : ℕ) := by
    rw [add_mul]
    calc
      (basePower : ENNReal) * ENNReal.ofReal rho +
            ((2 * radiusBlocks + 3 : ℕ) : ENNReal) *
              ENNReal.ofReal rho ≤
          (prepared.base : ENNReal) +
            ((2 * radiusBlocks + 3 : ℕ) : ENNReal) * 1 := by
        gcongr
      _ = (base + 2 * radiusBlocks + 3 : ℕ) := by
        rw [hbase]
        norm_cast
        ring
  have hcellCount :
      (projectedFiberOSCinematicCellBound
          prepared.base level 131 radiusBlocks : ENNReal) *
          ENNReal.ofReal rho ≤
        ((base + 2 * radiusBlocks + 3 : ℕ) : ENNReal) *
          (slopeFactor : ENNReal) := by
    have hcellCast :
        (projectedFiberOSCinematicCellBound
          prepared.base level 131 radiusBlocks : ENNReal) =
          ((basePower : ENNReal) +
            ((2 * radiusBlocks + 3 : ℕ) : ENNReal)) *
            (slopeFactor : ENNReal) := by
      dsimp only [projectedFiberOSCinematicCellBound,
        basePower, slopeFactor,
        parameterBlockProjectionSlopeFactor]
      norm_cast
    rw [hcellCast]
    calc
      (((basePower : ENNReal) +
            (2 * radiusBlocks + 3 : ℕ)) *
            (slopeFactor : ENNReal)) *
            ENNReal.ofReal rho =
          (((basePower : ENNReal) +
            (2 * radiusBlocks + 3 : ℕ)) *
            ENNReal.ofReal rho) *
            (slopeFactor : ENNReal) := by ring
      _ ≤
          ((base + 2 * radiusBlocks + 3 : ℕ) : ENNReal) *
            (slopeFactor : ENNReal) := by
        gcongr
  have hthickening :
      projectedFiberOSPreparedCellThickeningBound prepared rho =
        ENNReal.ofReal
            (Real.pi * (2 * (base : ℝ) + 3) ^ 2) *
          ENNReal.ofReal rho * ENNReal.ofReal rho := by
    simp only [projectedFiberOSPreparedCellThickeningBound]
    rw [hbase]
    have hfixed_nonneg :
        0 ≤ Real.pi * (2 * (base : ℝ) + 3) ^ 2 := by
      positivity
    have hrho_nonneg : 0 ≤ rho := hrho.le
    rw [show
      ((((2 * base + 3 : ℕ) : ℝ) * rho) ^ 2) * Real.pi =
        (Real.pi * (2 * (base : ℝ) + 3) ^ 2) *
          (rho * rho) by
      norm_num
      ring]
    rw [ENNReal.ofReal_mul hfixed_nonneg,
      ENNReal.ofReal_mul hrho_nonneg]
    ring
  rw [hthickening]
  simp only [parameterBlockProjectionCellConstant]
  change
    4 *
        (projectedFiberOSCinematicCellBound
          prepared.base level 131 radiusBlocks : ENNReal) *
        (ENNReal.ofReal
            (Real.pi * (2 * (base : ℝ) + 3) ^ 2) *
          ENNReal.ofReal rho * ENNReal.ofReal rho) ≤
      4 *
        ((base + 2 * radiusBlocks + 3 : ℕ) : ENNReal) *
        (slopeFactor : ENNReal) *
        ENNReal.ofReal
          (Real.pi * (2 * (base : ℝ) + 3) ^ 2) *
        ENNReal.ofReal rho
  calc
    4 *
          (projectedFiberOSCinematicCellBound
            prepared.base level 131 radiusBlocks : ENNReal) *
          (ENNReal.ofReal
              (Real.pi * (2 * (base : ℝ) + 3) ^ 2) *
            ENNReal.ofReal rho * ENNReal.ofReal rho) =
        4 *
          ((projectedFiberOSCinematicCellBound
              prepared.base level 131 radiusBlocks : ENNReal) *
            ENNReal.ofReal rho) *
          ENNReal.ofReal
            (Real.pi * (2 * (base : ℝ) + 3) ^ 2) *
          ENNReal.ofReal rho := by ring
    _ ≤
        4 *
          (((base + 2 * radiusBlocks + 3 : ℕ) : ENNReal) *
            (slopeFactor : ENNReal)) *
          ENNReal.ofReal
            (Real.pi * (2 * (base : ℝ) + 3) ^ 2) *
          ENNReal.ofReal rho := by
      gcongr
    _ =
        4 *
          ((base + 2 * radiusBlocks + 3 : ℕ) : ENNReal) *
          (slopeFactor : ENNReal) *
          ENNReal.ofReal
            (Real.pi * (2 * (base : ℝ) + 3) ^ 2) *
          ENNReal.ofReal rho := by ring

end Kakeya.Assouad
