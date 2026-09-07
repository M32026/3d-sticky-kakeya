import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCellAreaUniformityStatement

/-!
# Planar cell-area uniformity after projected-fiber OS branching

Convert same-level projected cell-mass uniformity into factor-four planar
area uniformity and identify the exact final twisted support.
-/

open MeasureTheory

namespace Kakeya.Assouad

theorem projected_fiber_os_cell_area_uniformity :
    ProjectedFiberOSCellAreaUniformityStatement := by
  intro hPullback hBandCmp delta F Y f threshold hth0 hthtop
    levelCount bandData base levels indexBound atomized uniform cellMass
  let lam := projectedFiberBandValue Y f bandData
  have hlam0 : lam ≠ 0 := by
    simp only [lam, projectedFiberBandValue]
    positivity
  have hlamtop : lam ≠ ⊤ := by
    simp only [lam, projectedFiberBandValue]
    apply ENNReal.mul_ne_top hthtop
    exact Ne.symm (not_eq_of_beq_eq_false rfl)
  have h_subset : ∀ (level : ℕ), level ≤ levels + 1 →
      ∀ cell ∈ planarGridPartition base level atomized.centers,
        projectedFiberOSCellBand
            Y f bandData base levels uniform.centers cell ⊆
          bandData.band := by
    intro level hlevel cell hcell
    have h1 :
        projectedFiberOSCellBand
            Y f bandData base levels uniform.centers cell ⊆
          uniform.retainedBand :=
      cellMass.cellBand_subset level hlevel cell hcell
    have h2 : uniform.retainedBand ⊆ atomized.retainedBand :=
      uniform.retainedBand_subset
    have h3 : atomized.retainedBand ⊆ bandData.band :=
      atomized.retainedBand_subset
    exact Set.Subset.trans h1 (Set.Subset.trans h2 h3)
  have h_bandcmp : ∀ (level : ℕ), level ≤ levels + 1 →
      ∀ cell ∈ planarGridPartition base level atomized.centers,
        lam *
              volume
                (projectedFiberOSCellBand
                  Y f bandData base levels uniform.centers cell) ≤
            projectedFiberMeasure Y f
              (projectedFiberOSCellBand
                Y f bandData base levels uniform.centers cell) ∧
          projectedFiberMeasure Y f
                (projectedFiberOSCellBand
                  Y f bandData base levels uniform.centers cell) ≤
            2 * lam *
              volume
                (projectedFiberOSCellBand
                  Y f bandData base levels uniform.centers cell) := by
    intro level hlevel cell hcell
    have hmeas :
        MeasurableSet
          (projectedFiberOSCellBand
            Y f bandData base levels uniform.centers cell) :=
      cellMass.cellBand_measurable level hlevel cell hcell
    have hsub :
        projectedFiberOSCellBand
            Y f bandData base levels uniform.centers cell ⊆
          bandData.band :=
      h_subset level hlevel cell hcell
    exact hBandCmp F Y f bandData
      (projectedFiberOSCellBand
        Y f bandData base levels uniform.centers cell)
      hmeas hsub
  have h_twisted :
      twistedUnion uniform.shading f = uniform.retainedBand := by
    have h_mult :
        ∀ q ∈ uniform.retainedBand,
          projectedFiberMultiplicity Y f q ≠ 0 := by
      intro q hq
      have hq2 : q ∈ atomized.retainedBand :=
        uniform.retainedBand_subset hq
      have hq3 : q ∈ bandData.band :=
        atomized.retainedBand_subset hq2
      have h4 : lam ≤ projectedFiberMultiplicity Y f q :=
        bandData.fiber_lower q hq3
      have h5 : (0 : ENNReal) < lam :=
        bot_lt_iff_ne_bot.mpr hlam0
      exact ne_of_gt (lt_of_lt_of_le h5 h4)
    have h5 := hPullback (F := F) (Y := Y) (f := f)
      (X := uniform.retainedBand) uniform.retainedBand_measurable h_mult
    simpa [uniform.shading_eq] using h5
  refine' ⟨h_twisted, _, _, _⟩
  · intro level hlevel cell hcell hnonempty
    set X :=
      projectedFiberOSCellBand
        Y f bandData base levels uniform.centers cell with hX
    have h := h_bandcmp level hlevel cell hcell
    have h6 : projectedFiberMeasure Y f X ≤ 2 * lam * volume X :=
      h.2
    by_contra h7
    have h7' : volume X = 0 := h7
    rw [h7'] at h6
    have h8 : 2 * lam * (0 : ENNReal) = 0 :=
      mul_zero (2 * lam)
    rw [h8] at h6
    have h9 : projectedFiberMeasure Y f X ≤ 0 := h6
    have h10 : projectedFiberMeasure Y f X = 0 := by
      simpa using h9
    exact cellMass.cellBand_nonzero
      level hlevel cell hcell hnonempty h10
  · intro level hlevel cell hcell
    set X :=
      projectedFiberOSCellBand
        Y f bandData base levels uniform.centers cell with hX
    have h := h_bandcmp level hlevel cell hcell
    have h6 : lam * volume X ≤ projectedFiberMeasure Y f X :=
      h.1
    by_contra h7
    have h7' : volume X = ⊤ := h7
    rw [h7'] at h6
    have h9 : lam * (⊤ : ENNReal) = ⊤ :=
      ENNReal.mul_top hlam0
    rw [h9] at h6
    have h10 : projectedFiberMeasure Y f X = ⊤ :=
      top_le_iff.mp h6
    exact cellMass.cellBand_ne_top level hlevel cell hcell h10
  · intro level hlevel cell₁ hcell₁ hnonempty₁
      cell₂ hcell₂ hnonempty₂
    set X₁ :=
      projectedFiberOSCellBand
        Y f bandData base levels uniform.centers cell₁ with hX₁
    set X₂ :=
      projectedFiberOSCellBand
        Y f bandData base levels uniform.centers cell₂ with hX₂
    have h1 : lam * volume X₁ ≤ projectedFiberMeasure Y f X₁ :=
      (h_bandcmp level hlevel cell₁ hcell₁).1
    have h2 :
        projectedFiberMeasure Y f X₁ ≤
          2 * projectedFiberMeasure Y f X₂ :=
      cellMass.cell_mass_comparable
        level hlevel cell₁ hcell₁ hnonempty₁
        cell₂ hcell₂ hnonempty₂
    have h3 :
        projectedFiberMeasure Y f X₂ ≤ 2 * lam * volume X₂ :=
      (h_bandcmp level hlevel cell₂ hcell₂).2
    have h41 :
        2 * (2 * lam * volume X₂) = lam * (4 * volume X₂) := by
      have h5 :
          2 * (2 * lam * volume X₂) =
            (2 * 2 : ENNReal) * (lam * volume X₂) := by
        simp [mul_assoc]
      rw [h5]
      have h6 : (2 * 2 : ENNReal) = 4 := by norm_num
      rw [h6]
      have h7 :
          (4 : ENNReal) * (lam * volume X₂) =
            lam * (4 * volume X₂) := by
        simp [mul_left_comm]
      exact h7
    have h4 : lam * volume X₁ ≤ lam * (4 * volume X₂) := by
      calc
        lam * volume X₁
            ≤ projectedFiberMeasure Y f X₁ := h1
        _ ≤ 2 * projectedFiberMeasure Y f X₂ := h2
        _ ≤ 2 * (2 * lam * volume X₂) := by gcongr
        _ = lam * (4 * volume X₂) := h41
    exact (ENNReal.mul_le_mul_iff_right hlam0 hlamtop).mp h4

end Kakeya.Assouad
