import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Finite representative public pure nearby-scale schedule

The paper's repeated pigeonholing uses only finitely many representative
nearby-scale witnesses.  This interface records the two facts needed to
recover all requested scales:

* each requested scale is assigned to one representative witness whose
  actual scale remains in the allowed enlarged window;
* parent degrees are regularized simultaneously only for those finite
  representative parent maps.

No arbitrary subfamily inheritance of CWA is asserted.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2FiniteNearbyScheduleData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ambientConstant outputConstant : ENNReal)
    (levelCount : ℕ) where
  scaleCount : ℕ
  scaleCount_pos : 0 < scaleCount
  scaleCount_le : scaleCount ≤ levelCount + 1
  gridTopIndex : ℕ
  scaleCount_eq : scaleCount = gridTopIndex + 1
  requested :
    Fin scaleCount →
      WZ2PaperRequestedScale delta
  requested_value :
    ∀ coordinate,
      (requested coordinate).1 =
        min
          (delta * ambientConstant.toReal ^ coordinate.val)
          1
  grid_top_reaches_one :
    1 ≤
      delta * ambientConstant.toReal ^ gridTopIndex
  grid_before_top :
    ∀ index < gridTopIndex,
      delta * ambientConstant.toReal ^ index < 1
  grid_adjacent_nested :
    ∀ index,
      ∀ (hindex : index + 1 < gridTopIndex),
        2 * (requested
              ⟨index, by
                rw [scaleCount_eq]
                omega⟩).1 ≤
          (requested
            ⟨index + 1, by
              rw [scaleCount_eq]
              omega⟩).1
  grid_next_le :
    ∀ index,
      ∀ (hindex : index + 1 ≤ gridTopIndex),
        ENNReal.ofReal
            (requested
              ⟨index + 1, by
                rw [scaleCount_eq]
                omega⟩).1 ≤
          ambientConstant *
            ENNReal.ofReal
              (requested
                ⟨index, by
                  rw [scaleCount_eq]
                  omega⟩).1
  requested_mono :
    ∀ first second : Fin scaleCount,
      first.val ≤ second.val →
        (requested first).1 ≤ (requested second).1
  witness :
    ∀ coordinate,
      WZ2PaperPureNearbyScaleCoverData
        family (requested coordinate) ambientConstant
  representative :
    WZ2PaperRequestedScale delta →
      Fin scaleCount
  requested_grid_le :
    ∀ rho₀,
      rho₀.1 ≤
        (requested (representative rho₀)).1
  requested_before_representative :
    ∀ rho₀,
      ∀ index,
        ∀ (hindex : index < (representative rho₀).val),
        (requested
          ⟨index, hindex.trans (representative rho₀).isLt⟩).1 <
          rho₀.1
  requested_grid_within_ambient :
    ∀ rho₀,
      ENNReal.ofReal
          (requested (representative rho₀)).1 <
        ambientConstant * ENNReal.ofReal rho₀.1
  requested_grid_within_output :
    ∀ rho₀,
      ENNReal.ofReal
          (requested (representative rho₀)).1 <
        outputConstant * ENNReal.ofReal rho₀.1
  requested_le :
    ∀ rho₀,
      rho₀.1 ≤
        (witness (representative rho₀)).rho
  within_output :
    ∀ rho₀,
      ENNReal.ofReal
          (witness (representative rho₀)).rho <
        outputConstant * ENNReal.ofReal rho₀.1

/--
Choose a finite representative schedule from hereditary nearby-scale CWA.

The output constant may be larger than the ambient CWA constant; its
additional loss pays for skipping finitely many intermediate witnesses.
-/
def PureWZ2FiniteNearbyScheduleStatement : Prop :=
  ∀ {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    (levelCount : ℕ),
    0 < delta →
    delta ≤ 1 →
    2 < ambientConstant →
    ambientConstant ≠ ⊤ →
    ENNReal.ofReal (1 / delta) ≤
      ambientConstant ^ levelCount →
    ambientConstant * ambientConstant ≤ outputConstant →
    WZ2PaperPureCWAAtNearbyScales family ambientConstant →
    Nonempty
      (PureWZ2FiniteNearbyScheduleData
        (family := family)
        ambientConstant outputConstant levelCount)

end Kakeya.Assouad

end
