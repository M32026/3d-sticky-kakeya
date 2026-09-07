import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement

/-! # Aggregate mass from pointwise multiplicity retention -/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
If `Z` retains at least one quarter of `Y`'s pointwise multiplicity, then it
retains at least one quarter of its aggregate shaded mass.
-/
lemma mass_lower_from_pointMultiplicity
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z Y : Kakeya.Streamlined.TubeShading F}
    (h_mult :
      ∀ p ∈ Y.union,
        Y.pointMultiplicity p ≤ 4 * Z.pointMultiplicity p) :
    (1 / 4 : ENNReal) * Y.mass ≤ Z.mass := by
  have h1 : ∀ p : Point3,
      (Y.pointMultiplicity p : ENNReal) ≤
        4 * (Z.pointMultiplicity p : ENNReal) := by
    intro p
    by_cases hp : p ∈ Y.union
    · exact_mod_cast h_mult p hp
    · have hY0 : Y.pointMultiplicity p = 0 := by
        simpa [Kakeya.Streamlined.Shading.pointMultiplicity,
          Kakeya.Streamlined.Shading.union] using hp
      rw [hY0]
      simp
  have h2 :
      (∫⁻ p, (Y.pointMultiplicity p : ENNReal)) ≤
        ∫⁻ p, 4 * (Z.pointMultiplicity p : ENNReal) :=
    MeasureTheory.lintegral_mono h1
  have hZmeas :
      Measurable fun p : Point3 =>
        (Z.pointMultiplicity p : ENNReal) := by
    have h_eq :
        (fun p : Point3 => (Z.pointMultiplicity p : ENNReal)) =
          fun p =>
            ∑ i : Fin F.card,
              (Z.carrier i).indicator (fun _ => (1 : ENNReal)) p := by
      funext p
      exact coe_pointMultiplicity_eq_sum_indicator Z p
    rw [h_eq]
    exact Finset.measurable_sum _ (fun i _ =>
      measurable_const.indicator (Z.measurable_carrier i))
  have h3 :
      (∫⁻ p, 4 * (Z.pointMultiplicity p : ENNReal)) =
        4 * (∫⁻ p, (Z.pointMultiplicity p : ENNReal)) := by
    rw [MeasureTheory.lintegral_const_mul]
    exact hZmeas
  rw [lintegral_pointMultiplicity Y, h3,
    lintegral_pointMultiplicity Z] at h2
  have h7 :
      (1 / 4 : ENNReal) * Y.mass ≤
        (1 / 4 : ENNReal) * (4 * Z.mass) :=
    mul_le_mul_right h2 (1 / 4 : ENNReal)
  have h8 : (1 / 4 : ENNReal) * (4 * Z.mass) = Z.mass := by
    simpa [div_eq_mul_inv] using
      ENNReal.inv_mul_cancel_left
        (show (4 : ENNReal) ≠ 0 by norm_num)
        (show (4 : ENNReal) ≠ ⊤ by norm_num)
  rw [h8] at h7
  exact h7

end Kakeya.Assouad
