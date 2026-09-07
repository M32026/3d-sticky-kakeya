import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberMultiplicityCapStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SameHeightDiameter

/-!
# Pointwise cap for twisted-projection fiber mass

This closes the geometric leaf bounding the integrated spatial multiplicity
on one exact twisted-projection fiber.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

theorem projected_fiber_multiplicity_cap :
    ProjectedFiberMultiplicityCapStatement := by
  intro delta hdelta F hvert Y f q
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let e1 : Point3 := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
  let e2 : Point3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  let g : ℝ → Point3 := fun y =>
    point3 (q 0 - f (q 1) * y) y (q 1)
  let f1 : ℝ → ℝ := fun y => q 0 - f (q 1) * y
  let f2 : ℝ → ℝ := fun y => y
  let f3 : ℝ → ℝ := fun _ => q 1
  have hf_cont : Continuous f := f.contDiff.continuous
  have h1 : Continuous f1 := by
    exact continuous_const.sub ((hf_cont.comp continuous_const).mul continuous_id)
  have h2 : Continuous f2 := continuous_id
  have h3 : Continuous f3 := continuous_const
  have hg_eq :
      g = fun y : ℝ => (f1 y) • e0 + (f2 y) • e1 + (f3 y) • e2 := by
    funext y
    simp [g, point3, e0, e1, e2, f1, f2, f3]
  have h4 : Continuous (fun y : ℝ => (f1 y) • e0) :=
    h1.smul (show Continuous (fun _ : ℝ => e0) from continuous_const)
  have h5 : Continuous (fun y : ℝ => (f2 y) • e1) :=
    h2.smul (show Continuous (fun _ : ℝ => e1) from continuous_const)
  have h6 : Continuous (fun y : ℝ => (f3 y) • e2) :=
    h3.smul (show Continuous (fun _ : ℝ => e2) from continuous_const)
  have hg_cont : Continuous g := by
    rw [hg_eq]
    exact (h4.add h5).add h6
  have hg_meas : Measurable g := hg_cont.measurable

  have h_pointMult :
      ∀ y : ℝ, (Y.pointMultiplicity (g y) : ENNReal) =
        ∑ i : Fin F.card,
          (Y.carrier i).indicator (fun _ => (1 : ENNReal)) (g y) := by
    intro y
    exact coe_pointMultiplicity_eq_sum_indicator Y (g y)

  have h_meas_terms :
      ∀ i : Fin F.card,
        Measurable (fun y : ℝ =>
          (Y.carrier i).indicator (fun _ => (1 : ENNReal)) (g y)) := by
    intro i
    have h_ind : Measurable (fun p : Point3 =>
        (Y.carrier i).indicator (fun _ => (1 : ENNReal)) p) :=
      (measurable_const : Measurable (fun _ : Point3 => (1 : ENNReal))).indicator
        (Y.measurable_carrier i)
    exact h_ind.comp hg_meas

  have h_main1 :
      projectedFiberMultiplicity Y f q =
        ∑ i : Fin F.card,
          ∫⁻ y : ℝ,
            (Y.carrier i).indicator (fun _ => (1 : ENNReal)) (g y) := by
    calc
      projectedFiberMultiplicity Y f q
          = ∫⁻ y : ℝ, (Y.pointMultiplicity (g y) : ENNReal) := by rfl
      _ = ∫⁻ y : ℝ,
            ∑ i : Fin F.card,
              (Y.carrier i).indicator (fun _ => (1 : ENNReal)) (g y) := by
          apply MeasureTheory.lintegral_congr
          exact h_pointMult
      _ = ∑ i : Fin F.card,
            ∫⁻ y : ℝ,
              (Y.carrier i).indicator (fun _ => (1 : ENNReal)) (g y) := by
          rw [MeasureTheory.lintegral_finsetSum]
          intro i _
          exact h_meas_terms i
  rw [h_main1]

  have h_each : ∀ i : Fin F.card,
      (∫⁻ y : ℝ,
        (Y.carrier i).indicator (fun _ => (1 : ENNReal)) (g y)) ≤
        ENNReal.ofReal (6 * delta) := by
    intro i
    let S_i : Set ℝ := g ⁻¹' (Y.carrier i)
    let T_i : Set ℝ := g ⁻¹' ((F.tube i).carrier)
    have hS_i_meas : MeasurableSet S_i :=
      (Y.measurable_carrier i).preimage hg_meas
    have hS_sub_T : S_i ⊆ T_i := by
      intro y hy
      exact Y.subset_body i hy
    have h_lintegral_eq :
        (∫⁻ y : ℝ,
          (Y.carrier i).indicator (fun _ => (1 : ENNReal)) (g y)) =
          MeasureTheory.volume S_i := by
      have h :
          (∫⁻ y : ℝ,
            (Y.carrier i).indicator (fun _ => (1 : ENNReal)) (g y)) =
            (1 : ENNReal) * MeasureTheory.volume (g ⁻¹' (Y.carrier i)) :=
        @MeasureTheory.lintegral_indicator_const_comp
          ℝ Point3 _ _ MeasureTheory.volume g (Y.carrier i)
          hg_meas (Y.measurable_carrier i) (1 : ENNReal)
      simpa [S_i, one_mul] using h
    rw [h_lintegral_eq]
    have h_diam : ∀ y1 ∈ T_i, ∀ y2 ∈ T_i, dist y1 y2 ≤ 6 * delta := by
      intro y1 hy1 y2 hy2
      let p1 : Point3 := g y1
      let p2 : Point3 := g y2
      have hp1 : p1 ∈ (F.tube i).carrier := hy1
      have hp2 : p2 ∈ (F.tube i).carrier := hy2
      have hz1 : p1 (2 : Fin 3) = q 1 := by
        simp [p1, g, point3]
      have hz2 : p2 (2 : Fin 3) = q 1 := by
        simp [p2, g, point3]
      have h_abs : |p1 1 - p2 1| ≤ 6 * delta :=
        tube_same_height_y_diameter hdelta hvert i hp1 hp2 hz1 hz2
      have h_p1y : p1 1 = y1 := by simp [p1, g, point3]
      have h_p2y : p2 1 = y2 := by simp [p2, g, point3]
      rw [h_p1y, h_p2y] at h_abs
      simpa [Real.dist_eq] using h_abs
    calc
      MeasureTheory.volume S_i ≤ MeasureTheory.volume T_i :=
        MeasureTheory.measure_mono hS_sub_T
      _ ≤ Metric.ediam T_i := Real.volume_le_diam T_i
      _ ≤ ENNReal.ofReal (6 * delta) :=
        Metric.ediam_le_of_forall_dist_le h_diam

  have h_sum :
      (∑ i : Fin F.card,
        ∫⁻ y : ℝ,
          (Y.carrier i).indicator (fun _ => (1 : ENNReal)) (g y)) ≤
      ∑ i : Fin F.card, ENNReal.ofReal (6 * delta) :=
    Finset.sum_le_sum fun i _ => h_each i
  have h_final :
      (∑ i : Fin F.card, ENNReal.ofReal (6 * delta)) =
        ENNReal.ofReal (6 * delta) * F.enncard := by
    have h1 :
        (∑ i : Fin F.card, ENNReal.ofReal (6 * delta)) =
          (F.card : ENNReal) * ENNReal.ofReal (6 * delta) := by
      rw [Finset.sum_const, Finset.card_fin]
      simp
    have h2 : F.enncard = (F.card : ENNReal) := by
      simp [Kakeya.Streamlined.TubeFamily.enncard]
    rw [h1, h2]
    exact mul_comm _ _
  rw [h_final] at h_sum
  exact h_sum

end Kakeya.Assouad
