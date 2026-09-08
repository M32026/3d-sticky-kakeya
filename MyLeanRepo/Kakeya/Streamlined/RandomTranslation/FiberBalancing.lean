import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FiberMassBound
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FrostmanAssembly

/-!
# Fiber mass balancing across scales

Provides uniform lower bounds on fiber mass and upper bounds on coarse body
volume across all admissible scales, by applying the single-scale
`fiberMass_lower_bound` and monotonicity of `deltaTubeVolume`.

## Main result

`fiberBalancing`: given a uniform tube structure with Katz–Tao bounds at every
scale, produce uniform `m > 0`, `m ≠ ⊤` and `V ≠ ⊤` such that every fiber at every
scale has mass `≥ m` and every coarse body has volume `≤ V`.
-/

noncomputable section

open MeasureTheory Kakeya.Streamlined Kakeya.Streamlined.RandomTranslation Metric

namespace Kakeya.Streamlined.RandomTranslation

/-- `deltaTubeVolume` is monotone in the radius. -/
lemma deltaTubeVolume_monotone {r1 r2 : ℝ} (h : r1 ≤ r2) (hr1 : 0 ≤ r1) :
    Kakeya.deltaTubeVolume r1 ≤ Kakeya.deltaTubeVolume r2 := by
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) 1
  let S : Set Point3 := unitSegment 0 e0
  have h1 : Metric.cthickening r1 S ⊆ Metric.cthickening r2 S :=
    Metric.cthickening_mono (α := Point3) h S
  exact measure_mono h1

/-- Uniform fiber mass and coarse volume bounds across all admissible scales. -/
theorem fiberBalancing
    {δ : ℝ} {F : TubeFamily δ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hF_ball : F.IsInUnitBall)
    (hF_nonempty : F.Nonempty)
    (U : AssignedUniformTubeStructure F)
    {C_KT : ENNReal} (hKT : U.IsKatzTaoAtEveryScale C_KT)
    (hC_KT_pos : 0 < C_KT) (hC_KT_ne_top : C_KT ≠ ⊤) :
    ∃ (m V : ENNReal), 0 < m ∧ m ≠ ⊤ ∧ V ≠ ⊤ ∧
      (∀ (rho : AdmissibleScale δ) (j : Fin (U.coarse rho).toBodyFamily.card),
        (U.cover rho).toFactoring.fiberMass j ≥ m) ∧
      (∀ (rho : AdmissibleScale δ) (j : Fin (U.coarse rho).toBodyFamily.card),
        ((U.coarse rho).toBodyFamily.body j).volume ≤ V) := by
  let Vδ := Kakeya.deltaTubeVolume δ
  let V1 := Kakeya.deltaTubeVolume 1
  let B5 := closedBall (0 : Point3) 5
  let V_B5 := volume B5
  let m := F.nominalMass * Vδ / (C_KT * V_B5 * U.assignedUniformity)

  have hVδ_pos : 0 < Vδ := deltaTubeVolume_pos hδ
  have hVδ_ne_top : Vδ ≠ ⊤ := deltaTubeVolume_ne_top (δ := δ)
  have hV1_ne_top : V1 ≠ ⊤ := deltaTubeVolume_ne_top (δ := 1)
  have hB5_pos : 0 < V_B5 := by
    have h_ball : ball (0 : Point3) 5 ⊆ B5 := ball_subset_closedBall
    have h_pos : 0 < volume (ball (0 : Point3) 5) :=
      Metric.measure_ball_pos volume (0 : Point3) (by norm_num)
    exact lt_of_lt_of_le h_pos (measure_mono h_ball)
  have hB5_ne_top : V_B5 ≠ ⊤ := isBounded_closedBall.measure_lt_top.ne
  have hU_pos : 0 < U.assignedUniformity := by
    have h1 : 1 ≤ U.assignedUniformity := (U.assignedUniform (⟨δ, by linarith, by linarith⟩)).1
    exact zero_lt_one.trans_le h1
  have hU_ne_top : U.assignedUniformity ≠ ⊤ := U.assignedUniformity_ne_top
  have h_nominal_pos : 0 < F.nominalMass := nominalMass_pos hδ hF_nonempty
  have h_nominal_ne_top : F.nominalMass ≠ ⊤ := by
    have h1 : F.enncard ≠ ⊤ := by simp [TubeFamily.enncard]
    exact ENNReal.mul_ne_top h1 hVδ_ne_top
  have h_denom_pos : 0 < C_KT * V_B5 * U.assignedUniformity := by
    positivity
  have h_denom_ne_top : (C_KT * V_B5 * U.assignedUniformity) ≠ ⊤ := by
    have h1 : C_KT * V_B5 ≠ ⊤ := ENNReal.mul_ne_top hC_KT_ne_top hB5_ne_top
    exact ENNReal.mul_ne_top h1 hU_ne_top
  have h_num_pos : 0 < F.nominalMass * Vδ := ENNReal.mul_pos h_nominal_pos.ne' hVδ_pos.ne'
  have h_num_ne_top : F.nominalMass * Vδ ≠ ⊤ := ENNReal.mul_ne_top h_nominal_ne_top hVδ_ne_top
  have h_m_pos : 0 < m := by
    dsimp only [m]
    exact ENNReal.div_pos h_num_pos.ne' h_denom_ne_top
  have h_m_ne_top : m ≠ ⊤ := by
    dsimp only [m]
    exact ENNReal.div_ne_top h_num_ne_top h_denom_pos.ne'

  have h_fiber_mass : ∀ (rho : AdmissibleScale δ) (j : Fin (U.coarse rho).toBodyFamily.card),
      (U.cover rho).toFactoring.fiberMass j ≥ m := by
    intro rho j
    have h1 := fiberMass_lower_bound hδ hδ1 hF_ball U hKT rho j
    have h2 : Vδ ≤ Kakeya.deltaTubeVolume rho.val :=
      deltaTubeVolume_monotone rho.2.1 (by linarith)
    have h3 : F.nominalMass * Vδ ≤ F.nominalMass * Kakeya.deltaTubeVolume rho.val := by
      gcongr
    have h4 : F.nominalMass * Kakeya.deltaTubeVolume rho.val / (C_KT * V_B5 * U.assignedUniformity) ≥
        F.nominalMass * Vδ / (C_KT * V_B5 * U.assignedUniformity) := by
      gcongr
    exact h4.trans h1

  have h_coarse_vol : ∀ (rho : AdmissibleScale δ) (j : Fin (U.coarse rho).toBodyFamily.card),
      ((U.coarse rho).toBodyFamily.body j).volume ≤ V1 := by
    intro rho j
    let G := U.coarse rho
    let eG : Fin G.toBodyFamily.card ≃ Fin G.card :=
      Equiv.cast (by simp [TubeFamily.toBodyFamily])
    have h_vol : ((U.coarse rho).toBodyFamily.body j).volume =
        Kakeya.deltaTubeVolume rho.val := by
      exact tube_volume_eq_deltaTubeVolume (G.tube (eG j))
    rw [h_vol]
    exact deltaTubeVolume_monotone rho.2.2 (by linarith [hδ, rho.2.1])

  exact ⟨m, V1, h_m_pos, h_m_ne_top, hV1_ne_top, h_fiber_mass, h_coarse_vol⟩

end Kakeya.Streamlined.RandomTranslation
