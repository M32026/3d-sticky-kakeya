import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds
import MyLeanRepo.Kakeya.Streamlined.MaximalDensityFactoring.DensityMax

/-!
# Maximal convex density for a bounded tube family

Two elementary bounds used by the Node-7 analytic cleanup.  They depend only
on equal positive finite tube volume and on support in a fixed ball; no
essential-distinctness or Frostman conclusion is assumed.
-/

noncomputable section

open MeasureTheory Set
open Kakeya.Streamlined

namespace Kakeya.Assouad

/-- Every convex-set density is at most the indexed cardinality. -/
lemma tubeFamily_deltaMax_le_enncard
    {delta : ℝ} (hdelta : 0 < delta)
    (F : Kakeya.Streamlined.TubeFamily delta) :
    F.toBodyFamily.deltaMax ≤ F.enncard := by
  let V : ENNReal := Kakeya.deltaTubeVolume delta
  let canonical : Kakeya.DeltaTube delta :=
    { base := 0
      direction := EuclideanSpace.single (0 : Fin 3) 1
      direction_unit := by simp <;> norm_num }
  have hV_pos : 0 < V := by
    have h := Kakeya.Streamlined.tube_volume_ge_two_delta_sq delta hdelta
    have hpos : 0 < ENNReal.ofReal (2 * delta ^ 2) := by
      apply ENNReal.ofReal_pos.mpr
      positivity
    exact hpos.trans_le h
  have hV_top : V ≠ ⊤ := by
    have h := Kakeya.Streamlined.GeometricLemmas.capsule_upper_bound_instantiation
      delta hdelta
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have htube_volume : ∀ i : Fin F.card, (F.tube i).volume = V := by
    intro i
    have h := Kakeya.Streamlined.tube_volume_eq (F.tube i) canonical
    have hcanonical : canonical.volume = Kakeya.deltaTubeVolume delta := by
      rfl
    exact h.trans hcanonical
  rcases Kakeya.Streamlined.deltaMax_attained F.toBodyFamily with
    ⟨K, _hK, hmax⟩
  rw [← hmax]
  by_cases hindices : F.toBodyFamily.containedIndices K = ∅
  · simp [BodyFamily.density, BodyFamily.containedMass, hindices]
  · have hne : (F.toBodyFamily.containedIndices K).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hindices
    rcases hne with ⟨i, hi⟩
    have hsub : (F.tube i).carrier ⊆ K :=
      BodyFamily.mem_containedIndices_iff.mp hi
    have hV_le_volume : V ≤ volume K := by
      rw [← htube_volume i]
      exact measure_mono hsub
    have hvolume_pos : volume K ≠ 0 := by
      exact ne_of_gt (hV_pos.trans_le hV_le_volume)
    by_cases hvolume_top : volume K = ⊤
    · simp [BodyFamily.density, hvolume_top]
    · rw [BodyFamily.density, ENNReal.div_le_iff hvolume_pos hvolume_top]
      calc
        F.toBodyFamily.containedMass K
            = ∑ _i ∈ F.toBodyFamily.containedIndices K, V := by
                apply Finset.sum_congr rfl
                intro j _
                exact htube_volume j
        _ = ((F.toBodyFamily.containedIndices K).card : ENNReal) * V := by
              simp [Finset.sum_const]
        _ ≤ F.enncard * V := by
              gcongr
              have hcard : (F.toBodyFamily.containedIndices K).card ≤ F.card := by
                change (F.toBodyFamily.containedIndices K).card ≤
                  F.toBodyFamily.card
                have h := Finset.card_le_card
                  (Finset.subset_univ (F.toBodyFamily.containedIndices K) :
                    F.toBodyFamily.containedIndices K ⊆
                      (Finset.univ : Finset (Fin F.toBodyFamily.card)))
                simpa using h
              simpa [Kakeya.Streamlined.TubeFamily.enncard] using
                (show ((F.toBodyFamily.containedIndices K).card : ENNReal) ≤
                    (F.card : ENNReal) by exact_mod_cast hcard)
        _ ≤ F.enncard * volume K := by gcongr

/-- A common bounded support supplies a lower bound for `deltaMax`. -/
lemma tubeFamily_density_support_le_deltaMax
    {delta R : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (hsupport : ∀ i, (F.tube i).carrier ⊆ Metric.closedBall (0 : Point3) R) :
    F.toBodyFamily.mass / volume (Metric.closedBall (0 : Point3) R) ≤
      F.toBodyFamily.deltaMax := by
  have hconvex : Convex ℝ (Metric.closedBall (0 : Point3) R) :=
    convex_closedBall _ _
  have hindices : F.toBodyFamily.containedIndices
      (Metric.closedBall (0 : Point3) R) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    exact BodyFamily.mem_containedIndices_iff.mpr (hsupport i)
  have hmass : F.toBodyFamily.containedMass
      (Metric.closedBall (0 : Point3) R) = F.toBodyFamily.mass := by
    simp [BodyFamily.containedMass, BodyFamily.mass, hindices]
  have hbdd : BddAbove
      {d : ENNReal | ∃ K : Set Point3, Convex ℝ K ∧
        d = F.toBodyFamily.density K} :=
    ⟨⊤, fun _ _ => le_top⟩
  have hle : F.toBodyFamily.density (Metric.closedBall (0 : Point3) R) ≤
      F.toBodyFamily.deltaMax := by
    rw [BodyFamily.deltaMax]
    exact le_csSup hbdd ⟨Metric.closedBall (0 : Point3) R, hconvex, rfl⟩
  simpa [BodyFamily.density, hmass] using hle

/-- Turn a common-support maximal-density bound into an absolute indexed
cardinality bound. -/
lemma tubeFamily_card_le_of_support_deltaMax
    {delta R : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (hsupport : ∀ i, (F.tube i).carrier ⊆
      Metric.closedBall (0 : Point3) R)
    (D : ENNReal) (hdeltaMax : F.toBodyFamily.deltaMax ≤ D)
    (hball_pos : 0 < volume (Metric.closedBall (0 : Point3) R))
    (hball_top : volume (Metric.closedBall (0 : Point3) R) ≠ ⊤) :
    F.enncard ≤
      D * volume (Metric.closedBall (0 : Point3) R) *
        (Kakeya.deltaTubeVolume delta)⁻¹ := by
  let V := Kakeya.deltaTubeVolume delta
  have hVpos : 0 < V :=
    (tube_volume_scaling.2.1 delta hdelta hdelta_one).1
  have hVtop : V ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta hdelta hdelta_one).2
  have hmassDiv := tubeFamily_density_support_le_deltaMax F hsupport
  have hmass : F.toBodyFamily.mass ≤
      D * volume (Metric.closedBall (0 : Point3) R) :=
    (ENNReal.div_le_iff hball_pos.ne' hball_top).mp
      (hmassDiv.trans hdeltaMax)
  rw [tubeFamily_mass_eq_nominal F] at hmass
  change F.enncard * V ≤
    D * volume (Metric.closedBall (0 : Point3) R) at hmass
  calc
    F.enncard = (F.enncard * V) * V⁻¹ := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hVpos.ne' hVtop, mul_one]
    _ ≤ (D * volume (Metric.closedBall (0 : Point3) R)) * V⁻¹ := by
      gcongr
    _ = D * volume (Metric.closedBall (0 : Point3) R) * V⁻¹ := rfl

/-- If Bernoulli sampling uses `target / D`, common bounded support cancels
the ambient cardinality against the lower bound on `D`. -/
lemma tubeFamily_sampling_card_le_of_support
    {delta R : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (hsupport : ∀ i, (F.tube i).carrier ⊆
      Metric.closedBall (0 : Point3) R)
    (target D : ENNReal)
    (hdeltaMax : F.toBodyFamily.deltaMax ≤ D)
    (htarget_D : target ≤ D) (htarget_zero : target ≠ 0)
    (hD_top : D ≠ ⊤)
    (hball_pos : 0 < volume (Metric.closedBall (0 : Point3) R))
    (hball_top : volume (Metric.closedBall (0 : Point3) R) ≠ ⊤) :
    (target / D) * F.enncard ≤
      target * volume (Metric.closedBall (0 : Point3) R) *
        (Kakeya.deltaTubeVolume delta)⁻¹ := by
  let V := Kakeya.deltaTubeVolume delta
  have hVpos : 0 < V :=
    (tube_volume_scaling.2.1 delta hdelta hdelta_one).1
  have hVtop : V ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta hdelta hdelta_one).2
  have hDzero : D ≠ 0 := by
    intro hzero
    rw [hzero] at htarget_D
    exact htarget_zero (bot_unique htarget_D)
  have hmassDiv := tubeFamily_density_support_le_deltaMax F hsupport
  have hmass : F.toBodyFamily.mass ≤
      D * volume (Metric.closedBall (0 : Point3) R) :=
    (ENNReal.div_le_iff hball_pos.ne' hball_top).mp
      (hmassDiv.trans hdeltaMax)
  rw [tubeFamily_mass_eq_nominal F] at hmass
  change F.enncard * V ≤
    D * volume (Metric.closedBall (0 : Point3) R) at hmass
  calc
    (target / D) * F.enncard =
        ((target / D) * (F.enncard * V)) * V⁻¹ := by
          rw [mul_assoc, mul_assoc, ENNReal.mul_inv_cancel hVpos.ne' hVtop,
            mul_one]
    _ ≤ ((target / D) *
          (D * volume (Metric.closedBall (0 : Point3) R))) * V⁻¹ := by
          gcongr
    _ = target * volume (Metric.closedBall (0 : Point3) R) * V⁻¹ := by
          rw [ENNReal.div_eq_inv_mul]
          rw [show D⁻¹ * target * (D *
                volume (Metric.closedBall (0 : Point3) R)) =
              target * (D⁻¹ * D) *
                volume (Metric.closedBall (0 : Point3) R) by ring]
          rw [ENNReal.inv_mul_cancel hDzero hD_top, mul_one]

/-- A convenient numerical volume bound for the support ball used in Node 7. -/
lemma volume_closedBall_six_le :
    volume (Metric.closedBall (0 : Point3) 6) ≤ (1200 : ENNReal) := by
  rw [EuclideanSpace.volume_closedBall_fin_three]
  have hsix : ENNReal.ofReal (6 : ℝ) ^ 3 =
      ENNReal.ofReal ((6 : ℝ) ^ 3) := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 6)]
  rw [hsix, ← ENNReal.ofReal_mul (by positivity)]
  have hreal : ((6 : ℝ) ^ 3) * (Real.pi * 4 / 3) ≤ 1200 := by
    have hpi := Real.pi_lt_four
    nlinarith
  have henn := ENNReal.ofReal_mono hreal
  simpa using henn

/-- A tube with base norm at most four and radius at most one lies in `B(0,6)`. -/
lemma tube_carrier_subset_closedBall_six
    {delta : ℝ} (hdelta : 0 ≤ delta) (hdelta_one : delta ≤ 1)
    (T : Kakeya.DeltaTube delta) (hbase : ‖T.base‖ ≤ 4) :
    T.carrier ⊆ Metric.closedBall (0 : Point3) 6 := by
  intro x hx
  have hsegment : IsCompact (Kakeya.unitSegment T.base T.direction) := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  change x ∈ Metric.cthickening delta
    (Kakeya.unitSegment T.base T.direction) at hx
  rw [hsegment.cthickening_eq_biUnion_closedBall hdelta] at hx
  rcases Set.mem_iUnion₂.mp hx with ⟨y, hy, hxy⟩
  rcases hy with ⟨t, ht, rfl⟩
  have hdist : dist x (T.base + t • T.direction) ≤ delta := by
    simpa [Metric.mem_closedBall] using hxy
  have haxis : ‖T.base + t • T.direction‖ ≤ 5 := by
    calc
      ‖T.base + t • T.direction‖ ≤ ‖T.base‖ + ‖t • T.direction‖ :=
        norm_add_le _ _
      _ = ‖T.base‖ + |t| := by simp [norm_smul, T.direction_unit]
      _ ≤ 4 + 1 := by
        have ht_abs : |t| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [ht.1, ht.2]
        gcongr
      _ = 5 := by norm_num
  have hxnorm : ‖x‖ ≤ 6 := by
    calc
      ‖x‖ = dist x 0 := by simp [dist_zero_right]
      _ ≤ dist x (T.base + t • T.direction) +
          dist (T.base + t • T.direction) 0 := dist_triangle _ _ _
      _ ≤ delta + 5 := by simpa [dist_zero_right] using add_le_add hdist haxis
      _ ≤ 6 := by linarith
  simpa [Metric.mem_closedBall, dist_zero_right] using hxnorm

end Kakeya.Assouad

end
