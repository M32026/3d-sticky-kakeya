import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedFSVSetupInputs

/-!
# Helper lemmas for delta positivity

Extract `0 ≤ delta` and `0 < delta` from a nonempty fine rectangle family.

`0 ≤ delta` follows from a carrier point: the vertical neighborhood condition
gives `0 ≤ |p.2 - f p.1| ≤ delta`.

`0 < delta` follows by contradiction from the two-ends certificate's metric
nonconcentration: if `delta ≤ 0`, choose a tiny `scale > 0` so that
`4 * (2*scale)^epsilon * metricFiber.card < 1`, while the intersection
`metricFiber ∩ ball(g, scale*t)` contains at least `g`, giving `1 ≤ ncard`.
-/

namespace Kakeya.Cinematic

lemma fine_delta_nonneg
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    {data : DyadicFineAssignmentData family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    {center : C2Function}
    {hE : MeasurableSet E}
    {C_R C_count C_shading C_volume : ℝ}
    (fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume) :
    0 ≤ delta := by
  have hfine_nonempty : fineSetup.fine.Nonempty := fineSetup.fine_nonempty
  let i : Fin fineSetup.fine.card :=
    Classical.choice (Fin.pos_iff_nonempty.mp hfine_nonempty)
  let p := fineSetup.source i
  have hpoint_in : fineSetup.pointData.point p ∈
      (fineSetup.pointData.rectangle p).carrier :=
    fineSetup.pointData.point_mem_rectangle p
  have h_simp :
    (fineSetup.pointData.point p).1 ∈
        (fineSetup.pointData.rectangle p).interval.carrier ∧
    |(fineSetup.pointData.point p).2 -
        (fineSetup.pointData.rectangle p).function.value
          (fineSetup.pointData.point p).1| ≤ delta := by
    simpa [CurvilinearRectangle.carrier, verticalNeighborhoodOn] using hpoint_in
  have h_abs_le :
    |(fineSetup.pointData.point p).2 -
        (fineSetup.pointData.rectangle p).function.value
          (fineSetup.pointData.point p).1| ≤ delta :=
    h_simp.2
  have h_abs_nonneg : 0 ≤ |(fineSetup.pointData.point p).2 -
      (fineSetup.pointData.rectangle p).function.value
        (fineSetup.pointData.point p).1| :=
    abs_nonneg _
  exact le_trans h_abs_nonneg h_abs_le

/-- Strict positivity of `delta` from the two-ends certificate nonconcentration. -/
lemma fine_delta_pos
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    {data : DyadicFineAssignmentData family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    {center : C2Function}
    {hE : MeasurableSet E}
    {C_R C_count C_shading C_volume : ℝ}
    (fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume) :
    0 < delta := by
  by_contra h
  have hdelta_nonpos : delta ≤ 0 := by linarith

  have hfine_nonempty : fineSetup.fine.Nonempty := fineSetup.fine_nonempty
  let i : Fin fineSetup.fine.card :=
    Classical.choice (Fin.pos_iff_nonempty.mp hfine_nonempty)
  let q := fineSetup.source i
  have hq_in_E : (q : ℝ × ℝ) ∈ E := q.property.1
  let p : E := ⟨q, hq_in_E⟩

  let cert := data.certificate p
  let t : ℝ := data.exactT p
  let metricFiber := data.metricFiber p

  have ht_pos : 0 < t := by
    have h1 : 0 < tRep := data.tRep_pos
    have h2 : tRep ≤ 8 * t := data.rep_le_eight_exactT p
    linarith

  have hdiam_pos : 0 < diameter := ht_pos.trans_le cert.t_le_diameter

  have hsource_card_pos : 0 < (data.source p).card := by
    have hmu_pos' : 0 < (data.mu : ℕ) := data.mu_pos
    exact_mod_cast lt_of_lt_of_le hmu_pos' (data.mu_le_source p)
  have hratio_pos : 0 < t / diameter := div_pos ht_pos hdiam_pos
  have hrpow_pos : 0 < Real.rpow (t / diameter) epsilon :=
    Real.rpow_pos_of_pos hratio_pos _
  have hleft_pos : 0 < Real.rpow (t / diameter) epsilon * ((data.source p).card : ℝ) :=
    mul_pos hrpow_pos (by exact_mod_cast hsource_card_pos)
  have hmetric_card_real_pos : (0 : ℝ) < (metricFiber.card : ℝ) :=
    hleft_pos.trans_le cert.metric_retention
  have hmetric_card_pos : 0 < metricFiber.card :=
    Nat.cast_pos.mp hmetric_card_real_pos

  let M : ℝ := metricFiber.card
  have hM_pos : 0 < M := hmetric_card_real_pos

  have hmetric_nonempty : metricFiber.carrier.Nonempty :=
    (Set.ncard_pos metricFiber.finite).1 hmetric_card_pos
  rcases hmetric_nonempty with ⟨g, hg_in⟩

  let y : ℝ := (1 / (4 * M)) ^ (1 / epsilon)
  have hy_pos : 0 < y := Real.rpow_pos_of_pos (by positivity) _
  have hbase_pos : 0 < 1 / (4 * M) := by positivity
  have h_rpow_comp : ∀ (x : ℝ), 0 ≤ x → ∀ (y z : ℝ),
      Real.rpow (Real.rpow x y) z = Real.rpow x (y * z) := by
    intro x hx y z
    exact (Real.rpow_mul hx y z).symm
  have h_y_rpow : Real.rpow y epsilon = 1 / (4 * M) := by
    have h1 : Real.rpow y epsilon = Real.rpow (Real.rpow (1 / (4 * M)) (1 / epsilon)) epsilon := rfl
    rw [h1]
    have h2 : Real.rpow (Real.rpow (1 / (4 * M)) (1 / epsilon)) epsilon =
        Real.rpow (1 / (4 * M)) ((1 / epsilon) * epsilon) :=
      h_rpow_comp (1 / (4 * M)) hbase_pos.le (1 / epsilon) epsilon
    rw [h2]
    have h3 : (1 / epsilon) * epsilon = 1 := by
      field_simp [data.epsilon_pos.ne']
    rw [h3]
    simp

  let scale : ℝ := min (y / 4) (1 / 2)
  have hscale_pos : 0 < scale := by positivity
  have hscale_lt_one : scale < 1 := by
    have h : scale ≤ 1 / 2 := min_le_right _ _
    linarith
  have h2scale_lt_y : 2 * scale < y := by
    have h1 : scale ≤ y / 4 := min_le_left _ _
    linarith
  have hdelta_t_lt_scale : delta / t < scale := by
    have h2 : delta / t ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg hdelta_nonpos ht_pos.le
    linarith

  have hrpow_lt : Real.rpow (2 * scale) epsilon < 1 / (4 * M) := by
    have h1 : 0 ≤ 2 * scale := by positivity
    have h3 : Real.rpow (2 * scale) epsilon < Real.rpow y epsilon :=
      Real.rpow_lt_rpow h1 h2scale_lt_y data.epsilon_pos
    have h4 : Real.rpow y epsilon = 1 / (4 * M) := h_y_rpow
    rw [h4] at h3
    exact h3

  have hg_ball : g ∈ c2Ball g (scale * t) := by
    rw [mem_c2Ball, c2Distance_eq_dist, dist_self]
    exact by positivity
  let S : Set C2Function := metricFiber.carrier ∩ c2Ball g (scale * t)
  have hS_finite : S.Finite := metricFiber.finite.inter_of_left _
  have hS_nonempty : S.Nonempty := ⟨g, hg_in, hg_ball⟩
  have hS_ncard_pos : 0 < S.ncard :=
    (Set.ncard_pos (hs := hS_finite)).mpr hS_nonempty

  have h_nonconc : (S.ncard : ℝ) ≤ 4 * Real.rpow (2 * scale) epsilon * M :=
    cert.metric_nonconcentration g scale hdelta_t_lt_scale hscale_lt_one

  have h_final : 4 * Real.rpow (2 * scale) epsilon * M < 1 := by
    have h5 : Real.rpow (2 * scale) epsilon < 1 / (4 * M) := hrpow_lt
    have h6 : 4 * Real.rpow (2 * scale) epsilon * M < 4 * (1 / (4 * M)) * M := by
      gcongr
    have h7 : 4 * (1 / (4 * M)) * M = 1 := by
      field_simp [hM_pos.ne']
    rw [h7] at h6
    exact h6

  have h_lt_one : (S.ncard : ℝ) < 1 := h_nonconc.trans_lt h_final
  have h_eq_zero : S.ncard = 0 := by
    exact Nat.cast_lt_one.mp h_lt_one
  exact hS_ncard_pos.ne' h_eq_zero

end Kakeya.Cinematic
