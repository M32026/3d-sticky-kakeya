import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling

/-!
# Per-tube density pruning for the plain TubeFamily / Shading API

Given an aggregate `η_in`-dense shading, prune tubes carrying less than
`δ^η_out * |T|` shaded mass.  The retained subfamily `F1` satisfies:

* cardinality retention: `δ^η_out * #F ≤ #F1`
* per-tube fullness: every `T ∈ F1` has `δ^η_out * |T| ≤ |Y1(T)|`

provided `δ^η_out ≤ (1/2) * δ^η_in`.
-/

noncomputable section

open MeasureTheory Set Finset

namespace Kakeya.Assouad

/--
Per-tube density pruning: retain tubes with at least `δ^eta_out * |T|` shaded
mass.  The output subfamily retains a `δ^eta_out` fraction of the cardinality
and every retained tube is individually `δ^eta_out`-dense.
-/
lemma per_tube_pruning
    {δ : ℝ} (hdelta : 0 < δ) (hdelta_one : δ ≤ 1)
    {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {eta_in eta_out : ℝ} (_h_in_pos : 0 < eta_in) (_h_out_pos : 0 < eta_out)
    (_h_in_lt_out : eta_in < eta_out)
    (hY_dense : Y.IsLambdaDense (Kakeya.realRpowENN δ eta_in))
    (h_small : Kakeya.realRpowENN δ eta_out ≤ (1 / 2 : ENNReal) * Kakeya.realRpowENN δ eta_in)
    (hF_nonempty : F.Nonempty) (hF_ball : F.IsInUnitBall) (hF_ed : F.IsEssentiallyDistinct) :
    ∃ (F1 : Kakeya.TubeFamily δ) (Y1 : Kakeya.Shading F1),
      F1 ⊆ F ∧
      F1.Nonempty ∧
      F1.IsInUnitBall ∧
      F1.IsEssentiallyDistinct ∧
      Y1.union ⊆ Y.union ∧
      (∀ (T : Kakeya.DeltaTube δ) (_hT : T ∈ F1), Y1.carrier T ⊆ Y.carrier T) ∧
      (Kakeya.realRpowENN δ eta_out * F.enncard ≤ F1.enncard) ∧
      (∀ T ∈ F1, Kakeya.realRpowENN δ eta_out * T.volume ≤ MeasureTheory.volume (Y1.carrier T)) := by
  classical
  rcases tube_volume_scaling with ⟨h_equal_volume, h_volume_finite, _⟩
  let V : ENNReal := Kakeya.deltaTubeVolume δ
  have hV_pos : 0 < V := (h_volume_finite δ hdelta hdelta_one).1
  have hV_ne_top : V ≠ ⊤ := (h_volume_finite δ hdelta hdelta_one).2
  let threshold : ENNReal := Kakeya.realRpowENN δ eta_out * V
  let F1 : Kakeya.TubeFamily δ :=
    F.filter fun T => threshold ≤ MeasureTheory.volume (Y.carrier T)
  have hF1_sub : F1 ⊆ F := Finset.filter_subset _ _
  let Y1 : Kakeya.Shading F1 :=
    { carrier := Y.carrier
      measurable_carrier := fun T hT => Y.measurable_carrier (hF1_sub hT)
      subset_tube := fun T hT => Y.subset_tube (hF1_sub hT) }
  have h_carrier_eq : ∀ T, Y1.carrier T = Y.carrier T := by
    intro T; rfl
  -- Per-tube density for good tubes
  have h_per_tube : ∀ T ∈ F1, threshold ≤ MeasureTheory.volume (Y1.carrier T) := by
    intro T hT
    have h5 : T ∈ F1 := hT
    have h6 : threshold ≤ MeasureTheory.volume (Y.carrier T) := by
      have h7 : T ∈ F ∧ threshold ≤ MeasureTheory.volume (Y.carrier T) := by
        simpa [F1, Finset.mem_filter] using h5
      exact h7.2
    simpa [h_carrier_eq] using h6
  -- Convert per-tube to the desired form using T.volume = V
  have h_per_tube' : ∀ T ∈ F1, Kakeya.realRpowENN δ eta_out * T.volume ≤ MeasureTheory.volume (Y1.carrier T) := by
    intro T hT
    have hTvol : T.volume = V := h_equal_volume δ T
    rw [hTvol]
    exact h_per_tube T hT
  -- Bad tubes and bad mass
  let bad : Kakeya.TubeFamily δ := F \ F1
  let badMass : ENNReal := ∑ T ∈ bad, MeasureTheory.volume (Y.carrier T)
  have h_bad_lt : ∀ T ∈ bad, MeasureTheory.volume (Y.carrier T) < threshold := by
    intro T hT
    have h2 : T ∈ F := (Finset.mem_sdiff).mp hT |>.1
    have h3 : T ∉ F1 := (Finset.mem_sdiff).mp hT |>.2
    have h4 : ¬(threshold ≤ MeasureTheory.volume (Y.carrier T)) := by
      simpa [F1, Finset.mem_filter, h2] using h3
    exact lt_of_not_ge h4
  have h_bad_le : badMass ≤ threshold * bad.enncard := by
    calc
      badMass
        ≤ ∑ T ∈ bad, threshold := by
          apply Finset.sum_le_sum
          intro T hT
          exact (h_bad_lt T hT).le
      _ = threshold * bad.enncard := by
        rw [Finset.sum_const]
        <;> simp [Kakeya.TubeFamily.enncard, mul_comm]
        <;> ring
  have h_bad_card : bad.enncard ≤ F.enncard := by
    have h : bad ⊆ F := by
      simp [bad]
      <;> tauto
    simpa [Kakeya.TubeFamily.enncard] using Finset.card_le_card h
  have h_bad_le' : badMass ≤ threshold * F.enncard := by
    calc
      badMass ≤ threshold * bad.enncard := h_bad_le
      _ ≤ threshold * F.enncard := by gcongr
  -- Mass split: Y.mass = Y1.mass + badMass
  have h_disj : Disjoint F1 bad := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx2).2 hx1
  have h_univ : F1 ∪ bad = F := by
    ext x
    simp [F1, bad, Finset.mem_filter]
    <;> tauto
  have h_mass_split : Y1.mass + badMass = Y.mass := by
    have h1 : Y1.mass = ∑ T ∈ F1, MeasureTheory.volume (Y.carrier T) := by
      rfl
    rw [h1]
    have h2 : ∑ T ∈ F1, MeasureTheory.volume (Y.carrier T) + badMass =
        ∑ T ∈ F1 ∪ bad, MeasureTheory.volume (Y.carrier T) := by
      rw [Finset.sum_union h_disj] <;> rfl
    rw [h2, h_univ] <;> rfl
  -- F.mass = F.enncard * V
  have h_F_mass : F.mass = F.enncard * V := by
    have h1 : F.mass = ∑ T ∈ F, T.volume := by rfl
    rw [h1]
    have h2 : ∀ T ∈ F, T.volume = V := by
      intro T _
      exact h_equal_volume δ T
    have h3 : ∑ T ∈ F, T.volume = ∑ T ∈ F, V := by
      apply Finset.sum_congr rfl
      intro T _
      exact h2 T ‹_›
    rw [h3]
    simp [Kakeya.TubeFamily.enncard, Finset.sum_const]
    <;> ring
  -- Y1.mass ≤ F1.enncard * V
  have h_Y1_mass_le : Y1.mass ≤ F1.enncard * V := by
    have h1 : Y1.mass = ∑ T ∈ F1, MeasureTheory.volume (Y1.carrier T) := by rfl
    rw [h1]
    have h2 : ∀ T ∈ F1, MeasureTheory.volume (Y1.carrier T) ≤ T.volume := by
      intro T hT
      have h3 : Y1.carrier T ⊆ T.carrier := Y1.subset_tube hT
      exact measure_mono h3
    have h3 : ∑ T ∈ F1, MeasureTheory.volume (Y1.carrier T) ≤ ∑ T ∈ F1, T.volume := by
      apply Finset.sum_le_sum
      intro T _
      exact h2 T ‹_›
    have h4 : ∑ T ∈ F1, T.volume = F1.enncard * V := by
      have h5 : ∀ T ∈ F1, T.volume = V := by
        intro T _
        exact h_equal_volume δ T
      have h6 : ∑ T ∈ F1, T.volume = ∑ T ∈ F1, V := by
        apply Finset.sum_congr rfl
        intro T _
        exact h5 T ‹_›
      rw [h6]
      simp [Kakeya.TubeFamily.enncard, Finset.sum_const] <;> ring
    rw [h4] at h3
    exact h3
  -- Finite terms for cancellation
  have h_rpow_in_ne_top : Kakeya.realRpowENN δ eta_in ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_rpow_out_ne_top : Kakeya.realRpowENN δ eta_out ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_F_enncard_ne_top : F.enncard ≠ ⊤ := by
    simp [Kakeya.TubeFamily.enncard] <;> exact ENNReal.coe_ne_top
  have h_F1_enncard_ne_top : F1.enncard ≠ ⊤ := by
    simp [Kakeya.TubeFamily.enncard] <;> exact ENNReal.coe_ne_top
  let b : ENNReal := Kakeya.realRpowENN δ eta_out * F.enncard
  have h_b_ne_top : b ≠ ⊤ := by
    apply ENNReal.mul_ne_top h_rpow_out_ne_top h_F_enncard_ne_top
  -- Main inequality
  have h_dense' : Kakeya.realRpowENN δ eta_in * F.mass ≤ Y.mass := hY_dense
  rw [h_F_mass] at h_dense'
  have h_dense'' : Kakeya.realRpowENN δ eta_in * F.enncard * V ≤ Y.mass := by
    have h_assoc : Kakeya.realRpowENN δ eta_in * F.enncard * V = Kakeya.realRpowENN δ eta_in * (F.enncard * V) := by
      simp [mul_assoc]
    rw [h_assoc]
    exact h_dense'
  have h_main1 : Kakeya.realRpowENN δ eta_in * F.enncard * V ≤ Y1.mass + badMass := by
    have h : Y1.mass + badMass = Y.mass := h_mass_split
    rw [h]
    exact h_dense''
  have h_main2 : Kakeya.realRpowENN δ eta_in * F.enncard * V ≤ F1.enncard * V + threshold * F.enncard := by
    calc
      Kakeya.realRpowENN δ eta_in * F.enncard * V
        ≤ Y1.mass + badMass := h_main1
      _ ≤ F1.enncard * V + badMass := by gcongr
      _ ≤ F1.enncard * V + threshold * F.enncard := by gcongr
  -- threshold * F.enncard = δ^eta_out * F.enncard * V = b * V
  have h_threshold_eq : threshold * F.enncard = b * V := by
    simp [threshold, b, mul_assoc, mul_comm, mul_left_comm] <;> rfl
  rw [h_threshold_eq] at h_main2
  -- Cancel V from both sides
  have h_main3 : Kakeya.realRpowENN δ eta_in * F.enncard ≤ F1.enncard + b := by
    have h_distrib : F1.enncard * V + b * V = (F1.enncard + b) * V := by
      rw [add_mul]
    rw [h_distrib] at h_main2
    have hV_pos' : V ≠ 0 := ne_of_gt hV_pos
    have h_main2' : V * (Kakeya.realRpowENN δ eta_in * F.enncard) ≤ V * (F1.enncard + b) := by
      have h1 : V * (Kakeya.realRpowENN δ eta_in * F.enncard) = Kakeya.realRpowENN δ eta_in * F.enncard * V := by
        simp [mul_comm, mul_assoc, mul_left_comm]
      have h2 : V * (F1.enncard + b) = (F1.enncard + b) * V := by
        rw [mul_comm]
      rw [h1, h2]
      exact h_main2
    exact (ENNReal.mul_le_mul_iff_right hV_pos' hV_ne_top).mp h_main2'
  -- From h_small: 2 * δ^eta_out ≤ δ^eta_in
  have h_double : 2 * Kakeya.realRpowENN δ eta_out ≤ Kakeya.realRpowENN δ eta_in := by
    have h : (2 : ENNReal) * Kakeya.realRpowENN δ eta_out ≤ (2 : ENNReal) * ((1 / 2 : ENNReal) * Kakeya.realRpowENN δ eta_in) := by
      gcongr
      <;> exact h_small
    have h2 : (2 : ENNReal) * ((1 / 2 : ENNReal) * Kakeya.realRpowENN δ eta_in) = Kakeya.realRpowENN δ eta_in := by
      have h3 : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
        have h4 : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by simp
        rw [h4]
        exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      calc
        (2 : ENNReal) * ((1 / 2 : ENNReal) * Kakeya.realRpowENN δ eta_in)
          = ((2 : ENNReal) * (1 / 2 : ENNReal)) * Kakeya.realRpowENN δ eta_in := by
            simp [mul_assoc] <;> rfl
        _ = (1 : ENNReal) * Kakeya.realRpowENN δ eta_in := by rw [h3]
        _ = Kakeya.realRpowENN δ eta_in := by simp
    rw [h2] at h
    exact h
  have h_main4 : 2 * b ≤ F1.enncard + b := by
    have h5 : 2 * b = 2 * Kakeya.realRpowENN δ eta_out * F.enncard := by
      simp [b, two_mul, mul_assoc, mul_comm, mul_left_comm] <;> rfl
    rw [h5]
    have h6 : 2 * Kakeya.realRpowENN δ eta_out * F.enncard ≤ Kakeya.realRpowENN δ eta_in * F.enncard := by
      gcongr
      <;> exact h_double
    exact h6.trans h_main3
  have h_card_retention : b ≤ F1.enncard := by
    have h7 : 2 * b = b + b := by
      simp [two_mul] <;> abel
    rw [h7] at h_main4
    exact (ENNReal.add_le_add_iff_right h_b_ne_top).mp h_main4
  -- F1.Nonempty
  have h_F_enncard_pos : 0 < F.enncard := by
    have h : 0 < F.card := Finset.card_pos.mpr hF_nonempty
    simpa [Kakeya.TubeFamily.enncard] using h
  have h_rpow_out_pos : 0 < Kakeya.realRpowENN δ eta_out := by
    have h : 0 < Real.rpow δ eta_out := Real.rpow_pos_of_pos hdelta eta_out
    exact ENNReal.ofReal_pos.mpr h
  have h_b_pos : 0 < b := by
    have h1 : Kakeya.realRpowENN δ eta_out ≠ 0 := ne_of_gt h_rpow_out_pos
    have h2 : F.enncard ≠ 0 := ne_of_gt h_F_enncard_pos
    exact ENNReal.mul_pos h1 h2
  have h_F1_enncard_pos : 0 < F1.enncard := h_b_pos.trans_le h_card_retention
  have hF1_nonempty : F1.Nonempty := by
    have h : 0 < F1.card := by
      simpa [Kakeya.TubeFamily.enncard] using h_F1_enncard_pos
    exact Finset.card_pos.mp h
  -- Inherited properties
  have hF1_ball : F1.IsInUnitBall := by
    intro T hT
    exact hF_ball (hF1_sub hT)
  have hF1_ed : F1.IsEssentiallyDistinct := by
    intro T hT U hU hne
    exact hF_ed (hF1_sub hT) (hF1_sub hU) hne
  -- Union containment
  have h_union_sub : Y1.union ⊆ Y.union := by
    intro x hx
    rcases hx with ⟨T, hT, hxT⟩
    refine ⟨T, hF1_sub hT, ?_⟩
    simpa [h_carrier_eq] using hxT
  -- Carrier containment
  have h_carrier_sub : ∀ (T : Kakeya.DeltaTube δ) (hT : T ∈ F1), Y1.carrier T ⊆ Y.carrier T := by
    intro T _
    simp [h_carrier_eq]
  exact ⟨F1, Y1, hF1_sub, hF1_nonempty, hF1_ball, hF1_ed, h_union_sub, h_carrier_sub, h_card_retention, h_per_tube'⟩

end Kakeya.Assouad
