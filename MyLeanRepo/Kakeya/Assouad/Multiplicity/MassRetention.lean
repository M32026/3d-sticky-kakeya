import MyLeanRepo.Kakeya.Assouad.ExtremalInfrastructure
import MyLeanRepo.Kakeya.Assouad.Targets.TubeVolumeScaling

/-!
# L2: Mass retention under pruning

If Y is η-dense and we discard tubes with `|Y(T)| < (1/2) * δ^η * |T|`,
the remaining shading retains at least `(1/2) * δ^η * F.mass` mass.
-/

noncomputable section

open MeasureTheory Set Finset

namespace Kakeya.Assouad

/--
Full version of `mass_retention_under_pruning`: returns the pruned shading `Y'`
together with `IsSubshading`, the mass retention bound, and the per-tube mass
guarantee `HasPerTubeMass Y' threshold`.
-/
lemma mass_retention_under_pruning_full
    {δ : ℝ} (hdelta : 0 < δ) (hdelta_one : δ ≤ 1)
    {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : Kakeya.Streamlined.TubeShading F}
    {eta : ℝ} (heta : 0 < eta)
    (hY_dense : Y.IsLambdaDense (Kakeya.realRpowENN δ eta)) :
    ∃ (Y' : Kakeya.Streamlined.TubeShading F),
      IsSubshading Y' Y ∧
      (1 / 2 : ENNReal) * Y.mass ≤ Y'.mass ∧
      Y'.mass ≥ (1 / 2 : ENNReal) * Kakeya.realRpowENN δ eta * F.toBodyFamily.mass ∧
      HasPerTubeMass Y'
        ((1 / 2 : ENNReal) * Kakeya.realRpowENN δ eta * Kakeya.deltaTubeVolume δ) ∧
      IsWholeTubeSubshading Y' Y := by
  classical
  rcases tube_volume_scaling with ⟨h_equal_volume, h_volume_finite, _⟩
  let threshold : ENNReal :=
    (1 / 2 : ENNReal) * Kakeya.realRpowENN δ eta * Kakeya.deltaTubeVolume δ
  let good : Finset (Fin F.toBodyFamily.card) :=
    Finset.univ.filter (fun i => threshold ≤ MeasureTheory.volume (Y.carrier i))
  let carrier' (i : Fin F.toBodyFamily.card) : Set Point3 :=
    if i ∈ good then Y.carrier i else (∅ : Set Point3)
  have h_meas : ∀ i, MeasurableSet (carrier' i) := by
    intro i
    by_cases h : i ∈ good
    · have h4 : carrier' i = Y.carrier i := by
        simp [carrier', h]
      rw [h4]
      exact Y.measurable_carrier i
    · have h4 : carrier' i = (∅ : Set Point3) := by
        simp [carrier', h]
      rw [h4]
      exact MeasurableSet.empty
  have h_subset : ∀ i, carrier' i ⊆ (F.toBodyFamily.body i).carrier := by
    intro i
    by_cases h : i ∈ good
    · have h4 : carrier' i = Y.carrier i := by simp [carrier', h]
      rw [h4]
      exact Y.subset_body i
    · have h4 : carrier' i = (∅ : Set Point3) := by simp [carrier', h]
      rw [h4]
      exact Set.empty_subset _
  let Y' : Kakeya.Streamlined.TubeShading F :=
    { carrier := carrier'
      measurable_carrier := h_meas
      subset_body := h_subset }
  have h_sub : ∀ i, Y'.carrier i ⊆ Y.carrier i := by
    intro i
    by_cases h : i ∈ good
    · have h4 : Y'.carrier i = Y.carrier i := by simp [Y', carrier', h]
      rw [h4] <;> exact Set.Subset.refl _
    · have h4 : Y'.carrier i = (∅ : Set Point3) := by simp [Y', carrier', h]
      rw [h4] <;> exact Set.empty_subset _
  have h_per_tube : HasPerTubeMass Y' threshold := by
    intro i
    by_cases h : i ∈ good
    · have h4 : Y'.carrier i = Y.carrier i := by simp [Y', carrier', h]
      have h5 : threshold ≤ MeasureTheory.volume (Y.carrier i) := by
        have h6 : i ∈ good := h
        simpa [good, Finset.mem_filter] using h6
      exact Or.inr (by rw [h4] <;> exact h5)
    · have h4 : Y'.carrier i = (∅ : Set Point3) := by simp [Y', carrier', h]
      exact Or.inl h4
  -- For i ∉ good, volume (Y'.carrier i) = 0
  have h_bad_zero : ∀ i ∉ good, MeasureTheory.volume (Y'.carrier i) = 0 := by
    intro i hi
    have h4 : Y'.carrier i = (∅ : Set Point3) := by simp [Y', carrier', hi]
    rw [h4]
    simp
  -- Y'.mass = sum over good
  have h_mass_Y' : Y'.mass = ∑ i ∈ good, MeasureTheory.volume (Y.carrier i) := by
    have h5 : Y'.mass = ∑ i : Fin F.toBodyFamily.card, MeasureTheory.volume (Y'.carrier i) := by rfl
    rw [h5]
    have h6 : ∑ i : Fin F.toBodyFamily.card, MeasureTheory.volume (Y'.carrier i) =
        ∑ i ∈ good, MeasureTheory.volume (Y'.carrier i) := by
      rw [Finset.sum_subset (show good ⊆ Finset.univ from by simp)]
      intro i _ hi
      exact h_bad_zero i hi
    rw [h6]
    apply Finset.sum_congr rfl
    intro i hi
    have h7 : Y'.carrier i = Y.carrier i := by simp [Y', carrier', hi]
    rw [h7]
  -- Mass of discarded tubes
  let badMass : ENNReal := ∑ i ∈ Finset.univ \ good, MeasureTheory.volume (Y.carrier i)
  have h_bad_le : badMass ≤ threshold * F.toBodyFamily.enncard := by
    have h1 : ∀ i ∈ Finset.univ \ good, MeasureTheory.volume (Y.carrier i) < threshold := by
      intro i hi
      have h2 : i ∉ good := (Finset.mem_sdiff).mp hi |>.2
      have h3 : ¬(threshold ≤ MeasureTheory.volume (Y.carrier i)) := by
        simpa [good] using h2
      exact lt_of_not_ge h3
    have h_card : (Finset.univ \ good).card ≤ F.toBodyFamily.card := by
      have h4 : (Finset.univ \ good) ⊆ (Finset.univ : Finset (Fin F.toBodyFamily.card)) := by simp
      have h5 : (Finset.univ \ good).card ≤ (Finset.univ : Finset (Fin F.toBodyFamily.card)).card :=
        Finset.card_le_card h4
      simpa using h5
    calc
      badMass
        ≤ ∑ i ∈ Finset.univ \ good, threshold := by
          apply Finset.sum_le_sum
          intro i hi
          exact (h1 i hi).le
      _ = threshold * (Finset.univ \ good).card := by
          rw [Finset.sum_const, mul_comm] <;> ring
      _ ≤ threshold * F.toBodyFamily.enncard := by
          gcongr
          <;> simpa [Kakeya.Streamlined.BodyFamily.enncard] using h_card
  -- Y'.mass + badMass = Y.mass
  have h_mass_split : Y'.mass + badMass = Y.mass := by
    rw [h_mass_Y']
    have h_disj : Disjoint good (Finset.univ \ good) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx2).2 hx1
    have h_univ : good ∪ (Finset.univ \ good) = (Finset.univ : Finset (Fin F.toBodyFamily.card)) := by
      ext x; simp
    have h2 : ∑ i ∈ good, MeasureTheory.volume (Y.carrier i) + badMass =
        ∑ i ∈ good ∪ (Finset.univ \ good), MeasureTheory.volume (Y.carrier i) := by
      rw [Finset.sum_union h_disj]
      <;> rfl
    rw [h2, h_univ]
    <;> rfl
  -- F.toBodyFamily.mass = F.toBodyFamily.enncard * deltaTubeVolume δ
  have h_mass_eq : F.toBodyFamily.mass = F.toBodyFamily.enncard * Kakeya.deltaTubeVolume δ := by
    have h1 : F.toBodyFamily.mass = ∑ i : Fin F.toBodyFamily.card, (F.toBodyFamily.body i).volume := by rfl
    rw [h1]
    have h2 : ∀ i : Fin F.toBodyFamily.card, (F.toBodyFamily.body i).volume = Kakeya.deltaTubeVolume δ := by
      intro i
      exact h_equal_volume δ (F.tube i)
    have h3 : ∑ i : Fin F.toBodyFamily.card, (F.toBodyFamily.body i).volume =
        ∑ i : Fin F.toBodyFamily.card, Kakeya.deltaTubeVolume δ := by
      apply Finset.sum_congr rfl
      intro i _
      exact h2 i
    rw [h3]
    simp [Kakeya.Streamlined.BodyFamily.enncard]
    <;> ring
  set b : ENNReal := (1 / 2 : ENNReal) * Kakeya.realRpowENN δ eta * F.toBodyFamily.mass with hb_def
  have hV_finite : Kakeya.deltaTubeVolume δ ≠ ⊤ := (h_volume_finite δ hdelta hdelta_one).2
  have h_rpow_finite : Kakeya.realRpowENN δ eta ≠ ⊤ := by
    exact ENNReal.ofReal_ne_top
  have h_b_ne_top : b ≠ ⊤ := by
    rw [hb_def, h_mass_eq]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · simp
      · exact h_rpow_finite
    · apply ENNReal.mul_ne_top
      · simp [Kakeya.Streamlined.BodyFamily.enncard]
      · exact hV_finite
  have h_threshold_eq : threshold * F.toBodyFamily.enncard = b := by
    have h9 : threshold * F.toBodyFamily.enncard =
        (1 / 2 : ENNReal) * Kakeya.realRpowENN δ eta * (F.toBodyFamily.enncard * Kakeya.deltaTubeVolume δ) := by
      simp [threshold, mul_assoc, mul_comm, mul_left_comm]
      <;> rfl
    rw [h9, ← h_mass_eq]
    <;> simp [hb_def, mul_assoc]
    <;> rfl
  have h_main : 2 * b ≤ Y'.mass + b := by
    have h_dense2 : 2 * b ≤ Y.mass := by
      have h_eq : 2 * b = Kakeya.realRpowENN δ eta * F.toBodyFamily.mass := by
        rw [hb_def]
        have h11 : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
          have h12 : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by simp
          rw [h12]
          exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        calc
          (2 : ENNReal) * ((1 / 2 : ENNReal) * Kakeya.realRpowENN δ eta * F.toBodyFamily.mass)
            = ((2 : ENNReal) * (1 / 2 : ENNReal)) * (Kakeya.realRpowENN δ eta * F.toBodyFamily.mass) := by
              simp [mul_assoc] <;> rfl
          _ = (1 : ENNReal) * (Kakeya.realRpowENN δ eta * F.toBodyFamily.mass) := by rw [h11]
          _ = Kakeya.realRpowENN δ eta * F.toBodyFamily.mass := by simp
      rw [h_eq]
      exact hY_dense
    have h_bad_le2 : badMass ≤ b := by
      calc badMass ≤ threshold * F.toBodyFamily.enncard := h_bad_le
           _ = b := h_threshold_eq
    calc
      2 * b
        ≤ Y.mass := h_dense2
      _ = Y'.mass + badMass := h_mass_split.symm
      _ ≤ Y'.mass + b := by gcongr
  have h_final : b ≤ Y'.mass := by
    have h_two_b : 2 * b = b + b := by
      simp [two_mul]
      <;> abel
    rw [h_two_b] at h_main
    exact (ENNReal.add_le_add_iff_right h_b_ne_top).mp h_main
  have h_half_mass : (1 / 2 : ENNReal) * Y.mass ≤ Y'.mass := by
    have h_bad_le_half :
        badMass ≤ (1 / 2 : ENNReal) * Y.mass := by
      calc
        badMass ≤ threshold * F.toBodyFamily.enncard := h_bad_le
        _ = b := h_threshold_eq
        _ ≤ (1 / 2 : ENNReal) * Y.mass := by
          dsimp only [b]
          calc
            (1 / 2 : ENNReal) *
                  Kakeya.realRpowENN δ eta *
                  F.toBodyFamily.mass =
                (1 / 2 : ENNReal) *
                  (Kakeya.realRpowENN δ eta *
                    F.toBodyFamily.mass) := by ring
            _ ≤ (1 / 2 : ENNReal) * Y.mass := by
              exact
                mul_le_mul_left'
                  hY_dense (1 / 2 : ENNReal)
    have hsplit :
        Y.mass = Y'.mass + badMass := h_mass_split.symm
    have hsum :
        Y.mass ≤ Y'.mass + (1 / 2 : ENNReal) * Y.mass := by
      calc
        Y.mass = Y'.mass + badMass := hsplit
        _ ≤ Y'.mass + (1 / 2 : ENNReal) * Y.mass := by
          gcongr
    have hhalfTop :
        (1 / 2 : ENNReal) * Y.mass ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · simp
      · have hFmassTop : F.toBodyFamily.mass ≠ ⊤ := by
          rw [h_mass_eq]
          apply ENNReal.mul_ne_top
          · simp [Kakeya.Streamlined.BodyFamily.enncard]
          · exact hV_finite
        have hYle : Y.mass ≤ F.toBodyFamily.mass := by
          apply Finset.sum_le_sum
          intro i _
          exact MeasureTheory.measure_mono (Y.subset_body i)
        exact ne_top_of_le_ne_top hFmassTop hYle
    have hhalfSum :
        (1 / 2 : ENNReal) * Y.mass +
            (1 / 2 : ENNReal) * Y.mass =
          Y.mass := by
      rw [← two_mul]
      have htwoHalf :
          (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
        simpa [one_div] using
          ENNReal.mul_inv_cancel
            (show (2 : ENNReal) ≠ 0 by norm_num)
            (show (2 : ENNReal) ≠ ⊤ by norm_num)
      rw [← mul_assoc, htwoHalf, one_mul]
    have hhalfSumLe :
        (1 / 2 : ENNReal) * Y.mass +
            (1 / 2 : ENNReal) * Y.mass ≤
          Y'.mass + (1 / 2 : ENNReal) * Y.mass := by
      calc
        (1 / 2 : ENNReal) * Y.mass +
              (1 / 2 : ENNReal) * Y.mass =
            Y.mass := hhalfSum
        _ ≤ Y'.mass + (1 / 2 : ENNReal) * Y.mass := hsum
    exact (ENNReal.add_le_add_iff_right hhalfTop).mp hhalfSumLe
  have h_whole : IsWholeTubeSubshading Y' Y := by
    intro i
    by_cases h : i ∈ good
    · exact Or.inl (by simp [Y', carrier', h])
    · exact Or.inr (by simp [Y', carrier', h])
  exact ⟨Y', h_sub, h_half_mass, h_final, h_per_tube, h_whole⟩

lemma mass_retention_under_pruning
    {δ : ℝ} (hdelta : 0 < δ) (hdelta_one : δ ≤ 1)
    {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : Kakeya.Streamlined.TubeShading F}
    {eta : ℝ} (heta : 0 < eta)
    (hY_dense : Y.IsLambdaDense (Kakeya.realRpowENN δ eta)) :
    ∃ (Y' : Kakeya.Streamlined.TubeShading F),
      (∀ i, Y'.carrier i ⊆ Y.carrier i) ∧
      Y'.mass ≥ (1 / 2 : ENNReal) * Kakeya.realRpowENN δ eta * F.toBodyFamily.mass := by
  rcases mass_retention_under_pruning_full hdelta hdelta_one (heta := heta) hY_dense with
    ⟨Y', h_sub, _, h_mass, _, _⟩
  exact ⟨Y', h_sub, h_mass⟩

end Kakeya.Assouad
