import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Multiplicity-weighted horizontal endpoint stub

This is the counting upgrade from the single-graph endpoint estimate to the
two endpoint intervals in the globalization following PYZ Lemma 39.
-/

open MeasureTheory Set

namespace Kakeya.Cinematic

theorem horizontal_stub_multiplicity_volume :
    HorizontalStubMultiplicityVolumeStatement := by
  classical
  intro h_graph_vol F delta L a b mu E hdelta hab hsub hderiv hmu_pos
    hE_meas hE_sub h_mult_lb
  set m : (ℝ × ℝ) → ℝ := multiplicity F delta
  set S : Finset C2Function := F.toFinset with hS_def
  by_cases hS_empty : S = ∅
  · have hF_empty : F.toFinset = ∅ := by
      simpa [hS_def] using hS_empty
    have h_m_zero : ∀ p, m p = 0 := by
      intro p
      have h : m p =
          ∑ f ∈ F.toFinset,
            (graphNeighborhood f delta).indicator
              (fun _ => (1 : ℝ)) p := by
        rfl
      rw [h, hF_empty]
      simp
    have hE_empty : E = ∅ := by
      by_contra h
      rcases Set.nonempty_iff_ne_empty.mpr h with ⟨p, hp⟩
      have h2 : (mu : ℝ) ≤ m p := h_mult_lb p hp
      rw [h_m_zero p] at h2
      have h4 : (0 : ℝ) < (mu : ℝ) := by positivity
      linarith
    rw [hE_empty]
    simp
  · have hS_nonempty : S.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hS_empty
    have hL_nonneg : 0 ≤ L := by
      rcases hS_nonempty with ⟨f, hf⟩
      have hf_carrier : f ∈ F.carrier := by
        simpa [hS_def, FiniteFunctionFamily.toFinset] using hf
      have h1 :
          |f.firstDeriv ⟨0, by simp [unitInterval]⟩| ≤ L :=
        hderiv f hf_carrier _
      have h2 :
          0 ≤ |f.firstDeriv ⟨0, by simp [unitInterval]⟩| :=
        abs_nonneg _
      linarith
    let g : (ℝ × ℝ) → ENNReal := fun p => ENNReal.ofReal (m p)
    let indE : (ℝ × ℝ) → ENNReal :=
      E.indicator (fun _ => (1 : ENNReal))
    have h_indE_meas : Measurable indE :=
      measurable_const.indicator hE_meas
    have h_m_nonneg : ∀ p, 0 ≤ m p := by
      intro p
      have h : m p =
          ∑ f ∈ S,
            (graphNeighborhood f delta).indicator
              (fun _ => (1 : ℝ)) p := by
        rfl
      rw [h]
      apply Finset.sum_nonneg
      intro f _
      exact Set.indicator_nonneg (fun _ => by norm_num) p
    have h1 : ∀ p ∈ E, ENNReal.ofReal (mu : ℝ) ≤ g p := by
      intro p hp
      exact ENNReal.ofReal_le_ofReal (h_mult_lb p hp)
    have h4 :
        ∀ p, indE p * ENNReal.ofReal (mu : ℝ) ≤ indE p * g p := by
      intro p
      by_cases hp : p ∈ E
      · have h5 : indE p = 1 := by simp [indE, hp]
        rw [h5]
        simpa using h1 p hp
      · have h6 : indE p = 0 := by simp [indE, hp]
        rw [h6]
        simp
    have h8 : ∫⁻ p, indE p ∂volume = volume E := by
      rw [lintegral_indicator hE_meas]
      simpa [indE, setLIntegral_one] using rfl
    have h_lintegral_lb :
        ∫⁻ p, indE p * ENNReal.ofReal (mu : ℝ) ∂volume =
          ENNReal.ofReal (mu : ℝ) * volume E := by
      have h7 :
          ∀ p, indE p * ENNReal.ofReal (mu : ℝ) =
            ENNReal.ofReal (mu : ℝ) * indE p := by
        intro p
        ring
      rw [funext h7]
      rw [lintegral_const_mul (ENNReal.ofReal (mu : ℝ)) h_indE_meas]
      rw [h8]
    have h5 :
        ENNReal.ofReal (mu : ℝ) * volume E ≤
          ∫⁻ p, indE p * g p ∂volume := by
      rw [← h_lintegral_lb]
      exact lintegral_mono h4
    have h_expand :
        ∀ p, g p =
          ∑ f ∈ S,
            (graphNeighborhood f delta).indicator
              (fun _ => (1 : ENNReal)) p := by
      intro p
      let summand : C2Function → ℝ := fun f =>
        (graphNeighborhood f delta).indicator
          (fun _ => (1 : ℝ)) p
      have hsummand_nonneg : ∀ f ∈ S, 0 ≤ summand f := by
        intro f _
        exact Set.indicator_nonneg (fun _ => by norm_num) p
      have h_sum : m p = ∑ f ∈ S, summand f := by rfl
      have h_main :
          ENNReal.ofReal (m p) =
            ∑ f ∈ S, ENNReal.ofReal (summand f) := by
        rw [h_sum, ENNReal.ofReal_sum_of_nonneg hsummand_nonneg]
      have h_sum2 :
          ∑ f ∈ S, ENNReal.ofReal (summand f) =
            ∑ f ∈ S,
              (graphNeighborhood f delta).indicator
                (fun _ => (1 : ENNReal)) p := by
        apply Finset.sum_congr rfl
        intro f _
        by_cases h12 : p ∈ graphNeighborhood f delta
        · simp [summand, h12]
        · simp [summand, h12]
      exact h_main.trans h_sum2
    have h12 :
        ∀ p, indE p * g p =
          ∑ f ∈ S,
            (E ∩ graphNeighborhood f delta).indicator
              (fun _ => (1 : ENNReal)) p := by
      intro p
      rw [h_expand p, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      by_cases hE : p ∈ E
        <;> by_cases hG : p ∈ graphNeighborhood f delta
        <;> simp [hE, hG, indE]
    have h12' :
        (fun p : ℝ × ℝ => indE p * g p) =
          fun p : ℝ × ℝ =>
            ∑ f ∈ S,
              (E ∩ graphNeighborhood f delta).indicator
                (fun _ => (1 : ENNReal)) p := by
      funext p
      exact h12 p
    rw [h12'] at h5
    have h_meas :
        ∀ f ∈ S,
          Measurable
            ((E ∩ graphNeighborhood f delta).indicator
              (fun _ => (1 : ENNReal))) := by
      intro f _
      exact measurable_const.indicator
        (hE_meas.inter (measurableSet_graphNeighborhood f delta))
    have h15 :
        ∫⁻ p,
            ∑ f ∈ S,
              (E ∩ graphNeighborhood f delta).indicator
                (fun _ => (1 : ENNReal)) p ∂volume =
          ∑ f ∈ S,
            ∫⁻ p,
              (E ∩ graphNeighborhood f delta).indicator
                (fun _ => (1 : ENNReal)) p ∂volume := by
      rw [lintegral_finsetSum S _]
      exact h_meas
    rw [h15] at h5
    have h16 :
        ∀ f ∈ S,
          ∫⁻ p,
              (E ∩ graphNeighborhood f delta).indicator
                (fun _ => (1 : ENNReal)) p ∂volume =
            volume (E ∩ graphNeighborhood f delta) := by
      intro f _
      have hmeas :
          MeasurableSet (E ∩ graphNeighborhood f delta) :=
        hE_meas.inter (measurableSet_graphNeighborhood f delta)
      rw [lintegral_indicator hmeas]
      simp
    have h17 :
        ∑ f ∈ S,
            ∫⁻ p,
              (E ∩ graphNeighborhood f delta).indicator
                (fun _ => (1 : ENNReal)) p ∂volume =
          ∑ f ∈ S, volume (E ∩ graphNeighborhood f delta) := by
      apply Finset.sum_congr rfl
      intro f hf
      exact h16 f hf
    rw [h17] at h5
    have h18 :
        ∀ f ∈ S,
          volume (E ∩ graphNeighborhood f delta) ≤
            ENNReal.ofReal
              (2 * (1 + L) * delta * (b - a)) := by
      intro f hf
      have hf_carrier : f ∈ F.carrier := by
        simpa [hS_def, FiniteFunctionFamily.toFinset] using hf
      have h19 :
          E ∩ graphNeighborhood f delta ⊆
            graphNeighborhood f delta ∩
              (Set.Icc a b ×ˢ (Set.univ : Set ℝ)) := by
        intro p hp
        exact ⟨hp.2, hE_sub hp.1⟩
      have h20 :
          volume (E ∩ graphNeighborhood f delta) ≤
            volume
              (graphNeighborhood f delta ∩
                (Set.Icc a b ×ˢ (Set.univ : Set ℝ))) :=
        measure_mono h19
      exact h20.trans
        (h_graph_vol hdelta hab hsub (hderiv f hf_carrier))
    have h22 :
        ∑ f ∈ S, volume (E ∩ graphNeighborhood f delta) ≤
          S.card *
            ENNReal.ofReal
              (2 * (1 + L) * delta * (b - a)) := by
      calc
        ∑ f ∈ S, volume (E ∩ graphNeighborhood f delta) ≤
            ∑ _f ∈ S,
              ENNReal.ofReal
                (2 * (1 + L) * delta * (b - a)) :=
          Finset.sum_le_sum h18
        _ = S.card *
              ENNReal.ofReal
                (2 * (1 + L) * delta * (b - a)) := by
          simp [Finset.sum_const]
    have h_card : S.card = F.card := by
      have h1 : S = F.finite.toFinset := by
        simp [hS_def, FiniteFunctionFamily.toFinset]
      rw [h1]
      have h2 :
          F.finite.toFinset.card = F.carrier.ncard :=
        (Set.ncard_eq_toFinset_card F.carrier F.finite).symm
      rw [h2]
      rfl
    rw [h_card] at h22
    have h24 :
        (F.card : ENNReal) *
            ENNReal.ofReal
              (2 * (1 + L) * delta * (b - a)) =
          ENNReal.ofReal
            (2 * (1 + L) * delta * (b - a) *
              (F.card : ℝ)) := by
      have h26 :
          (F.card : ENNReal) = ENNReal.ofReal (F.card : ℝ) := by
        simp
      rw [h26]
      have h27 :
          ENNReal.ofReal
              ((F.card : ℝ) *
                (2 * (1 + L) * delta * (b - a))) =
            ENNReal.ofReal (F.card : ℝ) *
              ENNReal.ofReal
                (2 * (1 + L) * delta * (b - a)) :=
        ENNReal.ofReal_mul (by positivity)
      rw [← h27]
      congr 1
      ring
    rw [h24] at h22
    exact h5.trans h22

end Kakeya.Cinematic
