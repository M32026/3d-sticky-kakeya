import MyLeanRepo.Kakeya.Assouad.ConditionalStatements
import MyLeanRepo.Kakeya.Assouad.CoveringInfrastructure

/-!
WZ Lemma 30: sum the one-cover-ball fiber-volume estimate over an exact finite
external cover and cancel the positive geometric factors.
-/

open MeasureTheory

namespace Kakeya.Assouad

theorem tube_segment_projection_covering_from_fiber :
    TubeSegmentProjectionCoveringFromFiberStatement := by
  intro hfiber delta rho lambda start hdelta hdelta_rho hrho_one hlambda hlambda_one
    base direction v hdir hv htau E hE_meas hE_sub hmass

  let tau := |inner ℝ direction v|
  have hrho_pos : 0 < rho := by linarith
  have htau_pos : 0 < tau := by
    have h1 : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
    have h2 : Real.sqrt rho ≤ tau := htau
    linarith

  set N : ℕ∞ := Metric.externalCoveringNumber ⟨rho, by linarith⟩
    (scalarProjection v E) with hN_def

  by_cases hN_top : N = ⊤
  · have h_main :
        (↑(Metric.externalCoveringNumber ⟨rho, by linarith⟩
          (scalarProjection v E)) : ENNReal) = ⊤ := by
      have h_goal : (↑N : ENNReal) = ⊤ := by exact_mod_cast hN_top
      rw [← hN_def]
      exact h_goal
    rw [h_main]
    have h : (10000 * ENNReal.ofReal rho * (⊤ : ENNReal)) = ⊤ := by
      apply ENNReal.mul_top
      positivity
    rw [h]
    exact le_top
  · obtain ⟨centers, hcenters_finite, hcenters_cover, hcenters_card⟩ :=
      exists_set_encard_eq_externalCoveringNumber hN_top

    let S : Finset ℝ := hcenters_finite.toFinset

    have hS_eq : (S : Set ℝ) = centers := hcenters_finite.coe_toFinset

    have hS_card : (S.card : ENNReal) = (↑N : ENNReal) := by
      have h1 : (↑S.card : ℕ∞) = centers.encard := by
        simpa [S, hcenters_finite.coe_toFinset] using
          hcenters_finite.encard_eq_coe_toFinset_card.symm
      have h2 : centers.encard = N := hcenters_card
      exact_mod_cast (h1.trans h2)

    let E_c (c : ℝ) : Set Point3 :=
      E ∩ {p | dist (inner ℝ p v) c ≤ rho}

    have hfiber_ball : ∀ c ∈ S, MeasureTheory.volume (E_c c) ≤
        ENNReal.ofReal (1000 * delta^2 * rho / tau) := by
      intro c _
      have hsub : E_c c ⊆
          {p | p ∈ tubeSegmentCarrier delta base direction start rho ∧
            dist (inner ℝ p v) c ≤ rho} := by
        intro p hp
        exact ⟨hE_sub hp.1, hp.2⟩
      exact (MeasureTheory.measure_mono hsub).trans
        (hfiber delta rho start c hdelta hdelta_rho hrho_one
          base direction v hdir hv htau)

    have hcover : E ⊆ ⋃ c ∈ S, E_c c := by
      intro p hp
      have hproj : inner ℝ p v ∈ scalarProjection v E := ⟨p, hp, rfl⟩
      have hball_cover : inner ℝ p v ∈
          ⋃ c ∈ centers, Metric.closedBall c rho :=
        hcenters_cover.subset_iUnion_closedBall hproj
      simp only [Set.mem_iUnion] at hball_cover
      rcases hball_cover with ⟨c, hc, hdist⟩
      have hcS : c ∈ S := by
        have h : c ∈ (S : Set ℝ) := by
          rw [hS_eq]
          exact hc
        exact h
      have hdist' : dist (inner ℝ p v) c ≤ rho := by exact_mod_cast hdist
      exact Set.mem_iUnion₂.mpr ⟨c, hcS, ⟨hp, hdist'⟩⟩

    have hsubadd : MeasureTheory.volume E ≤
        ∑ c ∈ S, MeasureTheory.volume (E_c c) := by
      exact (MeasureTheory.measure_mono hcover).trans
        (MeasureTheory.measure_biUnion_finset_le S (fun c => E_c c))

    have hsum_le : ∑ c ∈ S, MeasureTheory.volume (E_c c) ≤
        (S.card : ENNReal) *
          ENNReal.ofReal (1000 * delta^2 * rho / tau) := by
      calc
        ∑ c ∈ S, MeasureTheory.volume (E_c c)
          ≤ ∑ c ∈ S, ENNReal.ofReal (1000 * delta^2 * rho / tau) :=
            Finset.sum_le_sum fun c hc => hfiber_ball c hc
        _ = (S.card : ENNReal) *
            ENNReal.ofReal (1000 * delta^2 * rho / tau) := by
          simp [mul_comm]

    have hmain : MeasureTheory.volume E ≤
        (S.card : ENNReal) *
          ENNReal.ofReal (1000 * delta^2 * rho / tau) :=
      hsubadd.trans hsum_le

    have h3 : ENNReal.ofReal (lambda * delta^2 * Real.sqrt rho) ≤
        (S.card : ENNReal) *
          ENNReal.ofReal (1000 * delta^2 * rho / tau) :=
      hmass.trans hmain

    have hdelta2_ne_zero : ENNReal.ofReal (delta^2) ≠ 0 := by positivity
    have hdelta2_ne_top : ENNReal.ofReal (delta^2) ≠ ⊤ :=
      ENNReal.ofReal_ne_top

    have h4 :
        ENNReal.ofReal (lambda * delta^2 * Real.sqrt rho) *
            ENNReal.ofReal tau ≤
          ((S.card : ENNReal) *
            ENNReal.ofReal (1000 * delta^2 * rho / tau)) *
              ENNReal.ofReal tau := by
      gcongr

    have hLHS :
        ENNReal.ofReal (lambda * delta^2 * Real.sqrt rho) *
            ENNReal.ofReal tau =
          ENNReal.ofReal (lambda * tau * Real.sqrt rho) *
            ENNReal.ofReal (delta^2) := by
      rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      apply congr_arg ENNReal.ofReal
      ring

    have hpos3 : 0 ≤ 1000 * delta^2 * rho / tau := by positivity
    have h11 :
        ENNReal.ofReal (1000 * delta^2 * rho / tau) *
            ENNReal.ofReal tau =
          ENNReal.ofReal (1000 * delta^2 * rho) := by
      have h :
          ENNReal.ofReal ((1000 * delta^2 * rho / tau) * tau) =
            ENNReal.ofReal (1000 * delta^2 * rho / tau) *
              ENNReal.ofReal tau :=
        ENNReal.ofReal_mul hpos3
      have h2 : (1000 * delta^2 * rho / tau) * tau =
          1000 * delta^2 * rho := by
        field_simp [htau_pos.ne']
      have h3 :
          ENNReal.ofReal ((1000 * delta^2 * rho / tau) * tau) =
            ENNReal.ofReal (1000 * delta^2 * rho) := by
        rw [h2]
      exact h.symm.trans h3

    have hpos4 : 0 ≤ 1000 * rho := by positivity
    have h12 : ENNReal.ofReal (1000 * delta^2 * rho) =
        ENNReal.ofReal (1000 * rho) * ENNReal.ofReal (delta^2) := by
      have h : ENNReal.ofReal ((1000 * rho) * delta^2) =
          ENNReal.ofReal (1000 * rho) * ENNReal.ofReal (delta^2) :=
        ENNReal.ofReal_mul hpos4
      have h2 : (1000 * rho) * delta^2 = 1000 * delta^2 * rho := by ring
      rw [h2] at h
      exact h

    have hRHS :
        ((S.card : ENNReal) *
            ENNReal.ofReal (1000 * delta^2 * rho / tau)) *
            ENNReal.ofReal tau =
          ((S.card : ENNReal) * ENNReal.ofReal (1000 * rho)) *
            ENNReal.ofReal (delta^2) := by
      calc
        ((S.card : ENNReal) *
            ENNReal.ofReal (1000 * delta^2 * rho / tau)) *
              ENNReal.ofReal tau
          = (S.card : ENNReal) *
              (ENNReal.ofReal (1000 * delta^2 * rho / tau) *
                ENNReal.ofReal tau) := by ring
        _ = (S.card : ENNReal) *
            ENNReal.ofReal (1000 * delta^2 * rho) := by rw [h11]
        _ = (S.card : ENNReal) *
            (ENNReal.ofReal (1000 * rho) *
              ENNReal.ofReal (delta^2)) := by rw [h12]
        _ = ((S.card : ENNReal) * ENNReal.ofReal (1000 * rho)) *
            ENNReal.ofReal (delta^2) := by ring

    rw [hLHS, hRHS] at h4

    have h5 : ENNReal.ofReal (lambda * tau * Real.sqrt rho) ≤
        (S.card : ENNReal) * ENNReal.ofReal (1000 * rho) :=
      (ENNReal.mul_le_mul_iff_left hdelta2_ne_zero hdelta2_ne_top).mp h4

    have h13 : ENNReal.ofReal (1000 * rho) ≤
        (10000 : ENNReal) * ENNReal.ofReal rho := by
      have h14 : 1000 * rho ≤ 10000 * rho := by linarith
      have h15 : ENNReal.ofReal (1000 * rho) ≤
          ENNReal.ofReal (10000 * rho) :=
        ENNReal.ofReal_le_ofReal h14
      have h16 : ENNReal.ofReal (10000 * rho) =
          (10000 : ENNReal) * ENNReal.ofReal rho := by
        have h161 : ENNReal.ofReal (10000 * rho) =
            ENNReal.ofReal 10000 * ENNReal.ofReal rho := by
          rw [← ENNReal.ofReal_mul (by positivity)]
        have h162 : ENNReal.ofReal 10000 = (10000 : ENNReal) := by simp
        rw [h161, h162]
      rw [h16] at h15
      exact h15

    have h12' : (S.card : ENNReal) * ENNReal.ofReal (1000 * rho) ≤
        (10000 : ENNReal) * ENNReal.ofReal rho * (S.card : ENNReal) := by
      have h121 : (S.card : ENNReal) * ENNReal.ofReal (1000 * rho) ≤
          (S.card : ENNReal) *
            ((10000 : ENNReal) * ENNReal.ofReal rho) := by
        exact mul_le_mul_right h13 (S.card : ENNReal)
      calc
        (S.card : ENNReal) * ENNReal.ofReal (1000 * rho)
          ≤ (S.card : ENNReal) *
              ((10000 : ENNReal) * ENNReal.ofReal rho) := h121
        _ = (10000 : ENNReal) * ENNReal.ofReal rho *
            (S.card : ENNReal) := by ring

    have h17 : ENNReal.ofReal (lambda * tau * Real.sqrt rho) ≤
        (10000 : ENNReal) * ENNReal.ofReal rho * (S.card : ENNReal) :=
      h5.trans h12'

    have h18 : ENNReal.ofReal (lambda * tau * Real.sqrt rho) ≤
        (10000 : ENNReal) * ENNReal.ofReal rho * (↑N : ENNReal) := by
      rw [hS_card] at h17
      exact h17

    simpa [hN_def, tau] using h18

end Kakeya.Assouad
