import MyLeanRepo.Kakeya.Assouad.WZ1.SharpSmoothedFrostmanStatement

/-!
WZ1 Proposition 41: all-scale linear Frostman bound for smoothed measures.
-/

namespace Kakeya.Assouad

open MeasureTheory Set Metric

/-- Volume of a 2D ball as ENNReal.ofReal (π * r²). -/
private lemma volume_ball2 {x : Point2} {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball x r) = ENNReal.ofReal (Real.pi * r^2) := by
  rw [EuclideanSpace.volume_ball_fin_two x r]
  have h1 : ENNReal.ofReal r ^ 2 = ENNReal.ofReal (r^2) := by
    have h11 : ENNReal.ofReal r ^ 2 = ENNReal.ofReal r * ENNReal.ofReal r := by rw [pow_two]
    have h12 : ENNReal.ofReal (r * r) = ENNReal.ofReal r * ENNReal.ofReal r :=
      @ENNReal.ofReal_mul r r hr
    have h13 : r * r = r^2 := by ring
    rw [h11, ←h12, h13]
  rw [h1]
  have h2 : ENNReal.ofReal (r^2) * ENNReal.ofReal Real.pi = ENNReal.ofReal (r^2 * Real.pi) := by
    have h21 : ENNReal.ofReal ((r^2) * Real.pi) = ENNReal.ofReal (r^2) * ENNReal.ofReal Real.pi :=
      @ENNReal.ofReal_mul (r^2) Real.pi (show 0 ≤ r^2 by positivity)
    exact h21.symm
  rw [h2]
  have h3 : r^2 * Real.pi = Real.pi * r^2 := by ring
  rw [h3]

/-- ENNReal division: (ofReal a)⁻¹ * ofReal b = ofReal (b/a) for a > 0, b ≥ 0. -/
private lemma ennreal_ofReal_div {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (ENNReal.ofReal a)⁻¹ * ENNReal.ofReal b = ENNReal.ofReal (b / a) := by
  have h1 : ENNReal.ofReal (b / a) * ENNReal.ofReal a = ENNReal.ofReal b := by
    have h2 : ENNReal.ofReal ((b / a) * a) = ENNReal.ofReal (b / a) * ENNReal.ofReal a :=
      ENNReal.ofReal_mul (show 0 ≤ b / a by positivity)
    have h3 : (b / a) * a = b := by field_simp [ha.ne']
    rw [h3] at h2
    exact h2.symm
  have h4 : ENNReal.ofReal a ≠ 0 := by positivity
  have h5 : ENNReal.ofReal a ≠ ⊤ := by simp
  have h_comm : ENNReal.ofReal (b / a) * ENNReal.ofReal a = ENNReal.ofReal a * ENNReal.ofReal (b / a) := mul_comm _ _
  have h6 : (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal (b / a) * ENNReal.ofReal a) = ENNReal.ofReal (b / a) := by
    rw [h_comm, ← mul_assoc, ENNReal.inv_mul_cancel h4 h5, one_mul]
  rw [h1] at h6
  exact h6

/-- If balls B(z,r) and B(0,ρ) are disjoint, σ(B(z,r)) = 0. -/
private lemma ballUniform_ball_zero
    {ρ : ℝ} (hρ : 0 < ρ) {z : Point2} {r : ℝ} (hr : 0 < r)
    (h_disj : r + ρ ≤ dist z 0) :
    (ballUniformMeasure ρ hρ : Measure Point2) (Metric.ball z r) = 0 := by
  set Vρ := volume (Metric.ball (0 : Point2) ρ) with hVρ
  have hs : MeasurableSet (Metric.ball z r) := Metric.isOpen_ball.measurableSet
  have h_empty : (Metric.ball (0 : Point2) ρ ∩ Metric.ball z r) = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro h
    have h1 : dist y z < r := by simpa [Metric.mem_ball] using h.2
    have h2 : dist y (0 : Point2) < ρ := by simpa [Metric.mem_ball] using h.1
    have h3 : dist z 0 ≤ dist z y + dist y 0 := dist_triangle z y 0
    have h4 : dist z 0 < r + ρ := by
      calc dist z 0 ≤ dist z y + dist y 0 := h3
        _ = dist y z + dist y 0 := by rw [dist_comm]
        _ < r + ρ := by linarith
    linarith
  have h_def : (ballUniformMeasure ρ hρ : Measure Point2) (Metric.ball z r) =
      Vρ⁻¹ * volume (Metric.ball (0 : Point2) ρ ∩ Metric.ball z r) := by
    rw [ballUniformMeasure_apply hρ hs]
  rw [h_def, h_empty]
  <;> simp

theorem wz1_sharp_smoothed_frostman : WZ1SharpSmoothedFrostmanStatement := by
  intro delta C A hA hdelta hdelta1 hC hsep hfrost x r hr
  set ρ : ℝ := delta / 10 with hρ_def
  have hρ : 0 < ρ := by positivity
  set ν : ProbabilityMeasure Point2 := smoothMeasure A hA ρ hρ with hν_def
  set σ : ProbabilityMeasure Point2 := ballUniformMeasure ρ hρ with hσ_def
  have h_ball_meas : MeasurableSet (Metric.ball x r) := Metric.isOpen_ball.measurableSet

  have h_main : (ν : Measure Point2) (Metric.ball x r) =
      (A.card : ENNReal)⁻¹ * ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) := by
    rw [smoothMeasure_apply h_ball_meas]
    apply congr_arg (fun y => (A.card : ENNReal)⁻¹ * y)
    apply Finset.sum_congr rfl
    intro a _
    have h_set : {y : Point2 | a + y ∈ Metric.ball x r} = Metric.ball (x - a) r := by
      ext y
      simp only [Set.mem_setOf_eq, Metric.mem_ball]
      have h_eq : dist (a + y) x = dist y (x - a) := by
        simp [dist_eq_norm, sub_eq_add_neg] <;> abel
      rw [h_eq]
    rw [h_set]

  have h_nonneg : 0 ≤ 100 * C * r := by positivity
  have h_coe : (Real.toNNReal (100 * C * r) : ENNReal) = ENNReal.ofReal (100 * C * r) := by
    have h : ENNReal.ofReal (100 * C * r) = ↑(Real.toNNReal (100 * C * r)) := by
      simp [ENNReal.ofReal, h_nonneg]
    exact h.symm

  have h_card_pos : (A.card : ENNReal) ≠ 0 := by
    have h : 0 < A.card := Finset.card_pos.mpr hA
    exact_mod_cast h.ne'
  have h_card_top : (A.card : ENNReal) ≠ ⊤ := by simp

  have h_goal : (ν : Measure Point2) (Metric.ball x r) ≤ ENNReal.ofReal (100 * C * r) := by
    rw [h_main]

    -- Frostman lower bound: (#A)⁻¹ ≤ C * δ
    obtain ⟨a0, ha0⟩ := hA
    have h_filter_in : a0 ∈ A.filter (fun y => dist y a0 ≤ delta) := by
      simp only [Finset.mem_filter]
      exact ⟨ha0, by simp [hdelta.le]⟩
    have h1 : 1 ≤ A.ballCount a0 delta := by
      have h_card : 1 ≤ (A.filter (fun y => dist y a0 ≤ delta)).card :=
        Finset.one_le_card.mpr ⟨a0, h_filter_in⟩
      simpa [DiscreteSet.ballCount] using h_card
    have h_frost_delta := hfrost a0 delta (by linarith) hdelta1
    have h_rpow1 : Kakeya.realRpowENN delta 1 = ENNReal.ofReal delta := by
      simp [Kakeya.realRpowENN] <;> norm_num
    rw [h_rpow1] at h_frost_delta
    have h_enncard : A.enncard = (A.card : ENNReal) := by simp [DiscreteSet.enncard]
    rw [h_enncard] at h_frost_delta
    set b := ENNReal.ofReal C * ENNReal.ofReal delta with hb_def
    have h2 : 1 ≤ b * (A.card : ENNReal) := h1.trans h_frost_delta
    have h_lower : (A.card : ENNReal)⁻¹ ≤ b := by
      calc (A.card : ENNReal)⁻¹
        = (A.card : ENNReal)⁻¹ * 1 := by simp
      _ ≤ (A.card : ENNReal)⁻¹ * (b * (A.card : ENNReal)) := by gcongr
      _ = b := by
        have h_assoc : b * (A.card : ENNReal) = (A.card : ENNReal) * b := mul_comm _ _
        rw [h_assoc, ←mul_assoc, ENNReal.inv_mul_cancel h_card_pos h_card_top, one_mul]

    by_cases h_small : r < delta
    · -- Case 1: r < δ
      let E := fun a : Point2 => Metric.ball a ρ ∩ Metric.ball x r
      have hE_meas : ∀ (a : Point2), MeasurableSet (E a) := fun a =>
        Metric.isOpen_ball.measurableSet.inter Metric.isOpen_ball.measurableSet
      have h_disj : ∀ a1 ∈ A, ∀ a2 ∈ A, a1 ≠ a2 → Disjoint (E a1) (E a2) := by
        intro a1 ha1 a2 ha2 hne
        have h_dist : delta ≤ dist a1 a2 := hsep ha1 ha2 hne
        have h_2ρ_lt_delta : 2 * ρ < delta := by dsimp only [ρ] <;> linarith
        have h_balls_empty : (Metric.ball a1 ρ ∩ Metric.ball a2 ρ) = ∅ := by
          ext y
          simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
          intro h
          have h1 : dist y a1 < ρ := h.1
          have h2 : dist y a2 < ρ := h.2
          have h3 : dist a1 a2 < 2 * ρ := by
            calc dist a1 a2 ≤ dist a1 y + dist y a2 := dist_triangle a1 y a2
              _ = dist y a1 + dist y a2 := by rw [dist_comm]
              _ < ρ + ρ := by linarith
              _ = 2 * ρ := by ring
          linarith
        have h_disj1 : Disjoint (Metric.ball a1 ρ) (Metric.ball a2 ρ) := by
          rw [Set.disjoint_iff_inter_eq_empty] <;> exact h_balls_empty
        have h_sub1 : E a1 ⊆ Metric.ball a1 ρ := by intro z hz; exact hz.1
        have h_sub2 : E a2 ⊆ Metric.ball a2 ρ := by intro z hz; exact hz.1
        exact h_disj1.mono h_sub1 h_sub2
      have h_sub : ∀ a ∈ A, E a ⊆ Metric.ball x r := by
        intro a _ z hz; exact hz.2

      have hd : (↑A : Set Point2).PairwiseDisjoint E := by
        intro a1 ha1 a2 ha2 hne
        exact h_disj a1 ha1 a2 ha2 hne
      have h_union : volume (⋃ a ∈ A, E a) = ∑ a ∈ A, volume (E a) :=
        MeasureTheory.measure_biUnion_finset hd (fun a _ => hE_meas a)
      have h4 : (⋃ a ∈ A, E a) ⊆ Metric.ball x r := by
        intro y hy
        have h_exists : ∃ a ∈ A, y ∈ E a := by simpa [Finset.mem_biUnion] using hy
        rcases h_exists with ⟨a, ha, hya⟩
        exact h_sub a ha hya
      have h5 : volume (⋃ a ∈ A, E a) ≤ volume (Metric.ball x r) :=
        MeasureTheory.measure_mono h4
      have h_sum_vol : ∑ a ∈ A, volume (E a) ≤ volume (Metric.ball x r) := by
        rw [←h_union]
        exact h5

      set Vρ := volume (Metric.ball (0 : Point2) ρ) with hVρ
      have hVρ_pos : 0 < Vρ := by
        rw [hVρ, volume_ball2 (by linarith)] <;> positivity
      have hVρ_ne_zero : Vρ ≠ 0 := hVρ_pos.ne'
      have hVρ_ne_top : Vρ ≠ ⊤ := by
        rw [hVρ, volume_ball2 (by linarith)] <;> simp [ENNReal.ofReal_ne_top]

      have hσ_formula : ∀ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) =
          Vρ⁻¹ * volume (E a) := by
        intro a _
        have hs : MeasurableSet (Metric.ball (x - a) r) := Metric.isOpen_ball.measurableSet
        rw [ballUniformMeasure_apply hρ hs]
        let S := Metric.ball (0 : Point2) ρ ∩ Metric.ball (x - a) r
        have hS_meas : MeasurableSet S :=
          Metric.isOpen_ball.measurableSet.inter Metric.isOpen_ball.measurableSet
        have h_eq : (fun y : Point2 => a + y) '' S = E a := by
          ext z
          simp only [Set.mem_image, E, Set.mem_inter_iff, Metric.mem_ball]
          constructor
          · rintro ⟨y, hy, rfl⟩
            have h1 : dist (a + y) a < ρ := by simpa [dist_eq_norm] using hy.1
            have h21 : dist y (x - a) < r := hy.2
            have h2 : dist (a + y) x < r := by
              have h_eq : dist (a + y) x = dist y (x - a) := by
                simp [dist_eq_norm, sub_eq_add_neg] <;> abel
              rw [h_eq]; exact h21
            exact ⟨h1, h2⟩
          · intro hz
            refine ⟨z - a, ?_, by simp⟩
            have h1 : dist (z - a) (0 : Point2) < ρ := by simpa [dist_eq_norm] using hz.1
            have h2 : dist (z - a) (x - a) < r := by simpa [dist_eq_norm] using hz.2
            exact ⟨h1, h2⟩
        have h_eq1 : (fun y : Point2 => a + y) '' S = (fun z : Point2 => z - a) ⁻¹' S := by
          ext z
          simp only [Set.mem_image, Set.mem_preimage]
          constructor
          · rintro ⟨y, hy, rfl⟩; simpa using hy
          · intro hz; refine ⟨z - a, hz, by simp⟩
        have hmp : MeasureTheory.MeasurePreserving (fun z : Point2 => z - a) := by
          have h_eq : (fun z : Point2 => z - a) = (fun z : Point2 => -a + z) := by
            funext z; abel
          rw [h_eq]
          exact measurePreserving_add_left volume (-a)
        have h_vol : volume ((fun y : Point2 => a + y) '' S) = volume S := by
          rw [h_eq1]
          exact hmp.measure_preimage hS_meas.nullMeasurableSet
        have h_vol2 : volume (E a) = volume S := by
          rw [←h_eq]
          exact h_vol
        exact congr_arg (fun x => Vρ⁻¹ * x) h_vol2.symm

      have h_sum : ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) =
          Vρ⁻¹ * ∑ a ∈ A, volume (E a) := by
        have h : ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) =
            ∑ a ∈ A, (Vρ⁻¹ * volume (E a)) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hσ_formula a ha
        rw [h, Finset.mul_sum]

      rw [h_sum]
      have h_vol_ratio : Vρ⁻¹ * volume (Metric.ball x r) = ENNReal.ofReal (r^2 / ρ^2) := by
        rw [hVρ, volume_ball2 (show 0 ≤ ρ by linarith), volume_ball2 (show 0 ≤ r by linarith)]
        rw [ennreal_ofReal_div (by positivity) (by positivity)]
        congr 1
        field_simp [hρ.ne'] <;> ring
      have h_step1 : Vρ⁻¹ * ∑ a ∈ A, volume (E a) ≤ ENNReal.ofReal (r^2 / ρ^2) := by
        calc Vρ⁻¹ * ∑ a ∈ A, volume (E a)
          ≤ Vρ⁻¹ * volume (Metric.ball x r) := by gcongr
        _ = ENNReal.ofReal (r^2 / ρ^2) := h_vol_ratio
      have h6 : (A.card : ENNReal)⁻¹ * (Vρ⁻¹ * ∑ a ∈ A, volume (E a)) ≤
          b * ENNReal.ofReal (r^2 / ρ^2) := by
        calc (A.card : ENNReal)⁻¹ * (Vρ⁻¹ * ∑ a ∈ A, volume (E a))
          ≤ (A.card : ENNReal)⁻¹ * ENNReal.ofReal (r^2 / ρ^2) := by gcongr
        _ ≤ b * ENNReal.ofReal (r^2 / ρ^2) := by gcongr
      have h7 : b * ENNReal.ofReal (r^2 / ρ^2) =
          ENNReal.ofReal (C * delta * (r^2 / ρ^2)) := by
        simp only [hb_def]
        have h_mul : ENNReal.ofReal C * ENNReal.ofReal delta * ENNReal.ofReal (r^2 / ρ^2) =
            ENNReal.ofReal (C * delta * (r^2 / ρ^2)) := by
          have h1 : 0 ≤ C := by linarith
          have h2 : 0 ≤ delta := by linarith
          have h3 : 0 ≤ r^2 / ρ^2 := by positivity
          have h_mul1 : ENNReal.ofReal C * ENNReal.ofReal delta = ENNReal.ofReal (C * delta) :=
            (ENNReal.ofReal_mul h1).symm
          have h_mul2 : ENNReal.ofReal (C * delta) * ENNReal.ofReal (r^2 / ρ^2) =
              ENNReal.ofReal ((C * delta) * (r^2 / ρ^2)) :=
            (ENNReal.ofReal_mul (by positivity)).symm
          rw [h_mul1, h_mul2] <;> ring
        exact h_mul
      rw [h7] at h6
      have h8 : C * delta * (r^2 / ρ^2) = 100 * C * r^2 / delta := by
        dsimp only [ρ]
        field_simp [hdelta.ne'] <;> ring
      rw [h8] at h6
      have h91 : r^2 / delta ≤ r := by
        have h11 : 0 < delta := hdelta
        have h12 : r < delta := h_small
        have h : r^2 ≤ r * delta := by nlinarith
        calc r^2 / delta ≤ (r * delta) / delta := by gcongr
          _ = r := by field_simp [h11.ne'] <;> ring
      have h9 : 100 * C * r^2 / delta ≤ 100 * C * r := by
        have h10 : 0 < C := by linarith
        have h_pos : 0 ≤ 100 * C := by positivity
        have h_eq : 100 * C * r^2 / delta = 100 * C * (r^2 / delta) := by ring
        rw [h_eq]
        exact mul_le_mul_of_nonneg_left h91 h_pos
      exact h6.trans (ENNReal.ofReal_le_ofReal h9)

    · -- Case 2: δ ≤ r
      have h_large : delta ≤ r := by linarith
      let S := A.filter (fun a : Point2 => dist x a < r + ρ)
      have h1 : ∑ a ∈ S, (σ : Measure Point2) (Metric.ball (x - a) r) =
          ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro a ha hna
        have h_not : ¬(dist x a < r + ρ) := by
          simpa [S, Finset.mem_filter, ha] using hna
        have h' : r + ρ ≤ dist x a := by linarith
        have h_eq : dist (x - a) 0 = dist x a := by
          simp [dist_eq_norm, sub_eq_add_neg] <;> abel
        have h_dist : r + ρ ≤ dist (x - a) 0 := by rw [h_eq]; exact h'
        exact ballUniform_ball_zero hρ hr h_dist

      have h2 : ∑ a ∈ S, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ (S.card : ENNReal) := by
        have h3 : ∀ a ∈ S, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ 1 := by
          intro a _
          have h4 : (σ : Measure Point2) (Metric.ball (x - a) r) ≤ (σ : Measure Point2) Set.univ :=
            MeasureTheory.measure_mono (Set.subset_univ _)
          simpa using h4
        have h_sum1 : ∑ a ∈ S, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ ∑ a ∈ S, (1 : ENNReal) :=
          Finset.sum_le_sum h3
        have h_sum2 : ∑ a ∈ S, (1 : ENNReal) = (S.card : ENNReal) := by simp
        rw [h_sum2] at h_sum1
        exact h_sum1

      have hS_sub : S ⊆ A.filter (fun a => dist x a ≤ r + ρ) := by
        intro a ha
        have h4 : a ∈ A ∧ dist x a < r + ρ := by simpa [S, Finset.mem_filter] using ha
        simp only [Finset.mem_filter] at *
        exact ⟨h4.1, by linarith⟩

      have h4 : (S.card : ENNReal) ≤ A.ballCount x (r + ρ) := by
        have h5 : S.card ≤ (A.filter (fun a => dist x a ≤ r + ρ)).card :=
          Finset.card_le_card hS_sub
        have h_comm_filter : A.filter (fun y : Point2 => dist y x ≤ r + ρ) =
            A.filter (fun a : Point2 => dist x a ≤ r + ρ) := by
          apply Finset.ext; intro y; simp [dist_comm]
        have h6 : A.ballCount x (r + ρ) = ((A.filter (fun a => dist x a ≤ r + ρ)).card : ENNReal) := by
          simp [DiscreteSet.ballCount, h_comm_filter]
        rw [h6]
        exact_mod_cast h5

      have h4' : ∑ a ∈ S, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ A.ballCount x (r + ρ) :=
        h2.trans h4

      have h5 : (A.card : ENNReal)⁻¹ * ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) ≤
          (A.card : ENNReal)⁻¹ * A.ballCount x (r + ρ) := by
        rw [←h1]
        gcongr

      by_cases h_small2 : r + ρ ≤ 1
      · -- Subcase 2a: r + ρ ≤ 1
        have hδr : delta ≤ r + ρ := by dsimp only [ρ] <;> linarith
        have h_frost2 : A.ballCount x (r + ρ) ≤
            ENNReal.ofReal C * Kakeya.realRpowENN (r + ρ) 1 * A.enncard :=
          hfrost x (r + ρ) hδr h_small2
        have h_rpow : Kakeya.realRpowENN (r + ρ) 1 = ENNReal.ofReal (r + ρ) := by
          simp [Kakeya.realRpowENN] <;> norm_num
        rw [h_rpow] at h_frost2
        have h_enncard2 : A.enncard = (A.card : ENNReal) := by simp [DiscreteSet.enncard]
        rw [h_enncard2] at h_frost2
        set b2 := ENNReal.ofReal C * ENNReal.ofReal (r + ρ) with hb2_def
        have h6 : (A.card : ENNReal)⁻¹ * A.ballCount x (r + ρ) ≤ b2 := by
          have h7 : (A.card : ENNReal)⁻¹ * A.ballCount x (r + ρ) ≤
              (A.card : ENNReal)⁻¹ * (b2 * (A.card : ENNReal)) := by gcongr
          have h8 : (A.card : ENNReal)⁻¹ * (b2 * (A.card : ENNReal)) = b2 := by
            have h_comm : b2 * (A.card : ENNReal) = (A.card : ENNReal) * b2 := mul_comm _ _
            rw [h_comm, ←mul_assoc, ENNReal.inv_mul_cancel h_card_pos h_card_top, one_mul]
          rw [h8] at h7
          exact h7
        have h9 : C * (r + ρ) ≤ 100 * C * r := by
          have h10 : ρ ≤ r / 10 := by dsimp only [ρ] <;> linarith
          have h11 : 0 < C := by linarith
          nlinarith
        have h10 : b2 ≤ ENNReal.ofReal (100 * C * r) := by
          have h11 : b2 = ENNReal.ofReal (C * (r + ρ)) := by
            simp only [hb2_def]
            have h12 : 0 ≤ C := by linarith
            have h13 : 0 ≤ r + ρ := by linarith
            have h : ENNReal.ofReal C * ENNReal.ofReal (r + ρ) = ENNReal.ofReal (C * (r + ρ)) :=
              (ENNReal.ofReal_mul h12).symm
            exact h
          rw [h11]
          exact ENNReal.ofReal_le_ofReal h9
        exact h5.trans (h6.trans h10)

      · -- Subcase 2b: r + ρ > 1
        have h_goal2 : (A.card : ENNReal)⁻¹ * ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) ≤ 1 := by
          have h_eq2 : (A.card : ENNReal)⁻¹ * ∑ a ∈ A, (σ : Measure Point2) (Metric.ball (x - a) r) =
              (ν : Measure Point2) (Metric.ball x r) := by
            rw [←h_main]
          rw [h_eq2]
          have h : (ν : Measure Point2) (Metric.ball x r) ≤ (ν : Measure Point2) Set.univ :=
            MeasureTheory.measure_mono (Set.subset_univ _)
          simpa using h
        have h10 : 1 < 100 * C * r := by
          have h11 : r + ρ > 1 := by linarith
          have h12 : ρ ≤ r / 10 := by dsimp only [ρ] <;> linarith
          have h13 : 11 * r / 10 > 1 := by linarith
          have h14 : r > 10 / 11 := by linarith
          nlinarith
        have h15 : (1 : ENNReal) ≤ ENNReal.ofReal (100 * C * r) := by
          simpa [ENNReal.ofReal_le_ofReal_iff] using h10.le
        exact h_goal2.trans h15

  let a : NNReal := ν (Metric.ball x r)
  let b : NNReal := Real.toNNReal (100 * C * r)
  have h_goal2 : (ν : Measure Point2) (Metric.ball x r) ≤ (b : ENNReal) := by
    rw [h_coe]
    exact h_goal
  have h_eq1 : (a : ENNReal) = (ν : Measure Point2) (Metric.ball x r) :=
    ν.ennreal_coeFn_eq_coeFn_toMeasure (Metric.ball x r)
  have h_goal3 : (a : ENNReal) ≤ (b : ENNReal) := by
    rw [h_eq1]
    exact h_goal2
  have h_goal4 : (a : ℝ) ≤ (b : ℝ) := by
    have h5 : (a : ENNReal) ≤ (b : ENNReal) := h_goal3
    have ha_top : (a : ENNReal) ≠ ⊤ := by simp
    have hb_top : (b : ENNReal) ≠ ⊤ := by simp
    have h6 : (a : ENNReal).toReal ≤ (b : ENNReal).toReal :=
      (ENNReal.toReal_le_toReal ha_top hb_top).mpr h5
    have h7 : (a : ENNReal).toReal = (a : ℝ) := by simp
    have h8 : (b : ENNReal).toReal = (b : ℝ) := by simp
    rw [h7, h8] at h6
    exact h6
  have h_final : a ≤ b := NNReal.coe_le_coe.mp h_goal4
  exact h_final

end Kakeya.Assouad
