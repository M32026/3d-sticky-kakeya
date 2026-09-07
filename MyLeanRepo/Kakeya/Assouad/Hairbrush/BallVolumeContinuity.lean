import MyLeanRepo.Kakeya.AssertionD
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuity of ball volume

This module proves that `(x, r) ↦ volume (s ∩ Metric.ball x r)` is continuous
for measurable `s` with finite volume, on the domain `r > 0`.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

/-- The volume of `s ∩ closedBall x r` equals `s ∩ ball x r`, since the
sphere has Lebesgue measure zero. -/
lemma volume_inter_closedBall_eq_ball {s : Set Point3}
    (hs : MeasurableSet s) (hfin : volume s ≠ ⊤) (x : Point3) (r : ℝ) :
    volume (s ∩ Metric.closedBall x r) = volume (s ∩ Metric.ball x r) := by
  have hcomp : IsCompact (Metric.closedBall x r) :=
    ProperSpace.isCompact_closedBall x r
  have hfin_cb : volume (Metric.closedBall x r) ≠ ⊤ := by
    exact IsCompact.measure_ne_top hcomp
  have hfin_b : volume (Metric.ball x r) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin_cb (measure_mono ball_subset_closedBall)
  have h_real : volume.real (Metric.closedBall x r) = volume.real (Metric.ball x r) :=
    MeasureTheory.Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume x r
  have h_eq_ball : volume (Metric.closedBall x r) = volume (Metric.ball x r) := by
    have h1 : ENNReal.ofReal (volume.real (Metric.closedBall x r)) = volume (Metric.closedBall x r) :=
      ENNReal.ofReal_toReal hfin_cb
    have h2 : ENNReal.ofReal (volume.real (Metric.ball x r)) = volume (Metric.ball x r) :=
      ENNReal.ofReal_toReal hfin_b
    rw [←h1, ←h2, h_real]
  have h_decomp : Metric.closedBall x r = Metric.ball x r ∪ Metric.sphere x r := by
    ext y
    have h : dist y x ≤ r ↔ dist y x < r ∨ dist y x = r := le_iff_lt_or_eq
    simpa [Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere, Set.mem_union] using h
  have h_disj : Disjoint (Metric.ball x r) (Metric.sphere x r) := by
    rw [Set.disjoint_left]
    intro y h1 h2
    have h1' : dist y x < r := by simpa [Metric.mem_ball] using h1
    have h2_norm : ‖y - x‖ = r := by simpa [Metric.mem_sphere] using h2
    have h2' : dist y x = r := by
      have hdist : dist y x = ‖y - x‖ := dist_eq_norm y x
      rw [hdist, h2_norm]
    linarith
  have h_ms_ball : MeasurableSet (Metric.ball x r) := measurableSet_ball
  have h_ms_sphere : MeasurableSet (Metric.sphere x r) := isClosed_sphere.measurableSet
  have h_vol_union : volume (Metric.closedBall x r) =
      volume (Metric.ball x r) + volume (Metric.sphere x r) := by
    rw [h_decomp]
    exact measure_union h_disj h_ms_sphere
  rw [h_eq_ball] at h_vol_union
  have h_sphere_zero : volume (Metric.sphere x r) = 0 := by
    have h' : volume (Metric.ball x r) + volume (Metric.sphere x r) = volume (Metric.ball x r) :=
      h_vol_union.symm
    exact Measure.addHaar_sphere volume x r
  have h_s_sphere_zero : volume (s ∩ Metric.sphere x r) = 0 :=
    measure_mono_null Set.inter_subset_right h_sphere_zero
  have h_inter_union : s ∩ (Metric.ball x r ∪ Metric.sphere x r) =
      (s ∩ Metric.ball x r) ∪ (s ∩ Metric.sphere x r) := by
    ext z
    constructor
    · rintro ⟨hz1, (h | h)⟩
      · exact Or.inl ⟨hz1, h⟩
      · exact Or.inr ⟨hz1, h⟩
    · rintro (h | h)
      · exact ⟨h.1, Or.inl h.2⟩
      · exact ⟨h.1, Or.inr h.2⟩
  have h_s_decomp : s ∩ Metric.closedBall x r =
      (s ∩ Metric.ball x r) ∪ (s ∩ Metric.sphere x r) := by
    rw [h_decomp, h_inter_union]
  have h_disj2 : Disjoint (s ∩ Metric.ball x r) (s ∩ Metric.sphere x r) :=
    h_disj.mono Set.inter_subset_right Set.inter_subset_right
  have h_ms1 : MeasurableSet (s ∩ Metric.ball x r) := hs.inter h_ms_ball
  have h_ms2 : MeasurableSet (s ∩ Metric.sphere x r) := hs.inter h_ms_sphere
  rw [h_s_decomp]
  have h_final : volume ((s ∩ Metric.ball x r) ∪ (s ∩ Metric.sphere x r)) =
      volume (s ∩ Metric.ball x r) + volume (s ∩ Metric.sphere x r) := by
    exact measure_union h_disj2 h_ms2
  rw [h_final, h_s_sphere_zero, add_zero]

/-- Continuity of `(x, r) ↦ volume (s ∩ Metric.ball x r)` for measurable `s`
with finite volume, on the domain `r > 0`. -/
lemma continuousOn_volume_inter_ball {s : Set Point3}
    (hs : MeasurableSet s) (hfin : volume s ≠ ⊤) :
    ContinuousOn (fun p : Point3 × ℝ => volume (s ∩ Metric.ball p.1 p.2))
      {p | 0 < p.2} := by
  let f : Point3 → ℝ → ENNReal := fun x r => volume (s ∩ Metric.ball x r)
  have h_mono : ∀ x, Monotone (f x) := by
    intro x r1 r2 h
    exact measure_mono (inter_subset_inter_right s (ball_subset_ball h))
  have h_finite : ∀ x r, f x r ≠ ⊤ := by
    intro x r
    exact ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  -- Left limit: f x r = ⨆ n, f x (r - 1/(n+1))
  have h_left : ∀ (x : Point3) {r : ℝ}, 0 < r →
      f x r = ⨆ n : ℕ, f x (r - 1 / (n + 1 : ℝ)) := by
    intro x r hr
    let A : ℕ → Set Point3 := fun n => s ∩ Metric.ball x (r - 1 / (n + 1 : ℝ))
    have hA_mono : Monotone A := by
      intro m n hmn
      have h : r - 1 / (m + 1 : ℝ) ≤ r - 1 / (n + 1 : ℝ) := by gcongr
      exact inter_subset_inter_right s (ball_subset_ball h)
    have h_union : (⋃ n, A n) = s ∩ Metric.ball x r := by
      ext y
      simp only [A, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨n, hs, hball⟩
        have h1 : dist y x < r - 1 / (n + 1 : ℝ) := by simpa [Metric.mem_ball] using hball
        have h2 : 0 < (1 : ℝ) / (n + 1) := by positivity
        have h : dist y x < r := by linarith
        exact ⟨hs, by simpa [Metric.mem_ball] using h⟩
      · rintro ⟨hs, hball⟩
        have hdist : dist y x < r := by simpa [Metric.mem_ball] using hball
        have hpos : 0 < r - dist y x := by linarith
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / (r - dist y x))
        have h2 : 1 / (n + 1 : ℝ) < r - dist y x := by
          have h3 : (n : ℝ) > 1 / (r - dist y x) := by exact_mod_cast hn
          have h4 : 1 / ((n : ℝ) + 1) < 1 / (1 / (r - dist y x)) := by
            apply one_div_lt_one_div_of_lt
            · positivity
            · linarith
          have h5 : 1 / (1 / (r - dist y x)) = r - dist y x := by
            field_simp [hpos.ne'] <;> ring
          rw [h5] at h4
          exact h4
        have h6 : dist y x < r - 1 / (n + 1 : ℝ) := by linarith
        exact ⟨n, hs, by simpa [Metric.mem_ball] using h6⟩
    have h_dir : DirectedOn (fun (i j : ℕ) => A i ⊆ A j) Set.univ := by
      intro m _ n _
      refine ⟨max m n, by trivial, hA_mono (le_max_left m n), hA_mono (le_max_right m n)⟩
    have h_null : ∀ n, NullMeasurableSet (A n) volume := by
      intro n; exact (hs.inter measurableSet_ball).nullMeasurableSet
    have h_eq : volume (⋃ n, A n) = ⨆ n, volume (A n) := by
      have h_main := measure_biUnion_eq_iSup (μ := volume) countable_univ h_dir
      simpa using h_main
    have h1 : volume (s ∩ Metric.ball x r) = ⨆ n, volume (A n) := by
      have h2 : volume (⋃ n, A n) = volume (s ∩ Metric.ball x r) := by rw [h_union]
      exact h2.symm.trans h_eq
    simpa [A, f] using h1
  -- Right limit: f x r = ⨅ n, f x (r + 1/(n+1))
  have h_right : ∀ (x : Point3) {r : ℝ}, 0 < r →
      f x r = ⨅ n : ℕ, f x (r + 1 / (n + 1 : ℝ)) := by
    intro x r hr
    let B : ℕ → Set Point3 := fun n => s ∩ Metric.ball x (r + 1 / (n + 1 : ℝ))
    have hB_anti : Antitone B := by
      intro m n hmn
      have h : r + 1 / (m + 1 : ℝ) ≥ r + 1 / (n + 1 : ℝ) := by gcongr
      exact inter_subset_inter_right s (ball_subset_ball h)
    have h_inter : (⋂ n, B n) = s ∩ Metric.closedBall x r := by
      ext y
      have h_iff : (∀ n : ℕ, y ∈ B n) ↔ y ∈ s ∩ Metric.closedBall x r := by
        constructor
        · intro hall
          have hs : y ∈ s := (hall 0).1
          have hdist : ∀ n : ℕ, dist y x < r + 1 / (n + 1 : ℝ) := by
            intro n; exact (hall n).2
          have hle : dist y x ≤ r := by
            by_contra h''
            have hgt : dist y x > r := by linarith
            have hpos : 0 < dist y x - r := by linarith
            obtain ⟨n, hn⟩ := exists_nat_gt (1 / (dist y x - r))
            have h2 : 1 / (n + 1 : ℝ) < dist y x - r := by
              have h3 : (n : ℝ) > 1 / (dist y x - r) := by exact_mod_cast hn
              have h_pos2 : 0 < 1 / (dist y x - r) := by positivity
              have h_lt : 1 / (dist y x - r) < (n : ℝ) + 1 := by linarith
              have h4 : 1 / ((n : ℝ) + 1) < 1 / (1 / (dist y x - r)) :=
                one_div_lt_one_div_of_lt h_pos2 h_lt
              have h5 : 1 / (1 / (dist y x - r)) = dist y x - r := by
                field_simp [hpos.ne'] <;> ring
              rw [h5] at h4; exact h4
            have h6 := hdist n
            linarith
          exact ⟨hs, hle⟩
        · rintro ⟨hs, hle⟩
          intro n
          have h_pos : 0 < (1 : ℝ) / (n + 1) := by positivity
          have h : dist y x < r + 1 / (n + 1 : ℝ) := by
            calc dist y x ≤ r := hle
              _ < r + 1 / (n + 1 : ℝ) := by linarith
          exact ⟨hs, by simpa [Metric.mem_ball] using h⟩
      simpa [B, Set.mem_iInter] using h_iff
    have h_fin : ∃ i, volume (B i) ≠ ⊤ := by
      refine ⟨0, ?_⟩
      simpa [B, f] using h_finite x (r + 1)
    have h_null : ∀ i, NullMeasurableSet (B i) volume := by
      intro i; exact (hs.inter measurableSet_ball).nullMeasurableSet
    have h_simp1 : ∀ i : ℕ, (⋂ j : ℕ, ⋂ (_ : j ≤ i), B j) = B i := by
      intro i
      ext y
      simp only [Set.mem_iInter]
      constructor
      · intro h
        exact h i (by linarith)
      · intro hy j hj
        exact hB_anti hj hy
    have h_eq : volume (⋂ n, B n) = ⨅ n, volume (B n) := by
      have h_main := measure_iInter_eq_iInf_measure_iInter_le (f := B) h_null h_fin
      rw [h_main]
      have h9 : (⨅ i : ℕ, volume (⋂ j : ℕ, ⋂ (_ : j ≤ i), B j)) = ⨅ i : ℕ, volume (B i) := by
        congr with i
        <;> rw [h_simp1 i]
      exact h9
    have h_cb : volume (s ∩ Metric.closedBall x r) = volume (s ∩ Metric.ball x r) :=
      volume_inter_closedBall_eq_ball hs hfin x r
    have h6 : volume (⋂ n, B n) = volume (s ∩ Metric.closedBall x r) := by rw [h_inter]
    have h7 : volume (s ∩ Metric.ball x r) = ⨅ n, volume (B n) := by
      calc volume (s ∩ Metric.ball x r)
        = volume (s ∩ Metric.closedBall x r) := h_cb.symm
      _ = volume (⋂ n, B n) := h6.symm
      _ = ⨅ n, volume (B n) := h_eq
    simpa [B, f] using h7
  -- Squeeze: if dist x x₀ < δ and δ < r, then f x₀ (r-δ) ≤ f x r ≤ f x₀ (r+δ)
  have h_squeeze : ∀ (x x₀ : Point3) (r δ : ℝ), 0 < δ → δ < r → dist x x₀ < δ →
      f x₀ (r - δ) ≤ f x r ∧ f x r ≤ f x₀ (r + δ) := by
    intro x x₀ r δ hδ_pos hδ_lt_r hdist
    have h1 : Metric.ball x r ⊆ Metric.ball x₀ (r + δ) := by
      apply Metric.ball_subset_ball'
      linarith
    have h2 : Metric.ball x₀ (r - δ) ⊆ Metric.ball x r := by
      apply Metric.ball_subset_ball'
      linarith [dist_comm x x₀]
    constructor
    · exact measure_mono (inter_subset_inter_right s h2)
    · exact measure_mono (inter_subset_inter_right s h1)
  -- Prove continuity of the real-valued version
  have h_cont_real : ∀ (x₀ : Point3) (r₀ : ℝ), 0 < r₀ →
      ContinuousAt (fun p : Point3 × ℝ => (f p.1 p.2).toReal) (x₀, r₀) := by
    intro x₀ r₀ hr₀
    have h_finite' : f x₀ r₀ ≠ ⊤ := h_finite x₀ r₀
    have h_left' := h_left x₀ hr₀
    have h_right' := h_right x₀ hr₀
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    -- Find n₁ for left bound
    have h_exists1 : ∃ n₁ : ℕ, (f x₀ r₀).toReal - (f x₀ (r₀ - 1 / (n₁ + 1 : ℝ))).toReal < ε := by
      by_cases hcase : (f x₀ r₀).toReal < ε
      · refine ⟨0, ?_⟩
        have h_nonneg : 0 ≤ (f x₀ (r₀ - 1 / (0 + 1 : ℝ))).toReal := by positivity
        linarith
      · have h_ge : ε ≤ (f x₀ r₀).toReal := by linarith
        set b : ENNReal := ENNReal.ofReal ((f x₀ r₀).toReal - ε) with hb_def
        have hb_ne : b ≠ ⊤ := by simp [b, hb_def]
        have h_b_lt : b < f x₀ r₀ := by
          have h_pos : 0 ≤ (f x₀ r₀).toReal - ε := by linarith
          have h_b_real : b.toReal = (f x₀ r₀).toReal - ε := by
            rw [hb_def, ENNReal.toReal_ofReal h_pos]
          have h : b.toReal < (f x₀ r₀).toReal := by
            rw [h_b_real] <;> linarith
          exact (ENNReal.toReal_lt_toReal hb_ne h_finite').mp h
        have h4 : b < ⨆ n : ℕ, f x₀ (r₀ - 1 / (n + 1 : ℝ)) := by
          rw [←h_left'] <;> exact h_b_lt
        have h5 : ∃ n₁ : ℕ, b < f x₀ (r₀ - 1 / (n₁ + 1 : ℝ)) := by
          simpa [lt_iSup_iff] using h4
        rcases h5 with ⟨n₁, hn₁⟩
        refine ⟨n₁, ?_⟩
        have h6 : (f x₀ r₀).toReal - ε < (f x₀ (r₀ - 1 / (n₁ + 1 : ℝ))).toReal := by
          have h7 : b.toReal < (f x₀ (r₀ - 1 / (n₁ + 1 : ℝ))).toReal :=
            (ENNReal.toReal_lt_toReal hb_ne (h_finite _ _)).mpr hn₁
          have h_pos2 : 0 ≤ (f x₀ r₀).toReal - ε := by linarith
          have h_b_real2 : b.toReal = (f x₀ r₀).toReal - ε := by
            rw [hb_def, ENNReal.toReal_ofReal h_pos2]
          rw [h_b_real2] at h7
          exact h7
        linarith
    -- Find n₂ for right bound
    have h_exists2 : ∃ n₂ : ℕ, (f x₀ (r₀ + 1 / (n₂ + 1 : ℝ))).toReal - (f x₀ r₀).toReal < ε := by
      set c : ENNReal := ENNReal.ofReal ((f x₀ r₀).toReal + ε) with hc_def
      have hc_ne : c ≠ ⊤ := by simp [c, hc_def]
      have h_a_lt : f x₀ r₀ < c := by
        have h_pos : 0 ≤ (f x₀ r₀).toReal + ε := by positivity
        have h_c_real : c.toReal = (f x₀ r₀).toReal + ε := by
          rw [hc_def, ENNReal.toReal_ofReal h_pos]
        have h : (f x₀ r₀).toReal < c.toReal := by
          rw [h_c_real] <;> linarith
        exact (ENNReal.toReal_lt_toReal h_finite' hc_ne).mp h
      have h4 : (⨅ n : ℕ, f x₀ (r₀ + 1 / (n + 1 : ℝ))) < c := by
        rw [←h_right'] <;> exact h_a_lt
      have h5 : ∃ n₂ : ℕ, f x₀ (r₀ + 1 / (n₂ + 1 : ℝ)) < c := by
        by_contra h
        push_neg at h
        have h6 : c ≤ ⨅ n : ℕ, f x₀ (r₀ + 1 / (n + 1 : ℝ)) := by
          exact le_iInf h
        have h7 : (⨅ n : ℕ, f x₀ (r₀ + 1 / (n + 1 : ℝ))) < c := h4
        exact False.elim (not_le.mpr h7 h6)
      rcases h5 with ⟨n₂, hn₂⟩
      refine ⟨n₂, ?_⟩
      have h6 : (f x₀ (r₀ + 1 / (n₂ + 1 : ℝ))).toReal < (f x₀ r₀).toReal + ε := by
        have h7 : (f x₀ (r₀ + 1 / (n₂ + 1 : ℝ))).toReal < c.toReal :=
          (ENNReal.toReal_lt_toReal (h_finite _ _) hc_ne).mpr hn₂
        have h_pos2 : 0 ≤ (f x₀ r₀).toReal + ε := by positivity
        have h_c_real2 : c.toReal = (f x₀ r₀).toReal + ε := by
          rw [hc_def, ENNReal.toReal_ofReal h_pos2]
        rw [h_c_real2] at h7
        exact h7
      linarith
    rcases h_exists1 with ⟨n₁, hn₁⟩
    rcases h_exists2 with ⟨n₂, hn₂⟩
    let δ₁ : ℝ := 1 / (2 * (n₁ + 1 : ℝ))
    let δ₂ : ℝ := 1 / (2 * (n₂ + 1 : ℝ))
    let δ : ℝ := min (min δ₁ δ₂) (r₀ / 2)
    have hδ_pos : 0 < δ := by positivity
    have hδ1 : δ ≤ δ₁ := by exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hδ2 : δ ≤ δ₂ := by exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hδ_half : δ ≤ r₀ / 2 := min_le_right _ _
    refine ⟨δ, hδ_pos, ?_⟩
    intro p hp
    have hdist : dist p.1 x₀ < δ := by
      have h : dist p.1 x₀ ≤ dist p (x₀, r₀) := by
        have h' := LipschitzWith.prod_fst.dist_le_mul p (x₀, r₀)
        simpa using h'
      exact h.trans_lt hp
    have hrad : |p.2 - r₀| < δ := by
      have h : dist p.2 r₀ ≤ dist p (x₀, r₀) := by
        have h' := LipschitzWith.prod_snd.dist_le_mul p (x₀, r₀)
        simpa using h'
      have h2 : dist p.2 r₀ = |p.2 - r₀| := by simp [Real.dist_eq]
      rw [h2] at h
      exact h.trans_lt hp
    have h_r_pos : 0 < p.2 := by linarith [abs_lt.mp hrad]
    have hδ_lt_r : δ < p.2 := by linarith [abs_lt.mp hrad]
    have h_sq := h_squeeze p.1 x₀ p.2 δ hδ_pos hδ_lt_r hdist
    have h1 : p.2 - δ > r₀ - 2 * δ := by linarith [abs_lt.mp hrad]
    have h2 : p.2 + δ < r₀ + 2 * δ := by linarith [abs_lt.mp hrad]
    have h3 : f x₀ (r₀ - 2 * δ) ≤ f p.1 p.2 := by
      calc f x₀ (r₀ - 2 * δ) ≤ f x₀ (p.2 - δ) := h_mono x₀ (by linarith)
        _ ≤ f p.1 p.2 := h_sq.1
    have h4 : f p.1 p.2 ≤ f x₀ (r₀ + 2 * δ) := by
      calc f p.1 p.2 ≤ f x₀ (p.2 + δ) := h_sq.2
        _ ≤ f x₀ (r₀ + 2 * δ) := h_mono x₀ (by linarith)
    have h5 : 2 * δ ≤ 1 / (n₁ + 1 : ℝ) := by
      calc 2 * δ ≤ 2 * δ₁ := by gcongr
        _ = 1 / (n₁ + 1 : ℝ) := by simp [δ₁] <;> ring
    have h6 : 2 * δ ≤ 1 / (n₂ + 1 : ℝ) := by
      calc 2 * δ ≤ 2 * δ₂ := by gcongr
        _ = 1 / (n₂ + 1 : ℝ) := by simp [δ₂] <;> ring
    have h7 : f x₀ (r₀ - 1 / (n₁ + 1 : ℝ)) ≤ f x₀ (r₀ - 2 * δ) :=
      h_mono x₀ (by linarith)
    have h8 : f x₀ (r₀ + 2 * δ) ≤ f x₀ (r₀ + 1 / (n₂ + 1 : ℝ)) :=
      h_mono x₀ (by linarith)
    have h9 : (f p.1 p.2).toReal - (f x₀ r₀).toReal < ε := by
      have h10 : (f p.1 p.2).toReal ≤ (f x₀ (r₀ + 1 / (n₂ + 1 : ℝ))).toReal := by
        exact ENNReal.toReal_le_toReal (h_finite _ _) (h_finite _ _) |>.mpr (h4.trans h8)
      linarith [hn₂]
    have h11 : (f x₀ r₀).toReal - (f p.1 p.2).toReal < ε := by
      have h12 : (f x₀ (r₀ - 1 / (n₁ + 1 : ℝ))).toReal ≤ (f p.1 p.2).toReal := by
        exact ENNReal.toReal_le_toReal (h_finite _ _) (h_finite _ _) |>.mpr (h7.trans h3)
      linarith [hn₁]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  -- Transfer from real-valued to ENNReal-valued
  have h_main_cont : ∀ (p : Point3 × ℝ), 0 < p.2 →
      ContinuousAt (fun p : Point3 × ℝ => f p.1 p.2) p := by
    intro p hp
    have h1 : ContinuousAt (fun q : Point3 × ℝ => (f q.1 q.2).toReal) p :=
      h_cont_real p.1 p.2 hp
    have h2 : Continuous (fun x : ℝ => ENNReal.ofReal x) := ENNReal.continuous_ofReal
    let h_fn : (Point3 × ℝ) → ℝ := fun q => (f q.1 q.2).toReal
    let g : ℝ → ENNReal := fun x => ENNReal.ofReal x
    have h1' : ContinuousAt h_fn p := h1
    have hg_at : ContinuousAt g (h_fn p) := h2.continuousAt
    have h3 : ContinuousAt (g ∘ h_fn) p := hg_at.comp h1'
    have h_eq : g ∘ h_fn = (fun q : Point3 × ℝ => f q.1 q.2) := by
      funext q
      dsimp only [g, h_fn]
      have h5 : f q.1 q.2 ≠ ⊤ := h_finite q.1 q.2
      exact ENNReal.ofReal_toReal h5
    rw [h_eq] at h3
    exact h3
  have h_final : ContinuousOn (fun p : Point3 × ℝ => f p.1 p.2) {p | 0 < p.2} := by
    intro p hp
    exact (h_main_cont p hp).continuousWithinAt
  exact h_final

end Kakeya.Assouad
