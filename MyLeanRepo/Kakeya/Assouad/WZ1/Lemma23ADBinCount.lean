import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ADBinCountStatements

/-!
# Count scalar mesh bins in WZ1 Lemma 23

Cover the bounded AD set by four localized unit-ball covers and observe that
one radius-`rho` real ball meets at most three integer `rho`-mesh bins.
-/

namespace Kakeya.Assouad

private lemma floor_image_ball_le_three
    {rho : ℝ} (hrho_pos : 0 < rho) {c : ℝ}
    {s : Finset ℝ}
    (h : ∀ v ∈ s, |v - c| ≤ rho) :
    (s.image fun v : ℝ => Int.floor (v / rho)).card ≤ 3 := by
  let m : ℤ := Int.floor (c / rho - 1)
  have h1 :
      ∀ v ∈ s,
        Int.floor (v / rho) ∈
          ({m, m + 1, m + 2} : Finset ℤ) := by
    intro v hv
    have h2 : |v - c| ≤ rho := h v hv
    have h21 : c - rho ≤ v := by
      linarith [abs_le.mp h2]
    have h22 : v ≤ c + rho := by
      linarith [abs_le.mp h2]
    have h3 : c / rho - 1 ≤ v / rho := by
      have h4 : c / rho - 1 = (c - rho) / rho := by
        field_simp [hrho_pos.ne']
      rw [h4]
      gcongr
    have h4 : v / rho ≤ c / rho + 1 := by
      have h5 : (c + rho) / rho = c / rho + 1 := by
        field_simp [hrho_pos.ne']
      calc
        v / rho ≤ (c + rho) / rho := by gcongr
        _ = c / rho + 1 := h5
    have h5 : (m : ℝ) ≤ v / rho := by
      have h6 : (m : ℝ) ≤ c / rho - 1 :=
        Int.floor_le (c / rho - 1)
      linarith
    have h61 : v / rho < (m : ℝ) + 3 := by
      have h7 :
          c / rho - 1 < (m : ℝ) + 1 :=
        Int.lt_floor_add_one (c / rho - 1)
      linarith
    have h62 : v / rho < (↑(m + 3) : ℝ) := by
      have h63 : (↑(m + 3) : ℝ) = (m : ℝ) + 3 := by
        simp
      rw [h63]
      exact h61
    have h8 : m ≤ Int.floor (v / rho) :=
      Int.le_floor.mpr h5
    have h9 : Int.floor (v / rho) < m + 3 :=
      Int.floor_lt.mpr h62
    simp only [Finset.mem_insert, Finset.mem_singleton] at *
    omega
  let bins :=
    s.image fun v : ℝ => Int.floor (v / rho)
  have h_sub :
      bins ⊆ ({m, m + 1, m + 2} : Finset ℤ) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨v, hv, rfl⟩
    exact h1 v hv
  exact
    (Finset.card_le_card h_sub).trans
      (by simp)

theorem wz1_lemma23_ad_bin_count :
    WZ1Lemma23ADBinCountStatement := by
  intro rho alpha C E values hAD hrho_le_one hvalues
  rcases hAD with
    ⟨hrho_pos, _halpha_pos, _halpha_le_one,
      _hC_one, hbounded, hcover⟩
  by_cases hC_eq_top : C = ⊤
  · rw [hC_eq_top]
    have hrpow_pos :
        0 < Kakeya.realRpowENN (1 / rho) alpha := by
      apply ENNReal.ofReal_pos.mpr
      apply Real.rpow_pos_of_pos
      positivity
    have h2 :
        (12 : ENNReal) * ⊤ *
            Kakeya.realRpowENN (1 / rho) alpha =
          ⊤ := by
      rw [ENNReal.mul_top (by norm_num)]
      exact ENNReal.top_mul hrpow_pos.ne'
    rw [h2]
    exact le_top
  · have hC_ne_top : C ≠ ⊤ := hC_eq_top
    let rho_nn : NNReal := ⟨rho, hrho_pos.le⟩
    let centers : Finset ℝ := {-3, -1, 1, 3}
    have hrpow_ne_top :
        Kakeya.realRpowENN (1 / rho) alpha ≠ ⊤ := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    have h_mul_ne_top :
        C * Kakeya.realRpowENN (1 / rho) alpha ≠ ⊤ :=
      ENNReal.mul_ne_top hC_ne_top hrpow_ne_top
    have h_main :
        ∀ c : ℝ,
          ∃ S_c : Finset ℝ,
            c ∈ centers →
              Metric.IsCover rho_nn
                (E ∩ Metric.closedBall c 1)
                (S_c : Set ℝ) ∧
              (S_c.card : ENNReal) ≤
                C * Kakeya.realRpowENN (1 / rho) alpha := by
      intro c
      by_cases hc : c ∈ centers
      · have h1 :
            (↑(Metric.externalCoveringNumber rho_nn
              (E ∩ Metric.closedBall c 1)) : ENNReal) ≤
              C * Kakeya.realRpowENN (1 / rho) alpha :=
          hcover rho hrho_pos.le le_rfl hrho_le_one
            c 1 hrho_le_one le_rfl
        have h_fin :
            Metric.externalCoveringNumber rho_nn
              (E ∩ Metric.closedBall c 1) ≠ ⊤ := by
          intro htop
          rw [htop] at h1
          exact h_mul_ne_top (top_le_iff.mp h1)
        rcases
            exists_finset_cover_of_externalCoveringNumber h_fin with
          ⟨S_c, hS_cover, hS_card⟩
        have h_eq :
            (S_c.card : ENNReal) =
              (↑(Metric.externalCoveringNumber rho_nn
                (E ∩ Metric.closedBall c 1)) : ENNReal) := by
          exact_mod_cast hS_card
        exact
          ⟨S_c, fun _ =>
            ⟨hS_cover, by rw [h_eq]; exact h1⟩⟩
      · exact ⟨∅, fun h => False.elim (hc h)⟩
    choose S_c hS_c using h_main
    let S : Finset ℝ := centers.biUnion S_c
    have hS_cover :
        ∀ c ∈ centers,
          Metric.IsCover rho_nn
            (E ∩ Metric.closedBall c 1)
            (S_c c : Set ℝ) :=
      fun c hc => (hS_c c hc).1
    have hS_card_bound :
        ∀ c ∈ centers,
          ((S_c c).card : ENNReal) ≤
            C * Kakeya.realRpowENN (1 / rho) alpha :=
      fun c hc => (hS_c c hc).2
    have hS_cover_values :
        ∀ v ∈ values, ∃ c ∈ S, |v - c| ≤ rho := by
      intro v hv
      have hvE : v ∈ E := hvalues (Finset.mem_coe.mp hv)
      have hv4 : v ∈ Set.Icc (-4) 4 := hbounded hvE
      have h_process :
          ∀ c : ℝ, c ∈ centers →
            v ∈ Metric.closedBall c 1 →
              ∃ y ∈ S, |v - y| ≤ rho := by
        intro c hc hball
        have hEball :
            v ∈ E ∩ Metric.closedBall c 1 :=
          ⟨hvE, hball⟩
        have hcover' :=
          hS_cover c hc
        rw [Metric.isCover_iff_subset_iUnion_closedBall] at hcover'
        have h4 :=
          hcover' hEball
        rcases Set.mem_iUnion₂.mp h4 with ⟨y, hy, hball2⟩
        have hball2' : dist v y ≤ rho :=
          Metric.mem_closedBall.mp hball2
        have h6 : |v - y| ≤ rho := by
          rwa [Real.dist_eq] at hball2'
        exact
          ⟨y, Finset.mem_biUnion.mpr ⟨c, hc, hy⟩, h6⟩
      rcases hv4 with ⟨hleft, hright⟩
      by_cases h : v ≤ -2
      · exact h_process (-3) (by simp [centers])
          (by
            rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
            constructor <;> linarith)
      · by_cases h2 : v ≤ 0
        · exact h_process (-1) (by simp [centers])
            (by
              rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
              constructor <;> linarith)
        · by_cases h3 : v ≤ 2
          · exact h_process 1 (by simp [centers])
              (by
                rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
                constructor <;> linarith)
          · exact h_process 3 (by simp [centers])
              (by
                rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
                constructor <;> linarith)
    let binSet := wz1Lemma23ScalarBins rho values
    let binsPerCenter (c : ℝ) : Finset ℤ :=
      Finset.image (fun v : ℝ => Int.floor (v / rho))
        (values.filter fun v => |v - c| ≤ rho)
    have h_bin_per_center :
        ∀ c : ℝ, (binsPerCenter c).card ≤ 3 := by
      intro c
      exact floor_image_ball_le_three hrho_pos
        (fun v hv => (Finset.mem_filter.mp hv).2)
    have h_bin_union :
        binSet ⊆ S.biUnion binsPerCenter := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨v, hv, rfl⟩
      rcases hS_cover_values v hv with ⟨c, hc, hdist⟩
      exact Finset.mem_biUnion.mpr
        ⟨c, hc, Finset.mem_image.mpr
          ⟨v, Finset.mem_filter.mpr ⟨hv, hdist⟩, rfl⟩⟩
    have h_final5 : binSet.card ≤ 3 * S.card := by
      calc
        binSet.card ≤ (S.biUnion binsPerCenter).card :=
          Finset.card_le_card h_bin_union
        _ ≤ ∑ c ∈ S, (binsPerCenter c).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _c ∈ S, 3 :=
          Finset.sum_le_sum
            (fun c _ => h_bin_per_center c)
        _ = 3 * S.card := by simp [mul_comm]
    have hS_card_bound :
        (S.card : ENNReal) ≤
          4 * C * Kakeya.realRpowENN (1 / rho) alpha := by
      have h1 :
          S.card ≤ ∑ c ∈ centers, (S_c c).card :=
        Finset.card_biUnion_le
      have h2 :
          (S.card : ENNReal) ≤
            ∑ c ∈ centers, ((S_c c).card : ENNReal) := by
        exact_mod_cast h1
      calc
        (S.card : ENNReal) ≤
            ∑ c ∈ centers, ((S_c c).card : ENNReal) := h2
        _ ≤ ∑ _c ∈ centers,
            (C * Kakeya.realRpowENN (1 / rho) alpha) :=
          Finset.sum_le_sum hS_card_bound
        _ = 4 * C *
            Kakeya.realRpowENN (1 / rho) alpha := by
          norm_num [centers]
          ring
    have h6 :
        (binSet.card : ENNReal) ≤
          3 * (S.card : ENNReal) := by
      exact_mod_cast h_final5
    calc
      (binSet.card : ENNReal) ≤
          3 * (S.card : ENNReal) := h6
      _ ≤ 3 * (4 * C *
          Kakeya.realRpowENN (1 / rho) alpha) := by
        gcongr
      _ = 12 * C *
          Kakeya.realRpowENN (1 / rho) alpha := by
        ring

end Kakeya.Assouad
