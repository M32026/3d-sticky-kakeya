import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedADBinCountStatements

/-!
# Localized scalar-bin count for WZ1 Lemma 23

Apply the local covering clause of `IsADSet1` inside one radius-`R` ball.
Each radius-`rho` real ball meets at most three integer `rho`-mesh bins.
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

theorem wz1_lemma23_localized_ad_bin_count :
    WZ1Lemma23LocalizedADBinCountStatement := by
  intro rho R alpha C E values center hAD hrho_R hR_one hsubset
  rcases hAD with
    ⟨hrho_pos, _halpha_pos, _halpha_le_one,
      _hC_one, _hbounded, hcover⟩
  by_cases hC_eq_top : C = ⊤
  · rw [hC_eq_top]
    have hrpow_pos :
        0 < Kakeya.realRpowENN (R / rho) alpha := by
      apply ENNReal.ofReal_pos.mpr
      apply Real.rpow_pos_of_pos
      have hR_pos : 0 < R := by
        linarith
      positivity
    have h2 :
        (3 : ENNReal) * ⊤ *
            Kakeya.realRpowENN (R / rho) alpha =
          ⊤ := by
      rw [ENNReal.mul_top (by norm_num)]
      exact ENNReal.top_mul hrpow_pos.ne'
    rw [h2]
    exact le_top
  · have hC_ne_top : C ≠ ⊤ := hC_eq_top
    let rho_nn : NNReal := ⟨rho, hrho_pos.le⟩
    have hrpow_ne_top :
        Kakeya.realRpowENN (R / rho) alpha ≠ ⊤ := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    have h_mul_ne_top :
        C * Kakeya.realRpowENN (R / rho) alpha ≠ ⊤ :=
      ENNReal.mul_ne_top hC_ne_top hrpow_ne_top
    have hcover_bound :
        (↑(Metric.externalCoveringNumber rho_nn
          (E ∩ Metric.closedBall center R)) : ENNReal) ≤
            C * Kakeya.realRpowENN (R / rho) alpha :=
      hcover rho hrho_pos.le le_rfl (by linarith)
        center R hrho_R hR_one
    have hfinite :
        Metric.externalCoveringNumber rho_nn
          (E ∩ Metric.closedBall center R) ≠ ⊤ := by
      intro htop
      rw [htop] at hcover_bound
      exact h_mul_ne_top (top_le_iff.mp hcover_bound)
    rcases
        exists_finset_cover_of_externalCoveringNumber hfinite with
      ⟨centers, hcenters_cover, hcenters_card⟩
    have hcenters_card_eq :
        (centers.card : ENNReal) =
          (↑(Metric.externalCoveringNumber rho_nn
            (E ∩ Metric.closedBall center R)) : ENNReal) := by
      exact_mod_cast hcenters_card
    have hcenters_card_bound :
        (centers.card : ENNReal) ≤
          C * Kakeya.realRpowENN (R / rho) alpha := by
      rw [hcenters_card_eq]
      exact hcover_bound
    have hcenters_cover_values :
        ∀ v ∈ values, ∃ c ∈ centers, |v - c| ≤ rho := by
      intro v hv
      have hv_local :
          v ∈ E ∩ Metric.closedBall center R :=
        hsubset (Finset.mem_coe.mp hv)
      rw [Metric.isCover_iff_subset_iUnion_closedBall] at hcenters_cover
      have hv_cover := hcenters_cover hv_local
      rcases Set.mem_iUnion₂.mp hv_cover with
        ⟨c, hc, hball⟩
      have hdist : dist v c ≤ rho :=
        Metric.mem_closedBall.mp hball
      exact ⟨c, hc, by rwa [Real.dist_eq] at hdist⟩
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
        binSet ⊆ centers.biUnion binsPerCenter := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨v, hv, rfl⟩
      rcases hcenters_cover_values v hv with
        ⟨c, hc, hdist⟩
      exact Finset.mem_biUnion.mpr
        ⟨c, hc, Finset.mem_image.mpr
          ⟨v, Finset.mem_filter.mpr ⟨hv, hdist⟩, rfl⟩⟩
    have h_bin_card :
        binSet.card ≤ 3 * centers.card := by
      calc
        binSet.card ≤
            (centers.biUnion binsPerCenter).card :=
          Finset.card_le_card h_bin_union
        _ ≤ ∑ c ∈ centers, (binsPerCenter c).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _c ∈ centers, 3 :=
          Finset.sum_le_sum
            (fun c _ => h_bin_per_center c)
        _ = 3 * centers.card := by simp [mul_comm]
    have h_bin_card_enn :
        (binSet.card : ENNReal) ≤
          3 * (centers.card : ENNReal) := by
      exact_mod_cast h_bin_card
    calc
      (binSet.card : ENNReal) ≤
          3 * (centers.card : ENNReal) :=
        h_bin_card_enn
      _ ≤ 3 *
          (C * Kakeya.realRpowENN (R / rho) alpha) := by
        gcongr
      _ = 3 * C *
          Kakeya.realRpowENN (R / rho) alpha := by
        ring

end Kakeya.Assouad
