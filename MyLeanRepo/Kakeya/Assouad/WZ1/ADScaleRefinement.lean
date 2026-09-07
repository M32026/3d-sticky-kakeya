import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.CoveringInfrastructure

/-!
# Scale refinement for `IsADSet1`

Transfer an `IsADSet1` bound from a coarser minimum scale to a finer one,
and establish trivial bounds for bounded subsets of `ℝ`.
-/

noncomputable section

open Metric Set

namespace Kakeya.Assouad

lemma real_closedBall_finer_cover
    (c : ℝ) {δ s : ℝ} (hs : 0 < s) (hδ : 0 < δ) (h : s ≤ δ) :
    ∃ centers : Finset ℝ,
      (centers.card : ENNReal) ≤
          (Nat.ceil (2 * δ / s) + 1 : ENNReal) ∧
        Metric.closedBall c δ ⊆
          ⋃ y ∈ centers, Metric.closedBall y s := by
  let M : ℕ := Nat.ceil (2 * δ / s) + 1
  let centers : Finset ℝ :=
    Finset.image
      (fun k : ℕ => c - δ + (k : ℝ) * s)
      (Finset.range M)
  have hM_pos : 0 < M := by positivity
  have h1 : (2 * δ / s : ℝ) < (M : ℝ) := by
    have h2 :
        (Nat.ceil (2 * δ / s) : ℝ) ≥ 2 * δ / s :=
      Nat.le_ceil _
    simp only [M, Nat.cast_add, Nat.cast_one] at *
    linarith
  have hcard :
      centers.card ≤ (Finset.range M).card :=
    Finset.card_image_le
  have hcardM : (Finset.range M).card = M := by simp
  have hcard' :
      (centers.card : ENNReal) ≤ (M : ENNReal) := by
    rw [hcardM] at hcard
    exact_mod_cast hcard
  refine ⟨centers, ?_, ?_⟩
  · simpa [M] using hcard'
  · intro x hx
    have hdist : dist x c ≤ δ := hx
    have habs : |x - c| ≤ δ := by
      simpa [Real.dist_eq] using hdist
    have hx1 : c - δ ≤ x := by
      linarith [abs_le.mp habs]
    have hx2 : x ≤ c + δ := by
      linarith [abs_le.mp habs]
    let t : ℝ := (x - (c - δ)) / s
    have ht0 : 0 ≤ t := by
      apply div_nonneg <;> linarith
    have ht1 : t < (M : ℝ) := by
      have h3 : x - (c - δ) ≤ 2 * δ := by linarith
      have h4 : t ≤ 2 * δ / s := by
        calc
          t = (x - (c - δ)) / s := rfl
          _ ≤ (2 * δ) / s := by gcongr
          _ = 2 * δ / s := by ring
      linarith
    let k : ℕ := Nat.floor t
    have hk1 : (k : ℝ) ≤ t := Nat.floor_le ht0
    have hk2 : t < (k : ℝ) + 1 :=
      Nat.lt_floor_add_one t
    have hkM : k < M := by
      have h5 : (k : ℝ) < (M : ℝ) := by linarith
      exact_mod_cast h5
    have h_ts : t * s = x - (c - δ) := by
      dsimp only [t]
      field_simp [hs.ne']
    have hdist2 :
        |x - (c - δ + (k : ℝ) * s)| ≤ s := by
      have h6 :
          0 ≤ x - (c - δ + (k : ℝ) * s) := by
        have h7 :
            (k : ℝ) * s ≤ x - (c - δ) := by
          have h8 : (k : ℝ) ≤ t := hk1
          have h9 : (k : ℝ) * s ≤ t * s := by gcongr
          rw [h_ts] at h9
          exact h9
        linarith
      have h11 :
          x - (c - δ + (k : ℝ) * s) < s := by
        have h12 :
            x - (c - δ) < ((k : ℝ) + 1) * s := by
          have h13 : t < (k : ℝ) + 1 := hk2
          have h14 :
              t * s < ((k : ℝ) + 1) * s := by
            gcongr
          rw [h_ts] at h14
          exact h14
        linarith
      rw [abs_le]
      constructor <;> linarith
    have hmem :
        c - δ + (k : ℝ) * s ∈ centers := by
      apply Finset.mem_image.mpr
      exact ⟨k, Finset.mem_range.mpr hkM, rfl⟩
    exact
      Set.mem_iUnion₂.mpr
        ⟨c - δ + (k : ℝ) * s, hmem, by
          simpa [Metric.mem_closedBall, Real.dist_eq] using
            hdist2⟩

lemma externalCoveringNumber_refine_real
    {A : Set ℝ} {δ s : ℝ}
    (hs : 0 < s) (hδ : 0 < δ) (h : s ≤ δ) :
    Metric.externalCoveringNumber ⟨s, hs.le⟩ A ≤
      (Nat.ceil (2 * δ / s) + 1 : ENNReal) *
        Metric.externalCoveringNumber ⟨δ, hδ.le⟩ A := by
  by_cases htop :
      Metric.externalCoveringNumber ⟨δ, hδ.le⟩ A = ⊤
  · have h_main :
        (Nat.ceil (2 * δ / s) + 1 : ENNReal) *
            Metric.externalCoveringNumber ⟨δ, hδ.le⟩ A =
          ⊤ := by
      rw [htop]
      simp
    rw [h_main]
    exact le_top
  · have hfin :
        Metric.externalCoveringNumber ⟨δ, hδ.le⟩ A ≠ ⊤ :=
      htop
    obtain
      ⟨centers, hcenters_finite, hcenters_cover,
        hcenters_card⟩ :=
      exists_set_encard_eq_externalCoveringNumber hfin
    let centersFinset : Finset ℝ :=
      hcenters_finite.toFinset
    have hcentersFinset_coe :
        (centersFinset : Set ℝ) = centers := by
      simp [centersFinset, hcenters_finite.coe_toFinset]
    choose refinedCenters hrefined_card hrefined_cover using
      fun c : ℝ =>
        real_closedBall_finer_cover c hs hδ h
    let allCenters : Finset ℝ :=
      centersFinset.biUnion refinedCenters
    have hcover :
        A ⊆ ⋃ y ∈ allCenters, Metric.closedBall y s := by
      intro x hx
      have h1 := hcenters_cover hx
      rcases h1 with ⟨c, hc, hpair⟩
      have hnn :
          nndist x c ≤ (⟨δ, hδ.le⟩ : NNReal) := by
        simpa [Set.mem_setOf_eq] using hpair
      have hdist : dist x c ≤ δ := by
        exact mem_closedBall.mp hnn
      have hxc : x ∈ Metric.closedBall c δ := by
        simpa [Metric.mem_closedBall] using hdist
      have hc' : c ∈ centersFinset := by
        have h : c ∈ (centersFinset : Set ℝ) := by
          rw [hcentersFinset_coe]
          exact hc
        simpa using h
      have h3 :
          x ∈ ⋃ y ∈ refinedCenters c,
            Metric.closedBall y s :=
        hrefined_cover c hxc
      rcases Set.mem_iUnion₂.mp h3 with
        ⟨y, hy, hyball⟩
      have h4 : y ∈ allCenters :=
        Finset.mem_biUnion.mpr ⟨c, hc', hy⟩
      exact Set.mem_iUnion₂.mpr ⟨y, h4, hyball⟩
    have hIsCover :
        Metric.IsCover ⟨s, hs.le⟩ A
          (allCenters : Set ℝ) := by
      intro x hx
      have h :
          x ∈ ⋃ y ∈ allCenters, Metric.closedBall y s :=
        hcover hx
      rcases Set.mem_iUnion₂.mp h with
        ⟨y, hy, hball⟩
      have hdist : dist x y ≤ s := by
        simpa [Metric.mem_closedBall] using hball
      have hnn :
          nndist x y ≤ (⟨s, hs.le⟩ : NNReal) :=
        dist_le_coe.mp hball
      refine ⟨y, hy, ?_⟩
      simpa [Set.mem_setOf_eq] using hnn
    have h_main :
        Metric.externalCoveringNumber ⟨s, hs.le⟩ A ≤
          (allCenters : Set ℝ).encard :=
      hIsCover.externalCoveringNumber_le_encard
    have h_encard_eq :
        (allCenters : Set ℝ).encard = ↑allCenters.card := by
      simp
    have h_main2 :
        (Metric.externalCoveringNumber
              ⟨s, hs.le⟩ A : ENNReal) ≤
          (allCenters.card : ENNReal) := by
      have h4 :
          Metric.externalCoveringNumber ⟨s, hs.le⟩ A ≤
            (allCenters : Set ℝ).encard :=
        h_main
      rw [h_encard_eq] at h4
      exact_mod_cast h4
    have hcard :
        (allCenters.card : ENNReal) ≤
          (centersFinset.card : ENNReal) *
            (Nat.ceil (2 * δ / s) + 1 : ENNReal) := by
      have h1 :
          allCenters.card ≤
            ∑ c ∈ centersFinset,
              (refinedCenters c).card :=
        Finset.card_biUnion_le
      have h2 :
          ∑ c ∈ centersFinset,
              (refinedCenters c).card ≤
            ∑ c ∈ centersFinset,
              (Nat.ceil (2 * δ / s) + 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact_mod_cast hrefined_card i
      have h3 :
          ∑ c ∈ centersFinset,
              (Nat.ceil (2 * δ / s) + 1) =
            centersFinset.card *
              (Nat.ceil (2 * δ / s) + 1) := by
        simp [Finset.sum_const]
      calc
        (allCenters.card : ENNReal)
            ≤ ↑(∑ c ∈ centersFinset,
                (refinedCenters c).card) := by
              exact_mod_cast h1
        _ ≤ ↑(∑ c ∈ centersFinset,
                (Nat.ceil (2 * δ / s) + 1)) := by
              exact_mod_cast h2
        _ =
            (centersFinset.card : ENNReal) *
              (Nat.ceil (2 * δ / s) + 1 : ENNReal) := by
              rw [h3]
              simp
    have h_centers_card :
        (centersFinset.card : ENNReal) =
          Metric.externalCoveringNumber
            ⟨δ, hδ.le⟩ A := by
      have h1 :
          (↑centersFinset.card : ℕ∞) = centers.encard := by
        simpa [centersFinset] using
          hcenters_finite.encard_eq_coe_toFinset_card.symm
      have h2 :
          centers.encard =
            Metric.externalCoveringNumber
              ⟨δ, hδ.le⟩ A :=
        hcenters_card
      have h3 :
          (↑centersFinset.card : ℕ∞) =
            Metric.externalCoveringNumber
              ⟨δ, hδ.le⟩ A := by
        rw [h1, h2]
      exact_mod_cast h3
    calc
      (Metric.externalCoveringNumber
            ⟨s, hs.le⟩ A : ENNReal)
          ≤ (allCenters.card : ENNReal) :=
        h_main2
      _ ≤
          (centersFinset.card : ENNReal) *
            (Nat.ceil (2 * δ / s) + 1 : ENNReal) :=
        hcard
      _ =
          (Metric.externalCoveringNumber
                ⟨δ, hδ.le⟩ A : ENNReal) *
            (Nat.ceil (2 * δ / s) + 1 : ENNReal) := by
        rw [h_centers_card]
      _ =
          (Nat.ceil (2 * δ / s) + 1 : ENNReal) *
            (Metric.externalCoveringNumber
              ⟨δ, hδ.le⟩ A : ENNReal) := by
        rw [mul_comm]

lemma IsADSet1.weaken_scale
    {E : Set ℝ} {δ s α : ℝ} {C : ENNReal}
    (hAD : IsADSet1 E δ α C)
    (hs : 0 < s) (h : s ≤ δ) (hδ1 : δ ≤ 1) :
    IsADSet1 E s α
      (C * ENNReal.ofReal (10 * δ / s)) := by
  rcases hAD with
    ⟨hδ_pos, hα_pos, hα_one, hC_one, hbounded,
      hcover⟩
  let C' : ENNReal :=
    C * ENNReal.ofReal (10 * δ / s)
  have hds_ge_one : 1 ≤ δ / s := by
    calc
      (1 : ℝ) = s / s := by
        field_simp [hs.ne']
      _ ≤ δ / s := by gcongr
  have h10ds_ge_one : 1 ≤ 10 * δ / s := by
    have h4 : 10 * (δ / s) ≥ 10 := by
      calc
        10 * (δ / s) ≥ 10 * (1 : ℝ) := by
          gcongr
        _ = 10 := by norm_num
    have h5 : 10 * δ / s = 10 * (δ / s) := by
      ring
    rw [h5]
    linarith
  have h5 :
      (1 : ENNReal) ≤
        ENNReal.ofReal (10 * δ / s) := by
    have h51 :
        ENNReal.ofReal (1 : ℝ) ≤
          ENNReal.ofReal (10 * δ / s) :=
      ENNReal.ofReal_le_ofReal h10ds_ge_one
    simpa using h51
  have hC'_one : 1 ≤ C' := by
    have h6 :
        C * (1 : ENNReal) ≤
          C * ENNReal.ofReal (10 * δ / s) :=
      mul_le_mul_left' h5 C
    have h7 :
        C ≤ C * ENNReal.ofReal (10 * δ / s) := by
      simpa using h6
    exact hC_one.trans h7
  have hC_le_C' : C ≤ C' := by
    have h6 :
        C * (1 : ENNReal) ≤
          C * ENNReal.ofReal (10 * δ / s) :=
      mul_le_mul_left' h5 C
    simpa using h6
  refine
    ⟨hs, hα_pos, hα_one, hC'_one, hbounded, ?_⟩
  intro t ht_nonneg hs_le_t ht_one x r ht_le_r hr_le_one
  by_cases hδ_le_t : δ ≤ t
  · have h_orig :=
      hcover t ht_nonneg hδ_le_t ht_one x r
        ht_le_r hr_le_one
    exact h_orig.trans
      (mul_le_mul_right' hC_le_C' _)
  · have ht_pos : 0 < t := by linarith
    have h_t_lt_delta : t < δ := by linarith
    by_cases hδ_le_r : δ ≤ r
    · have h_orig :=
        hcover δ hδ_pos.le (by linarith) hδ1 x r
          hδ_le_r hr_le_one
      have h_refine :=
        externalCoveringNumber_refine_real
          (A := E ∩ Metric.closedBall x r)
          ht_pos hδ_pos (by linarith)
      have h_factor_real :
          (Nat.ceil (2 * δ / t) + 1 : ℝ) ≤
            10 * δ / s := by
        have h1 :
            (Nat.ceil (2 * δ / t) : ℝ) <
              2 * δ / t + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        have h2 :
            (Nat.ceil (2 * δ / t) + 1 : ℝ) ≤
              2 * δ / t + 2 := by
          linarith
        have h3 : 2 * δ / t ≤ 2 * δ / s := by
          gcongr
        have h4 : (2 : ℝ) ≤ 2 * δ / s := by
          calc
            (2 : ℝ) = 2 * (1 : ℝ) := by ring
            _ ≤ 2 * (δ / s) := by gcongr
            _ = 2 * δ / s := by ring
        calc
          (Nat.ceil (2 * δ / t) + 1 : ℝ)
              ≤ 2 * δ / t + 2 := h2
          _ ≤ 2 * δ / s + 2 := by gcongr
          _ ≤ 2 * δ / s + 2 * δ / s := by
            gcongr
          _ = 4 * (δ / s) := by ring
          _ ≤ 10 * δ / s := by
            have h5 : 0 < δ / s := by positivity
            have h6 :
                4 * (δ / s) ≤ 10 * (δ / s) :=
              mul_le_mul_of_nonneg_right (by norm_num) h5.le
            have h7 :
                10 * (δ / s) = 10 * δ / s := by ring
            rw [h7] at h6
            exact h6
      have h_factor :
          (Nat.ceil (2 * δ / t) + 1 : ENNReal) ≤
            ENNReal.ofReal (10 * δ / s) := by
        let n : ℕ := Nat.ceil (2 * δ / t) + 1
        have h_real : (n : ℝ) ≤ 10 * δ / s := by
          simpa [n] using h_factor_real
        have h_ennreal :
            ENNReal.ofReal ((n : ℝ)) ≤
              ENNReal.ofReal (10 * δ / s) :=
          ENNReal.ofReal_le_ofReal h_real
        rw [ENNReal.ofReal_natCast] at h_ennreal
        simpa [n] using h_ennreal
      have h9 :
          Kakeya.realRpowENN (r / δ) α ≤
            Kakeya.realRpowENN (r / t) α := by
        simp only [Kakeya.realRpowENN]
        apply ENNReal.ofReal_mono
        have h10 : 0 ≤ r / δ := by
          apply div_nonneg <;> linarith
        have h11 : r / δ ≤ r / t := by
          gcongr <;> linarith
        exact Real.rpow_le_rpow h10 h11 (by linarith)
      calc
        (Metric.externalCoveringNumber
              ⟨t, ht_nonneg⟩
              (E ∩ Metric.closedBall x r) : ENNReal)
            ≤
              (Nat.ceil (2 * δ / t) + 1 : ENNReal) *
                (Metric.externalCoveringNumber
                    ⟨δ, hδ_pos.le⟩
                    (E ∩ Metric.closedBall x r) : ENNReal) :=
          h_refine
        _ ≤
            (Nat.ceil (2 * δ / t) + 1 : ENNReal) *
              (C * Kakeya.realRpowENN (r / δ) α) := by
          gcongr
        _ ≤
            ENNReal.ofReal (10 * δ / s) *
              (C * Kakeya.realRpowENN (r / δ) α) := by
          gcongr
        _ =
            C * ENNReal.ofReal (10 * δ / s) *
              Kakeya.realRpowENN (r / δ) α := by ring
        _ ≤ C' * Kakeya.realRpowENN (r / t) α := by
          gcongr
    · have hr_pos : 0 < r := by linarith
      obtain ⟨D, hD_card, hD_cover⟩ :=
        real_closedBall_finer_cover x ht_pos hr_pos
          (by linarith)
      have hD_cover' :
          E ∩ Metric.closedBall x r ⊆
            ⋃ d ∈ D, Metric.closedBall d t :=
        (Set.inter_subset_right).trans hD_cover
      have hIsCover :
          Metric.IsCover ⟨t, ht_nonneg⟩
            (E ∩ Metric.closedBall x r)
            (D : Set ℝ) := by
        intro a ha
        have h1 :
            a ∈ ⋃ d ∈ D, Metric.closedBall d t :=
          hD_cover' ha
        rcases Set.mem_iUnion₂.mp h1 with
          ⟨d, hd_in, hball⟩
        have hnn :
            nndist a d ≤ (⟨t, ht_nonneg⟩ : NNReal) :=
          dist_le_coe.mp hball
        refine ⟨d, hd_in, ?_⟩
        simpa [Set.mem_setOf_eq] using hnn
      have h1 :
          (Metric.externalCoveringNumber
                ⟨t, ht_nonneg⟩
                (E ∩ Metric.closedBall x r) : ENNReal) ≤
            (D.card : ENNReal) := by
        have h_main :
            Metric.externalCoveringNumber
                ⟨t, ht_nonneg⟩
                (E ∩ Metric.closedBall x r) ≤
              (D : Set ℝ).encard :=
          hIsCover.externalCoveringNumber_le_encard
        have h_eq : (D : Set ℝ).encard = ↑D.card := by
          simp
        rw [h_eq] at h_main
        exact_mod_cast h_main
      have hD_bound_real :
          (D.card : ℝ) ≤ 10 * δ / s := by
        have h3 :
            (D.card : ℝ) ≤
              (Nat.ceil (2 * r / t) + 1 : ℝ) := by
          exact_mod_cast hD_card
        have h4 :
            (Nat.ceil (2 * r / t) : ℝ) <
              2 * r / t + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        have h5 :
            (Nat.ceil (2 * r / t) + 1 : ℝ) ≤
              2 * r / t + 2 := by
          linarith
        have h6 : 2 * r / t ≤ 2 * δ / s := by
          have h7 : r < δ := by linarith
          have h8 : t ≥ s := hs_le_t
          gcongr
        have h9 : (2 : ℝ) ≤ 2 * δ / s := by
          calc
            (2 : ℝ) = 2 * (1 : ℝ) := by ring
            _ ≤ 2 * (δ / s) := by gcongr
            _ = 2 * δ / s := by ring
        calc
          (D.card : ℝ)
              ≤ (Nat.ceil (2 * r / t) + 1 : ℝ) := h3
          _ ≤ 2 * r / t + 2 := h5
          _ ≤ 2 * δ / s + 2 := by gcongr
          _ ≤ 2 * δ / s + 2 * δ / s := by
            gcongr
          _ = 4 * (δ / s) := by ring
          _ ≤ 10 * δ / s := by
            have h10 : 0 < δ / s := by positivity
            have h11 :
                4 * (δ / s) ≤ 10 * (δ / s) :=
              mul_le_mul_of_nonneg_right (by norm_num) h10.le
            have h12 :
                10 * (δ / s) = 10 * δ / s := by ring
            rw [h12] at h11
            exact h11
      have hD_bound' :
          (D.card : ENNReal) ≤
            ENNReal.ofReal (10 * δ / s) := by
        have h :
            ENNReal.ofReal ((D.card : ℝ)) ≤
              ENNReal.ofReal (10 * δ / s) :=
          ENNReal.ofReal_le_ofReal hD_bound_real
        rw [ENNReal.ofReal_natCast] at h
        exact h
      have h10 :
          (1 : ENNReal) ≤
            Kakeya.realRpowENN (r / t) α := by
        simp only [Kakeya.realRpowENN]
        have h11 : 1 ≤ r / t := by
          calc
            (1 : ℝ) = t / t := by
              field_simp [ht_pos.ne']
            _ ≤ r / t := by gcongr
        have h13 :
            (1 : ℝ) ≤ Real.rpow (r / t) α :=
          Real.one_le_rpow h11 (by linarith)
        have h14 :
            ENNReal.ofReal (1 : ℝ) ≤
              ENNReal.ofReal (Real.rpow (r / t) α) :=
          ENNReal.ofReal_le_ofReal h13
        simpa using h14
      calc
        (Metric.externalCoveringNumber
              ⟨t, ht_nonneg⟩
              (E ∩ Metric.closedBall x r) : ENNReal)
            ≤ (D.card : ENNReal) := h1
        _ ≤
            C * ENNReal.ofReal (10 * δ / s) *
              Kakeya.realRpowENN (r / t) α := by
          have h14 :
              (D.card : ENNReal) ≤
                ENNReal.ofReal (10 * δ / s) :=
            hD_bound'
          have h15 :
              ENNReal.ofReal (10 * δ / s) ≤
                C * ENNReal.ofReal (10 * δ / s) := by
            have h16 :
                ENNReal.ofReal (10 * δ / s) *
                    (1 : ENNReal) ≤
                  ENNReal.ofReal (10 * δ / s) * C :=
              mul_le_mul_left' hC_one _
            have h17 :
                ENNReal.ofReal (10 * δ / s) * C =
                  C * ENNReal.ofReal (10 * δ / s) := by
              ring
            rw [h17] at h16
            simpa using h16
          have h16 :
              C * ENNReal.ofReal (10 * δ / s) ≤
                C * ENNReal.ofReal (10 * δ / s) *
                  Kakeya.realRpowENN (r / t) α := by
            have h17 :
                C * ENNReal.ofReal (10 * δ / s) *
                    (1 : ENNReal) ≤
                  C * ENNReal.ofReal (10 * δ / s) *
                    Kakeya.realRpowENN (r / t) α :=
              mul_le_mul_left' h10 _
            simpa using h17
          exact (h14.trans h15).trans h16
        _ = C' * Kakeya.realRpowENN (r / t) α := by
          simp [C', mul_assoc]

lemma IsADSet1.trivial_bound
    {E : Set ℝ} {ρ α : ℝ}
    (hE : E ⊆ Set.Icc (-4 : ℝ) 4)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    IsADSet1 E ρ α (ENNReal.ofReal (10 / ρ)) := by
  have h10ρ_ge_one : 1 ≤ 10 / ρ := by
    have h3 : 10 / ρ ≥ 10 := by
      calc
        10 / ρ ≥ 10 / (1 : ℝ) := by
          gcongr <;> norm_num
        _ = 10 := by norm_num
    linarith
  have hC_one :
      (1 : ENNReal) ≤ ENNReal.ofReal (10 / ρ) := by
    have h51 :
        ENNReal.ofReal (1 : ℝ) ≤
          ENNReal.ofReal (10 / ρ) :=
      ENNReal.ofReal_le_ofReal h10ρ_ge_one
    simpa using h51
  refine ⟨hρ, hα, hα1, hC_one, hE, ?_⟩
  intro s hs_nonneg hρ_le_s hs_le_one x r hs_le_r hr_le_one
  have hs_pos : 0 < s := by linarith
  obtain ⟨D, hD_card, hD_cover⟩ :=
    real_closedBall_finer_cover
      (c := (0 : ℝ)) (δ := (4 : ℝ))
      (s := s) hs_pos (by norm_num) (by linarith)
  have h_sub :
      E ∩ Metric.closedBall x r ⊆
        Metric.closedBall (0 : ℝ) 4 := by
    intro y hy
    have h2 : y ∈ Set.Icc (-4 : ℝ) 4 := hE hy.1
    simpa [Metric.mem_closedBall, Real.dist_eq, abs_le]
      using h2
  have hD_cover' :
      E ∩ Metric.closedBall x r ⊆
        ⋃ d ∈ D, Metric.closedBall d s :=
    h_sub.trans hD_cover
  have hIsCover :
      Metric.IsCover ⟨s, hs_nonneg⟩
        (E ∩ Metric.closedBall x r) (D : Set ℝ) := by
    intro a ha
    have h1 :
        a ∈ ⋃ d ∈ D, Metric.closedBall d s :=
      hD_cover' ha
    rcases Set.mem_iUnion₂.mp h1 with
      ⟨d, hd_in, hball⟩
    have hnn :
        nndist a d ≤ (⟨s, hs_nonneg⟩ : NNReal) :=
      dist_le_coe.mp hball
    refine ⟨d, hd_in, ?_⟩
    simpa [Set.mem_setOf_eq] using hnn
  have h1 :
      (Metric.externalCoveringNumber
            ⟨s, hs_nonneg⟩
            (E ∩ Metric.closedBall x r) : ENNReal) ≤
        (D.card : ENNReal) := by
    have h_main :
        Metric.externalCoveringNumber
            ⟨s, hs_nonneg⟩
            (E ∩ Metric.closedBall x r) ≤
          (D : Set ℝ).encard :=
      hIsCover.externalCoveringNumber_le_encard
    have h_eq : (D : Set ℝ).encard = ↑D.card := by simp
    rw [h_eq] at h_main
    exact_mod_cast h_main
  have hD_bound_real :
      (D.card : ℝ) ≤ 10 / ρ := by
    have h3 :
        (D.card : ℝ) ≤
          (Nat.ceil (8 / s) + 1 : ℝ) := by
      exact_mod_cast hD_card
    have h4 :
        (Nat.ceil (8 / s) : ℝ) < 8 / s + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h5 :
        (Nat.ceil (8 / s) + 1 : ℝ) ≤
          8 / s + 2 := by
      linarith
    have h6 : 8 / s ≤ 8 / ρ := by gcongr
    have h7 : (2 : ℝ) ≤ 2 / ρ := by
      have h9 : 2 / ρ ≥ 2 := by
        calc
          2 / ρ ≥ 2 / (1 : ℝ) := by
            gcongr <;> norm_num
          _ = 2 := by norm_num
      linarith
    calc
      (D.card : ℝ)
          ≤ (Nat.ceil (8 / s) + 1 : ℝ) := h3
      _ ≤ 8 / s + 2 := h5
      _ ≤ 8 / ρ + 2 := by gcongr
      _ ≤ 8 / ρ + 2 / ρ := by gcongr
      _ = 10 / ρ := by ring
  have hD_bound' :
      (D.card : ENNReal) ≤
        ENNReal.ofReal (10 / ρ) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hD_bound_real
  have h10 :
      (1 : ENNReal) ≤
        Kakeya.realRpowENN (r / s) α := by
    simp only [Kakeya.realRpowENN]
    have h11 : 1 ≤ r / s := by
      calc
        (1 : ℝ) = s / s := by
          field_simp [hs_pos.ne']
        _ ≤ r / s := by gcongr
    have h13 :
        (1 : ℝ) ≤ Real.rpow (r / s) α :=
      Real.one_le_rpow h11 (by linarith)
    have h14 :
        ENNReal.ofReal (1 : ℝ) ≤
          ENNReal.ofReal (Real.rpow (r / s) α) :=
      ENNReal.ofReal_le_ofReal h13
    simpa using h14
  calc
    (Metric.externalCoveringNumber
          ⟨s, hs_nonneg⟩
          (E ∩ Metric.closedBall x r) : ENNReal)
        ≤ (D.card : ENNReal) := h1
    _ ≤ ENNReal.ofReal (10 / ρ) := hD_bound'
    _ ≤
        ENNReal.ofReal (10 / ρ) *
          Kakeya.realRpowENN (r / s) α := by
      have h17 :
          ENNReal.ofReal (10 / ρ) * (1 : ENNReal) ≤
            ENNReal.ofReal (10 / ρ) *
              Kakeya.realRpowENN (r / s) α :=
        mul_le_mul_left' h10 _
      simpa using h17

/--
Coarsen the AD scale: if `E` has AD at scale `δ`, it also has AD at any
coarser scale `s ≥ δ` with the same constant. This is trivial because the
definition only quantifies over covering radii `ρ ≥ δ`, and `s ≥ δ`
makes the quantification more restrictive.
-/
lemma IsADSet1.coarsen_scale
    {E : Set ℝ} {δ s α : ℝ} {C : ENNReal}
    (hAD : IsADSet1 E δ α C)
    (hs : 0 < s) (h : δ ≤ s) (hs1 : s ≤ 1) :
    IsADSet1 E s α C := by
  rcases hAD with ⟨hδ_pos, hα_pos, hα_one, hC_one, hbounded, hcover⟩
  refine ⟨hs, hα_pos, hα_one, hC_one, hbounded, ?_⟩
  intro ρ hρ hs_ρ hρ_one x r hρ_r hr_one
  have hδ_ρ : δ ≤ ρ := le_trans h hs_ρ
  exact hcover ρ hρ hδ_ρ hρ_one x r hρ_r hr_one

end Kakeya.Assouad
