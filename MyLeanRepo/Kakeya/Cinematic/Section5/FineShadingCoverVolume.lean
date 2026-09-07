import MyLeanRepo.Kakeya.Cinematic.Section5.FineShadingCoverVolumeInputs

/-!
# Fine-shading cover and volume assembly
-/

open MeasureTheory

namespace Kakeya.Cinematic

theorem fine_shading_cover_volume :
    FineShadingCoverVolumeStatement := by
  intro hCentered hShading hMaximal hCount hComparable hTransitivity
  intro K D T C_R₀ hK hD hT hC_R₀_pos

  rcases hShading hComparable hTransitivity K D hK hD with
    ⟨C_s, hCs_100, hShading_prop⟩

  let C_R : ℝ := max C_R₀ (max 100 (C_s * (96 * K)^2))
  have hC_R₀_le : C_R₀ ≤ C_R := le_max_left _ _
  have h100_le_C_R : 100 ≤ C_R := by
    have h : 100 ≤ max 100 (C_s * (96 * K)^2) := le_max_left _ _
    exact le_trans h (le_max_right _ _)
  have hC_R_pos : 0 < C_R := by linarith
  have hCs_le_C_R : C_s ≤ C_R := by
    have h1 : 1 ≤ (96 * K)^2 := by
      have h2 : 1 ≤ 96 * K := by linarith
      nlinarith
    have h3 : C_s ≤ C_s * (96 * K)^2 := by
      have h4 : 0 ≤ C_s := by linarith
      nlinarith
    have h5 : C_s * (96 * K)^2 ≤ max 100 (C_s * (96 * K)^2) :=
      le_max_right _ _
    have h6 : max 100 (C_s * (96 * K)^2) ≤ C_R := le_max_right _ _
    linarith
  have hCs_pos : 0 < C_s := by linarith

  rcases hCount D hD with ⟨C, hC_pos, hCount_prop⟩
  let T_count : ℝ := C_R * T ^ 2
  have hT_count : 1 ≤ T_count := by
    have hT_sq : 1 ≤ T ^ 2 := by nlinarith
    dsimp only [T_count]
    nlinarith
  rcases hCount_prop K T_count hK hT_count with
    ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, hCount_delta⟩

  let C_volume : ℝ := C_s * Real.sqrt C_s
  have hC_volume_ge_100 : 100 ≤ C_volume := by
    dsimp only [C_volume]
    have h1 : 0 ≤ C_s := by linarith
    have h2 : Real.sqrt C_s ≥ 10 := by
      have h3 : Real.sqrt C_s ≥ Real.sqrt 100 :=
        Real.sqrt_le_sqrt (by linarith)
      have h4 : Real.sqrt 100 = 10 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      linarith
    nlinarith

  refine ⟨C_R, C, C_s, C_volume, hC_R₀_le, h100_le_C_R,
    hC_pos, hCs_100, hC_volume_ge_100, delta₀, hdelta₀_pos,
    hdelta₀_le_one, ?_⟩
  intro family E₂ delta t Delta hfamily hE₂_nonempty hdelta
    hdelta_le_delta₀ hdelta_le_Delta hDelta_le_t ht_le_T data₀

  have ht_pos : 0 < t := by linarith
  have hDelta_pos : 0 < Delta := by linarith
  rcases fine_assignment_enlarge_C_R data₀ hdelta ht_pos hDelta_pos
      hC_R₀_pos hC_R_pos hC_R₀_le with
    ⟨data, hinterval, hcenter, hfiber⟩

  let tFine : ℝ := C_R * t * Delta / delta
  have h_tFine_pos : 0 < tFine := by positivity
  have h_delta2_le_tDelta : delta^2 ≤ t * Delta := by nlinarith
  have h1_le_C_R : 1 ≤ C_R := by linarith

  have h_admissible_Cs : IsAdmissibleComparisonScale delta tFine C_s := by
    constructor
    · linarith
    · dsimp only [tFine]
      have h : C_s * delta^2 ≤ C_R * t * Delta := by
        have h2 : C_s * delta^2 ≤ C_R * delta^2 := by
          gcongr
          <;> linarith
        nlinarith
      have h3 : (C_s * delta^2) / delta ≤ (C_R * t * Delta) / delta :=
        div_le_div_of_nonneg_right h hdelta.le
      have h4 : (C_s * delta^2) / delta = C_s * delta := by
        field_simp [hdelta.ne'] <;> ring
      rw [h4] at h3
      exact h3

  have h_admissible_100 : IsAdmissibleComparisonScale delta tFine 100 := by
    constructor
    · norm_num
    · dsimp only [tFine]
      have h : 100 * delta^2 ≤ C_R * t * Delta := by
        have h2 : 100 * delta^2 ≤ C_R * delta^2 := by
          gcongr
          <;> linarith
        nlinarith
      have h3 : (100 * delta^2) / delta ≤ (C_R * t * Delta) / delta :=
        div_le_div_of_nonneg_right h hdelta.le
      have h4 : (100 * delta^2) / delta = 100 * delta := by
        field_simp [hdelta.ne'] <;> ring
      rw [h4] at h3
      exact h3

  have h_delta_le_tFine : delta ≤ tFine := by
    dsimp only [tFine]
    have h_pos_td : 0 ≤ t * Delta := by positivity
    have h : delta^2 ≤ C_R * t * Delta := by
      have h2 : delta^2 ≤ t * Delta := h_delta2_le_tDelta
      have h3 : t * Delta ≤ C_R * t * Delta := by
        have h4 : 0 ≤ t * Delta := h_pos_td
        nlinarith
      nlinarith
    have h4 : delta^2 / delta ≤ (C_R * t * Delta) / delta :=
      div_le_div_of_nonneg_right h hdelta.le
    have h5 : delta^2 / delta = delta := by
      field_simp [hdelta.ne'] <;> ring
    rw [h5] at h4
    exact h4

  have h_tFine_le : tFine ≤ T_count / delta := by
    dsimp only [tFine]
    have h_tDelta : t * Delta ≤ T ^ 2 := by
      have h1 : t * Delta ≤ t ^ 2 := by
        nlinarith
      have h2 : t ^ 2 ≤ T ^ 2 := by
        nlinarith
      exact h1.trans h2
    have h2 : C_R * t * Delta ≤ T_count := by
      dsimp only [T_count]
      nlinarith
    exact div_le_div_of_nonneg_right h2 hdelta.le

  have h_buffer_Cs :
      Real.sqrt (C_s * delta / tFine) ≤ data.interval.length / 8 := by
    have h1 : C_s * delta / tFine ≤ C_s / C_R := by
      dsimp only [tFine]
      have h2 : C_s * delta / (C_R * t * Delta / delta) =
          C_s * delta^2 / (C_R * t * Delta) := by
        field_simp [hdelta.ne'] <;> ring
      rw [h2]
      have h_pos_td : 0 < t * Delta := by positivity
      have h3 : C_s * delta^2 / (C_R * t * Delta) =
          (C_s / C_R) * (delta^2 / (t * Delta)) := by
        field_simp [hC_R_pos.ne', h_pos_td.ne'] <;> ring
      rw [h3]
      have h4 : delta^2 / (t * Delta) ≤ 1 := by
        apply (div_le_one h_pos_td).mpr
        nlinarith
      have h5 : 0 ≤ C_s / C_R := by positivity
      nlinarith
    have h5 :
        Real.sqrt (C_s * delta / tFine) ≤ Real.sqrt (C_s / C_R) :=
      Real.sqrt_le_sqrt h1
    have h6 : C_s / C_R ≤ 1 / (96 * K)^2 := by
      have h7 : C_R ≥ C_s * (96 * K)^2 := by
        have h8 : C_s * (96 * K)^2 ≤ max 100 (C_s * (96 * K)^2) :=
          le_max_right _ _
        have h9 : max 100 (C_s * (96 * K)^2) ≤ C_R :=
          le_max_right _ _
        linarith
      calc
        C_s / C_R ≤ C_s / (C_s * (96 * K)^2) := by gcongr
        _ = 1 / (96 * K)^2 := by
          field_simp [hCs_pos.ne'] <;> ring
    have h10 : Real.sqrt (C_s / C_R) ≤ Real.sqrt (1 / (96 * K)^2) :=
      Real.sqrt_le_sqrt h6
    have h11 : Real.sqrt (1 / (96 * K)^2) = 1 / (96 * K) := by
      have h12 : 0 < 96 * K := by linarith
      have h13 : 0 < 1 / (96 * K) := by positivity
      have h14 : (1 / (96 * K)) ^ 2 = 1 / (96 * K)^2 := by
        field_simp [h12.ne'] <;> ring
      rw [← h14]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos h13]
    rw [h11] at h10
    have h14 : (12 * K)⁻¹ ≤ data.interval.length :=
      data.intervalControlled.1
    have h15 : 1 / (96 * K) ≤ data.interval.length / 8 := by
      have h16 : 1 / (96 * K) = (12 * K)⁻¹ / 8 := by
        field_simp <;> ring
      rw [h16]
      linarith
    linarith

  have h_buffer_100 :
      Real.sqrt (100 * delta / tFine) ≤ data.interval.length / 8 := by
    have h1 : 100 * delta / tFine ≤ C_s * delta / tFine := by
      gcongr <;> linarith
    have h2 :
        Real.sqrt (100 * delta / tFine) ≤
          Real.sqrt (C_s * delta / tFine) :=
      Real.sqrt_le_sqrt h1
    linarith [h_buffer_Cs]

  have h_self_comp : ∀ (Q : CurvilinearRectangle delta tFine),
      Q.function ∈ family →
      Q.IsOverCentralQuarterOf data.interval →
      Q.AreLambdaComparable Q family 100 := by
    intro Q hQ_func hQ_central
    rcases hCentered hdelta h_tFine_pos (by norm_num) Q hQ_func
        hQ_central h_buffer_100 with
      ⟨U, hU_func, hU_mid, hU_carrier, hU_family⟩
    refine ⟨U, hU_family, ?_⟩
    simpa using hU_carrier

  let N : ℕ := Nat.ceil (Real.rpow delta (-C))
  have hbound : ∀ (S : RectangleFamily delta tFine),
      (∃ source : Fin S.card → E₂,
        ∀ i, S.rectangle i = data.rectangle (source i)) →
      S.IsPairwiseIncomparable family 100 →
      S.card ≤ N := by
    intro S hsource hincomp
    rcases hsource with ⟨source, hsource_eq⟩
    have hS_centers : S.CentersIn family := by
      intro i
      have h :
          (S.rectangle i).function =
            (data.rectangle (source i)).function := by
        rw [hsource_eq i]
      rw [h]
      have h2 :
          (data.rectangle (source i)).function = data.center (source i) :=
        data.rectangle_function (source i)
      rw [h2]
      exact data.center_mem (source i)
    have hS_central : S.IsOverCentralQuarterOf data.interval := by
      intro i
      rw [hsource_eq i]
      exact data.rectangle_central (source i)
    have hI_short : data.interval.IsShort K := data.intervalControlled.2
    have hcount : (S.card : ℝ) ≤ Real.rpow delta (-C) :=
      hCount_delta delta hdelta hdelta_le_delta₀ tFine 100
        h_delta_le_tFine h_tFine_le (by norm_num) h_admissible_100
        family hfamily data.interval hI_short S hS_centers hS_central hincomp
    have hceil : (S.card : ℝ) ≤ ↑N := by
      dsimp only [N]
      exact le_trans hcount (Nat.le_ceil _)
    exact_mod_cast hceil

  rcases hMaximal hE₂_nonempty data N hbound with
    ⟨R, source, hR_nonempty, hR_source, hR_centers, hR_central,
      hR_incomp, hR_maximal⟩

  have hR_card_count :
      (R.card : ℝ) ≤ Real.rpow delta (-C) := by
    apply hCount_delta delta hdelta hdelta_le_delta₀ tFine 100
      h_delta_le_tFine h_tFine_le (by norm_num) h_admissible_100
      family hfamily data.interval data.intervalControlled.2
      R hR_centers hR_central hR_incomp

  have h_cover :
      E₂ ⊆ ⋃ i : Fin R.card, fineOuterShading data C_s (R.rectangle i) := by
    intro p hp
    let p' : E₂ := ⟨p, hp⟩
    rcases hR_maximal p' with ⟨i, h_eq_or_comp⟩
    have h_comp :
        (R.rectangle i).AreLambdaComparable
          (data.rectangle p') family 100 := by
      cases h_eq_or_comp with
      | inl h_eq =>
        have h_self :
            (R.rectangle i).AreLambdaComparable
              (R.rectangle i) family 100 :=
          h_self_comp (R.rectangle i) (hR_centers i) (hR_central i)
        rw [h_eq] at *
        <;> exact h_self
      | inr h_comp' =>
        rcases h_comp' with ⟨U, hU_family, hsubset⟩
        refine ⟨U, hU_family, ?_⟩
        rw [Set.union_comm]
        exact hsubset
    have h_func_p' : (data.rectangle p').function ∈ family := by
      rw [data.rectangle_function p']
      exact data.center_mem p'
    have h_self_p :
        (data.rectangle p').AreLambdaComparable
          (data.rectangle p') family 100 :=
      h_self_comp (data.rectangle p') h_func_p'
        (data.rectangle_central p')
    have h_point_mem : data.point p' ∈ (data.rectangle p').carrier :=
      data.point_mem_rectangle p'
    have h_inner : p ∈ fineInnerShading data (data.rectangle p') := by
      simp only [fineInnerShading, Set.mem_setOf_eq]
      refine ⟨hp, ?_⟩
      simpa [p'] using ⟨h_self_p, h_point_mem⟩
    have h_mid_R :
        |(R.rectangle i).interval.midpoint - data.interval.midpoint| ≤
          data.interval.length / 16 := by
      have h :
          (R.rectangle i).interval.midpoint =
            (data.rectangle (source i)).interval.midpoint := by
        rw [hR_source i]
      rw [h]
      exact data.rectangle_midpoint_central (source i)
    have h_mid_R' :
        |(data.rectangle p').interval.midpoint - data.interval.midpoint| ≤
          data.interval.length / 16 :=
      data.rectangle_midpoint_central p'
    have h_shading_incl :
        fineInnerShading data (data.rectangle p') ⊆
          fineOuterShading data C_s (R.rectangle i) :=
      hShading_prop hfamily hdelta hdelta_le_Delta hDelta_le_t ht_pos
        hC_R_pos h_admissible_Cs data h_buffer_Cs
        (R.rectangle i) (data.rectangle p')
        (hR_centers i) h_func_p'
        (hR_central i) (data.rectangle_central p')
        h_mid_R h_mid_R' h_comp
    have h_outer : p ∈ fineOuterShading data C_s (R.rectangle i) :=
      h_shading_incl h_inner
    exact Set.subset_iUnion
      (fun i => fineOuterShading data C_s (R.rectangle i)) i h_outer

  have h_enlarged :
      ∀ (i : Fin R.card),
        ∃ U : CurvilinearRectangle (C_s * delta) tFine,
          U.function = (R.rectangle i).function ∧
          U.interval.midpoint = (R.rectangle i).interval.midpoint := by
    intro i
    rcases hCentered hdelta h_tFine_pos (by linarith)
        (R.rectangle i) (hR_centers i) (hR_central i) h_buffer_Cs with
      ⟨U, hU_func, hU_mid, _, _⟩
    exact ⟨U, hU_func, hU_mid⟩

  classical
  choose U_enlarged hU_function hU_midpoint using h_enlarged

  have h_realCarrier_cover :
      E₂ ⊆ ⋃ i : Fin R.card, (U_enlarged i).realCarrier := by
    intro p hp
    rcases Set.mem_iUnion.mp (h_cover hp) with ⟨i, hi⟩
    exact Set.subset_iUnion
      (fun i : Fin R.card => (U_enlarged i).realCarrier) i
      (fineOuterShading_subset_realCarrier data (R.rectangle i)
        (U_enlarged i) (hU_function i) (hU_midpoint i) hi)

  have h_volume_union :
      volume
          (⋃ i : Fin R.card,
            fineOuterShading data C_s (R.rectangle i)) ≤
        (R.card : ENNReal) *
          ENNReal.ofReal
            (2 * C_s * delta *
              Real.sqrt (C_s * delta / tFine)) :=
    fineOuterShading_union_volume_le hdelta (by linarith) data R
      U_enlarged hU_function hU_midpoint

  have h_algebra :
      2 * C_s * delta * Real.sqrt (C_s * delta / tFine) =
        2 * C_volume * delta^2 / Real.sqrt (C_R * t * Delta) := by
    dsimp only [tFine, C_volume]
    have h_pos_prod : 0 < C_R * t * Delta := by positivity
    have h1 : C_s * delta / (C_R * t * Delta / delta) =
        C_s * delta^2 / (C_R * t * Delta) := by
      field_simp [hdelta.ne'] <;> ring
    rw [h1]
    have h2 :
        Real.sqrt (C_s * delta^2 / (C_R * t * Delta)) =
          delta * Real.sqrt (C_s / (C_R * t * Delta)) := by
      have h3 :
          Real.sqrt (C_s * delta^2 / (C_R * t * Delta)) =
            Real.sqrt (delta^2) *
              Real.sqrt (C_s / (C_R * t * Delta)) := by
        rw [← Real.sqrt_mul] <;> ring_nf <;> positivity
      rw [h3]
      have h4 : Real.sqrt (delta^2) = delta := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hdelta]
      rw [h4] <;> ring
    rw [h2]
    have h5 :
        Real.sqrt (C_s / (C_R * t * Delta)) =
          Real.sqrt C_s / Real.sqrt (C_R * t * Delta) := by
      rw [Real.sqrt_div (by positivity)]
    rw [h5] <;> ring

  have h_volume_final :
      volume
          (⋃ i : Fin R.card,
            fineOuterShading data C_s (R.rectangle i)) ≤
        (R.card : ENNReal) *
          ENNReal.ofReal
            (2 * C_volume * delta^2 /
              Real.sqrt (C_R * t * Delta)) := by
    rw [h_algebra] at h_volume_union
    exact h_volume_union

  have h_volume_E2 :
      volume E₂ ≤
        (R.card : ENNReal) *
          ENNReal.ofReal
            (2 * C_volume * delta^2 /
              Real.sqrt (C_R * t * Delta)) := by
    calc
      volume E₂ ≤
          volume
            (⋃ i : Fin R.card,
              fineOuterShading data C_s (R.rectangle i)) :=
        measure_mono h_cover
      _ ≤
          (R.card : ENNReal) *
            ENNReal.ofReal
              (2 * C_volume * delta^2 /
                Real.sqrt (C_R * t * Delta)) :=
        h_volume_final

  exact ⟨data, hinterval, hcenter, hfiber, R, source, hR_nonempty, hR_source,
    hR_centers, hR_central, hR_incomp, hR_card_count, U_enlarged,
    hU_function, hU_midpoint, h_realCarrier_cover, h_volume_E2⟩

end Kakeya.Cinematic
