import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.LargeSlope.ADThickening
import Mathlib.Topology.MetricSpace.CoveringNumbers

noncomputable section

open Metric Set

namespace Kakeya.Assouad

private lemma rpow_three_factor {length ρ D α : ℝ} (hρ : 0 < ρ) (hD : 0 ≤ D)
    (hα_pos : 0 < α) (hα_one : α ≤ 1) (h_expand : length + 2 * D ≤ 3 * length) :
    Kakeya.realRpowENN ((length + 2 * D) / ρ) α ≤
      (3 : ENNReal) * Kakeya.realRpowENN (length / ρ) α := by
  have h_length_nonneg : 0 ≤ length := by linarith
  set x := (length + 2 * D) / ρ with hx_def
  set y := length / ρ with hy_def
  have hx_nonneg : 0 ≤ x := div_nonneg (by linarith) hρ.le
  have hy_nonneg : 0 ≤ y := div_nonneg h_length_nonneg hρ.le
  have hxy : x ≤ 3 * y := by
    dsimp only [x, y]
    have h : (length + 2 * D) / ρ ≤ (3 * length) / ρ :=
      div_le_div_of_nonneg_right (by linarith) hρ.le
    have h2 : (3 * length) / ρ = 3 * (length / ρ) := by ring
    rw [h2] at h
    exact h
  have h1 : Real.rpow x α ≤ Real.rpow (3 * y) α := Real.rpow_le_rpow hx_nonneg hxy hα_pos.le
  have h2 : Real.rpow (3 * y) α = Real.rpow 3 α * Real.rpow y α :=
    Real.mul_rpow (show (0 : ℝ) ≤ 3 by norm_num) hy_nonneg
  have h3 : Real.rpow 3 α ≤ 3 := by
    have h4 : Real.rpow 3 α ≤ Real.rpow 3 1 := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα_one
    have h5 : Real.rpow 3 1 = 3 := by norm_num
    rw [h5] at h4; exact h4
  dsimp only [Kakeya.realRpowENN]
  have h6 : ENNReal.ofReal (Real.rpow x α) ≤
      ENNReal.ofReal (Real.rpow 3 α) * ENNReal.ofReal (Real.rpow y α) := by
    calc ENNReal.ofReal (Real.rpow x α)
        ≤ ENNReal.ofReal (Real.rpow (3 * y) α) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (Real.rpow 3 α * Real.rpow y α) := by rw [h2]
      _ = ENNReal.ofReal (Real.rpow 3 α) * ENNReal.ofReal (Real.rpow y α) :=
        ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) α)
  have h8 : ENNReal.ofReal (Real.rpow 3 α) ≤ (3 : ENNReal) := by
    have h81 : ENNReal.ofReal (Real.rpow 3 α) ≤ ENNReal.ofReal 3 := ENNReal.ofReal_le_ofReal h3
    have h82 : ENNReal.ofReal 3 = (3 : ENNReal) := by norm_num
    rw [h82] at h81
    exact h81
  have h9 : 0 ≤ ENNReal.ofReal (Real.rpow y α) := by positivity
  exact le_trans h6 (mul_le_mul_of_nonneg_right h8 h9)

private lemma rpow_five_factor {length ρ D α : ℝ} (hρ : 0 < ρ) (hD : 0 ≤ D)
    (hα_pos : 0 < α) (hα_one : α ≤ 1) (h_expand : length + 2 * D ≤ 5 * length) :
    Kakeya.realRpowENN ((length + 2 * D) / ρ) α ≤
      (5 : ENNReal) * Kakeya.realRpowENN (length / ρ) α := by
  have h_length_nonneg : 0 ≤ length := by linarith
  set x := (length + 2 * D) / ρ with hx_def
  set y := length / ρ with hy_def
  have hx_nonneg : 0 ≤ x := div_nonneg (by linarith) hρ.le
  have hy_nonneg : 0 ≤ y := div_nonneg h_length_nonneg hρ.le
  have hxy : x ≤ 5 * y := by
    dsimp only [x, y]
    have h : (length + 2 * D) / ρ ≤ (5 * length) / ρ :=
      div_le_div_of_nonneg_right (by linarith) hρ.le
    have h2 : (5 * length) / ρ = 5 * (length / ρ) := by ring
    rw [h2] at h
    exact h
  have h1 : Real.rpow x α ≤ Real.rpow (5 * y) α :=
    Real.rpow_le_rpow hx_nonneg hxy hα_pos.le
  have h2 : Real.rpow (5 * y) α = Real.rpow 5 α * Real.rpow y α :=
    Real.mul_rpow (show (0 : ℝ) ≤ 5 by norm_num) hy_nonneg
  have h3 : Real.rpow 5 α ≤ 5 := by
    have h4 : Real.rpow 5 α ≤ Real.rpow 5 1 :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hα_one
    have h5 : Real.rpow 5 1 = 5 := by norm_num
    rw [h5] at h4
    exact h4
  dsimp only [Kakeya.realRpowENN]
  have h6 : ENNReal.ofReal (Real.rpow x α) ≤
      ENNReal.ofReal (Real.rpow 5 α) * ENNReal.ofReal (Real.rpow y α) := by
    calc
      ENNReal.ofReal (Real.rpow x α)
          ≤ ENNReal.ofReal (Real.rpow (5 * y) α) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (Real.rpow 5 α * Real.rpow y α) := by rw [h2]
      _ = ENNReal.ofReal (Real.rpow 5 α) * ENNReal.ofReal (Real.rpow y α) :=
        ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) α)
  have h8 : ENNReal.ofReal (Real.rpow 5 α) ≤ (5 : ENNReal) := by
    have h81 : ENNReal.ofReal (Real.rpow 5 α) ≤ ENNReal.ofReal 5 :=
      ENNReal.ofReal_le_ofReal h3
    have h82 : ENNReal.ofReal 5 = (5 : ENNReal) := by norm_num
    rw [h82] at h81
    exact h81
  have h9 : 0 ≤ ENNReal.ofReal (Real.rpow y α) := by positivity
  exact le_trans h6 (mul_le_mul_of_nonneg_right h8 h9)

/-- A subset of a `D`-thickening of a one-dimensional paper AD set remains
AD at the same base scale when `D ≤ δ`.  The factor `6` is the product of
the two-cover thickening loss and the factor-three interval enlargement. -/
lemma PureWZ2PaperADSet1.of_subset_cthickening
    {S T : Set ℝ} {D δ α : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 S δ α C)
    (hwitness : ∀ value ∈ T, ∃ source ∈ S, dist value source ≤ D)
    (hD_nonneg : 0 ≤ D) (hD_leδ : D ≤ δ) :
    PureWZ2PaperADSet1 T δ α (6 * C) := by
  rcases hAD with ⟨hδ_pos, hα_pos, hα_one, hC_one, hC_top, hcover⟩
  have h6C_one : (1 : ENNReal) ≤ 6 * C := by
    have h1 : (1 : ENNReal) ≤ C := hC_one
    have h2 : (1 : ENNReal) ≤ (6 : ENNReal) := by norm_num
    simpa using mul_le_mul' h2 h1
  have h6C_top : (6 * C : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hC_top
  refine ⟨hδ_pos, hα_pos, hα_one, h6C_one, h6C_top, ?_⟩
  intro ρ hρ_nonneg hδ_leρ left length hρ_lelength
  have hρ_pos : 0 < ρ := hδ_pos.trans_le hδ_leρ
  let left' := left - D
  let length' := length + 2 * D
  have hendpoint : left' + length' = left + length + D := by
    dsimp only [left', length']
    ring
  have hρ_lelength' : ρ ≤ length' := by
    dsimp only [length']
    linarith
  have hlocalSubset : T ∩ Set.Icc left (left + length) ⊆
      Metric.cthickening D (S ∩ Set.Icc left' (left' + length')) := by
    intro value hvalue
    rcases hwitness value hvalue.1 with ⟨source, hsource, hdist⟩
    have hdistAbs : |value - source| ≤ D := by
      simpa [Real.dist_eq] using hdist
    have hsourceLeft : left' ≤ source := by
      dsimp only [left']
      have hdiff : value - source ≤ D :=
        (le_abs_self _).trans hdistAbs
      linarith [hvalue.2.1]
    have hsourceRight : source ≤ left' + length' := by
      rw [hendpoint]
      have hdiff : source - value ≤ D := by
        calc
          source - value ≤ |source - value| := le_abs_self _
          _ = |value - source| := by
            rw [show source - value = -(value - source) by ring, abs_neg]
          _ ≤ D := hdistAbs
      linarith [hvalue.2.2]
    exact Metric.mem_cthickening_of_dist_le value source D _
      ⟨hsource, hsourceLeft, hsourceRight⟩ hdist
  have hcoverLocal := hcover ρ hρ_nonneg hδ_leρ left' length' hρ_lelength'
  have hcoverThick := externalCoveringNumber_cthickening_real2
    hρ_pos hD_nonneg (hD_leδ.trans hδ_leρ)
      (A := S ∩ Set.Icc left' (left' + length'))
  have hmono :
      (Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
          (T ∩ Set.Icc left (left + length)) : ENNReal) ≤
        (Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
          (Metric.cthickening D
            (S ∩ Set.Icc left' (left' + length'))) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hlocalSubset
  have hlengthExpanded : length' ≤ 3 * length := by
    dsimp only [length']
    linarith [hD_leδ.trans (hδ_leρ.trans hρ_lelength)]
  have hrpow := rpow_three_factor hρ_pos hD_nonneg hα_pos hα_one
    hlengthExpanded
  calc
    (Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
        (T ∩ Set.Icc left (left + length)) : ENNReal)
        ≤ (Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
            (Metric.cthickening D
              (S ∩ Set.Icc left' (left' + length'))) : ENNReal) := hmono
    _ ≤ 2 * (Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
            (S ∩ Set.Icc left' (left' + length')) : ENNReal) := hcoverThick
    _ ≤ 2 * (C * Kakeya.realRpowENN (length' / ρ) α) := by gcongr
    _ ≤ 2 * (C * (3 * Kakeya.realRpowENN (length / ρ) α)) := by gcongr
    _ = 6 * C * Kakeya.realRpowENN (length / ρ) α := by ring

/-- A subset of a `D`-thickening of a one-dimensional paper AD set remains
AD at the same base scale when `D ≤ 2 * δ`.  The factor `15` is the product
of the three-cover thickening loss and the factor-five interval enlargement. -/
lemma PureWZ2PaperADSet1.of_subset_cthickening_two
    {S T : Set ℝ} {D δ α : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 S δ α C)
    (hwitness : ∀ value ∈ T, ∃ source ∈ S, dist value source ≤ D)
    (hD_nonneg : 0 ≤ D) (hD_leδ : D ≤ 2 * δ) :
    PureWZ2PaperADSet1 T δ α (15 * C) := by
  rcases hAD with ⟨hδ_pos, hα_pos, hα_one, hC_one, hC_top, hcover⟩
  have h15C_one : (1 : ENNReal) ≤ 15 * C := by
    have h1 : (1 : ENNReal) ≤ C := hC_one
    have h2 : (1 : ENNReal) ≤ (15 : ENNReal) := by norm_num
    simpa using mul_le_mul' h2 h1
  have h15C_top : (15 * C : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hC_top
  refine ⟨hδ_pos, hα_pos, hα_one, h15C_one, h15C_top, ?_⟩
  intro ρ hρ_nonneg hδ_leρ left length hρ_lelength
  have hρ_pos : 0 < ρ := hδ_pos.trans_le hδ_leρ
  let left' := left - D
  let length' := length + 2 * D
  have hendpoint : left' + length' = left + length + D := by
    dsimp only [left', length']
    ring
  have hρ_lelength' : ρ ≤ length' := by
    dsimp only [length']
    linarith
  have hlocalSubset : T ∩ Set.Icc left (left + length) ⊆
      Metric.cthickening D (S ∩ Set.Icc left' (left' + length')) := by
    intro value hvalue
    rcases hwitness value hvalue.1 with ⟨source, hsource, hdist⟩
    have hdistAbs : |value - source| ≤ D := by
      simpa [Real.dist_eq] using hdist
    have hsourceLeft : left' ≤ source := by
      dsimp only [left']
      have hdiff : value - source ≤ D :=
        (le_abs_self _).trans hdistAbs
      linarith [hvalue.2.1]
    have hsourceRight : source ≤ left' + length' := by
      rw [hendpoint]
      have hdiff : source - value ≤ D := by
        calc
          source - value ≤ |source - value| := le_abs_self _
          _ = |value - source| := by
            rw [show source - value = -(value - source) by ring, abs_neg]
          _ ≤ D := hdistAbs
      linarith [hvalue.2.2]
    exact Metric.mem_cthickening_of_dist_le value source D _
      ⟨hsource, hsourceLeft, hsourceRight⟩ hdist
  have hcoverLocal := hcover ρ hρ_nonneg hδ_leρ left' length' hρ_lelength'
  have hcoverThick := externalCoveringNumber_cthickening_real3
    hρ_pos hD_nonneg (hD_leδ.trans (mul_le_mul_of_nonneg_left hδ_leρ (by norm_num)))
      (A := S ∩ Set.Icc left' (left' + length'))
  have hmono :
      (Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
          (T ∩ Set.Icc left (left + length)) : ENNReal) ≤
        (Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
          (Metric.cthickening D
            (S ∩ Set.Icc left' (left' + length'))) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hlocalSubset
  have hlengthExpanded : length' ≤ 5 * length := by
    dsimp only [length']
    have hD_le_two_length : D ≤ 2 * length :=
      hD_leδ.trans <| mul_le_mul_of_nonneg_left
        (hδ_leρ.trans hρ_lelength) (by norm_num)
    linarith
  have hrpow := rpow_five_factor hρ_pos hD_nonneg hα_pos hα_one
    hlengthExpanded
  calc
    (Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
        (T ∩ Set.Icc left (left + length)) : ENNReal)
        ≤ (Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
            (Metric.cthickening D
              (S ∩ Set.Icc left' (left' + length'))) : ENNReal) := hmono
    _ ≤ 3 * (Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
            (S ∩ Set.Icc left' (left' + length')) : ENNReal) := hcoverThick
    _ ≤ 3 * (C * Kakeya.realRpowENN (length' / ρ) α) := by gcongr
    _ ≤ 3 * (C * (5 * Kakeya.realRpowENN (length / ρ) α)) := by gcongr
    _ = 15 * C * Kakeya.realRpowENN (length / ρ) α := by ring

lemma PureWZ2PaperADSet1.nearby_projection_transfer
    {E : Set Point3} {v w : Point3} {D δ α : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 (scalarProjection v E) δ α C)
    (h_diff : ∀ p ∈ E, |inner ℝ p w - inner ℝ p v| ≤ D)
    (hD_nonneg : 0 ≤ D) (hD_leδ : D ≤ δ) :
    PureWZ2PaperADSet1 (scalarProjection w E) δ α (6 * C) := by
  rcases hAD with ⟨hδ_pos, hα_pos, hα_one, hC_one, hC_top, hcover⟩
  have h6C_one : (1 : ENNReal) ≤ 6 * C := by
    have h1 : (1 : ENNReal) ≤ C := hC_one
    have h2 : (1 : ENNReal) ≤ (6 : ENNReal) := by norm_num
    have h3 : (1 : ENNReal) * (1 : ENNReal) ≤ (6 : ENNReal) * C := mul_le_mul' h2 h1
    simpa using h3
  have h6C_top : (6 * C : ENNReal) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hC_top
  refine ⟨hδ_pos, hα_pos, hα_one, h6C_one, h6C_top, ?_⟩
  intro ρ hρ_nonneg hδ_leρ left length hρ_lelength
  have hρ_pos : 0 < ρ := by linarith
  set left' := left - D with hleft'_def
  set length' := length + 2 * D with hlength'_def
  have h_endpoint : left' + length' = left + length + D := by
    simp [hleft'_def, hlength'_def]; ring
  have hρ_lelength' : ρ ≤ length' := by
    simp [hlength'_def]; linarith
  have hcover_A : (↑(Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
        (scalarProjection v E ∩ Set.Icc left' (left' + length'))) : ENNReal) ≤
      C * Kakeya.realRpowENN (length' / ρ) α :=
    hcover ρ hρ_nonneg hδ_leρ left' length' hρ_lelength'
  have hD_leρ : D ≤ ρ := le_trans hD_leδ hδ_leρ
  have hB_thick : (scalarProjection w E) ∩ Set.Icc left (left + length) ⊆
      Metric.cthickening D (scalarProjection v E ∩ Set.Icc left' (left' + length')) := by
    intro y hy
    have hyB : y ∈ scalarProjection w E := hy.1
    have hyIcc : y ∈ Set.Icc left (left + length) := hy.2
    rcases hyB with ⟨p, hp, rfl⟩
    set x : ℝ := inner ℝ p v with hx_def
    have hx_in_A : x ∈ scalarProjection v E := ⟨p, hp, rfl⟩
    have h_diff' : |inner ℝ p w - x| ≤ D := h_diff p hp
    have hx1 : left' ≤ x := by
      simp [hleft'_def]
      have h : inner ℝ p w - x ≤ D := by
        calc inner ℝ p w - x
            ≤ |inner ℝ p w - x| := le_abs_self _
          _ ≤ D := h_diff'
      linarith [hyIcc.1]
    have hx2 : x ≤ left' + length' := by
      rw [h_endpoint]
      have h : x - inner ℝ p w ≤ |x - inner ℝ p w| := le_abs_self _
      have h' : |x - inner ℝ p w| = |inner ℝ p w - x| := by
        have h_eq : x - inner ℝ p w = -(inner ℝ p w - x) := by ring
        rw [h_eq, abs_neg]
      rw [h'] at h
      have h'' : |inner ℝ p w - x| ≤ D := h_diff'
      linarith [hyIcc.2]
    have hxS : x ∈ scalarProjection v E ∩ Set.Icc left' (left' + length') := ⟨hx_in_A, ⟨hx1, hx2⟩⟩
    have hdist : dist (inner ℝ p w) x ≤ D := by
      rw [Real.dist_eq]
      exact h_diff'
    exact Metric.mem_cthickening_of_dist_le (inner ℝ p w) x D _ hxS hdist
  have hcover_thick : (↑(Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
        (Metric.cthickening D (scalarProjection v E ∩ Set.Icc left' (left' + length')))) : ENNReal) ≤
      2 * (↑(Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
          (scalarProjection v E ∩ Set.Icc left' (left' + length'))) : ENNReal) :=
    externalCoveringNumber_cthickening_real2 hρ_pos hD_nonneg hD_leρ
  have h_mono_enat : Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
        ((scalarProjection w E) ∩ Set.Icc left (left + length)) ≤
      Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
        (Metric.cthickening D (scalarProjection v E ∩ Set.Icc left' (left' + length'))) :=
    Metric.externalCoveringNumber_mono_set hB_thick
  have h_mono : (↑(Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
        ((scalarProjection w E) ∩ Set.Icc left (left + length))) : ENNReal) ≤
      (↑(Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
          (Metric.cthickening D (scalarProjection v E ∩ Set.Icc left' (left' + length')))) : ENNReal) :=
    ENat.toENNReal_le.mpr h_mono_enat
  have h_length_expanded : length' ≤ 3 * length := by
    simp [hlength'_def]; linarith [le_trans hD_leδ (le_trans hδ_leρ hρ_lelength)]
  have h_rpow_le : Kakeya.realRpowENN (length' / ρ) α ≤
      (3 : ENNReal) * Kakeya.realRpowENN (length / ρ) α :=
    rpow_three_factor hρ_pos hD_nonneg hα_pos hα_one h_length_expanded
  have hC_nonneg : 0 ≤ C := by positivity
  have h_main1 : (↑(Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
          (scalarProjection v E ∩ Set.Icc left' (left' + length'))) : ENNReal) ≤
      C * ((3 : ENNReal) * Kakeya.realRpowENN (length / ρ) α) :=
    le_trans hcover_A (mul_le_mul_of_nonneg_left h_rpow_le hC_nonneg)
  have h2_pos : 0 ≤ (2 : ENNReal) := by positivity
  calc
    (↑(Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
        ((scalarProjection w E) ∩ Set.Icc left (left + length))) : ENNReal)
      ≤ (↑(Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
          (Metric.cthickening D (scalarProjection v E ∩ Set.Icc left' (left' + length')))) : ENNReal) := h_mono
    _ ≤ 2 * (↑(Metric.externalCoveringNumber ⟨ρ, hρ_nonneg⟩
            (scalarProjection v E ∩ Set.Icc left' (left' + length'))) : ENNReal) := hcover_thick
    _ ≤ 2 * (C * ((3 : ENNReal) * Kakeya.realRpowENN (length / ρ) α)) :=
        mul_le_mul_of_nonneg_left h_main1 h2_pos
    _ = 6 * C * Kakeya.realRpowENN (length / ρ) α := by ring

end Kakeya.Assouad

end
