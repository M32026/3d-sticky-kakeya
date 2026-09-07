import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.BrunnMinkowski.BM
import MyLeanRepo.Kakeya.CV.Isoperimetric.MinkowskiContent.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.MinkowskiContent.Smooth
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.LevelSetMeasurability
import Mathlib.Tactic

open scoped Pointwise MeasureTheory

namespace Geometry

open MeasureTheory ENNReal Metric Set
open Isoperimetric

private lemma exists_ennreal_pos_add_lt {a b : ENNReal} (h : a < b) :
    ∃ ε : ENNReal, 0 < ε ∧ a + ε < b := by
  by_cases ha_top : a = ⊤
  · exfalso
    rw [ha_top] at h
    simp at h
  by_cases hb_top : b = ⊤
  · refine ⟨1, by norm_num, ?_⟩
    rw [hb_top]
    exact lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨ha_top, by norm_num⟩)
  · have h_a_lt_b : a.toReal < b.toReal :=
      (ENNReal.toReal_lt_toReal ha_top hb_top).2 h
    let ε' : ℝ := (b.toReal - a.toReal) / 2
    have hε'_pos : 0 < ε' := by
      dsimp only [ε']
      linarith
    have ha'_nonneg : 0 ≤ a.toReal := by positivity
    set ε : ENNReal := ENNReal.ofReal ε' with hε_def
    have hε_pos : 0 < ε := ENNReal.ofReal_pos.mpr hε'_pos
    have h1 : a + ε < b := by
      have ha_eq : a = ENNReal.ofReal a.toReal := by
        rw [ENNReal.ofReal_toReal ha_top]
      have hb_eq : b = ENNReal.ofReal b.toReal := by
        rw [ENNReal.ofReal_toReal hb_top]
      rw [ha_eq, hb_eq, hε_def]
      have h_sum :
          ENNReal.ofReal a.toReal + ENNReal.ofReal ε' =
            ENNReal.ofReal (a.toReal + ε') := by
        rw [ENNReal.ofReal_add ha'_nonneg (by linarith)]
      rw [h_sum]
      have h2 : a.toReal + ε' < b.toReal := by
        dsimp only [ε']
        linarith
      have h_b_pos : 0 < b.toReal := by
        have h_nonneg : 0 ≤ a.toReal := by positivity
        linarith [h_a_lt_b]
      exact (ENNReal.ofReal_lt_ofReal_iff h_b_pos).2 h2
    exact ⟨ε, hε_pos, h1⟩

/-- The sharp isoperimetric inequality follows from an upper Minkowski-content bound. -/
theorem isoperimetric_of_minkowski_content' (n : ℕ) (hn : 2 ≤ n)
    {U : Set (E n)} (hU : IsOpen U) (hBdd : Bornology.IsBounded U)
    (hvol_pos : 0 < volume U) {C : ENNReal}
    (h_minkowski : HasUpperMinkowskiContent n U C) :
    (n : ENNReal) * (volume U) ^ ((n - 1 : ℝ) / n) *
      (volume (unitBall n)) ^ (1 / (n : ℝ)) ≤ C := by
  letI : Nonempty (Fin n) := ⟨⟨0, by linarith⟩⟩
  let V : ENNReal := volume U
  let ω : ENNReal := volume (unitBall n)
  let X : ENNReal := (n : ENNReal) * V ^ ((n - 1 : ℝ) / n) * ω ^ (1 / (n : ℝ))
  have hV_lt_top : V < ⊤ := hBdd.measure_lt_top
  have hU_meas : MeasurableSet U := hU.measurableSet

  by_contra h
  have h_lt : C < X := lt_of_not_ge h
  rcases exists_ennreal_pos_add_lt h_lt with ⟨ε, hε_pos, hε_lt⟩
  rcases h_minkowski ε hε_pos with ⟨δ, hδ_pos, hδ⟩
  let t : ℝ := δ / 2
  have ht_pos : 0 < t := half_pos hδ_pos
  have ht_ltδ : t < δ := half_lt_self hδ_pos

  have h_sum_open : IsOpen (U + t • unitBall n) := by
    have h1 : U + t • unitBall n = ⋃ y ∈ t • unitBall n, (fun x => y + x) '' U := by
      ext z
      simp only [Set.mem_add, Set.mem_iUnion, Set.mem_image]
      constructor
      · rintro ⟨x, hx, y, hy, h_eq⟩
        exact ⟨y, hy, x, hx, by simpa [add_comm] using h_eq⟩
      · rintro ⟨y, hy, x, hx, h_eq⟩
        exact ⟨x, hx, y, hy, by simpa [add_comm] using h_eq⟩
    rw [h1]
    exact isOpen_biUnion fun y hy => by
      let e : E n ≃ₜ E n :=
        { toFun := fun x => y + x
          invFun := fun x => x - y
          left_inv := by intro z; simp
          right_inv := by intro z; simp
          continuous_toFun := continuous_const.add continuous_id
          continuous_invFun := continuous_id.sub continuous_const }
      have h_eq : (fun x => y + x) '' U = e '' U := by rfl
      rw [h_eq]
      exact e.isOpenMap U hU
  have h_sum_meas : MeasurableSet (U + t • unitBall n) := h_sum_open.measurableSet

  have h_bm : volume (U + t • unitBall n) ≥
      V + (n : ENNReal) * ENNReal.ofReal t * V ^ ((n - 1 : ℝ) / n) *
        ω ^ (1 / (n : ℝ)) :=
    parallelVolume_lowerBound n hn U hU_meas t ht_pos h_sum_meas
  have h_upper : volume (U + t • unitBall n) ≤
      V + (C + ε) * ENNReal.ofReal t :=
    hδ t ht_pos ht_ltδ h_sum_meas
  have h1 : V + X * ENNReal.ofReal t ≤ V + (C + ε) * ENNReal.ofReal t := by
    have h_eq : X * ENNReal.ofReal t =
        (n : ENNReal) * ENNReal.ofReal t * V ^ ((n - 1 : ℝ) / n) *
          ω ^ (1 / (n : ℝ)) := by
      simp only [X]
      ring
    rw [h_eq]
    exact le_trans h_bm h_upper
  have h2 : X * ENNReal.ofReal t ≤ (C + ε) * ENNReal.ofReal t :=
    (ENNReal.add_le_add_iff_left hV_lt_top.ne).mp h1
  set c : ENNReal := ENNReal.ofReal t with hc_def
  have hc_pos : c ≠ 0 := (ENNReal.ofReal_pos.mpr ht_pos).ne'
  have hc_ne_top : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have h3 : X ≤ C + ε := by
    by_contra h4
    have h5 : C + ε < X := lt_of_not_ge h4
    have h6 : (C + ε) * c < X * c :=
      (ENNReal.mul_lt_mul_iff_left hc_pos hc_ne_top).mpr h5
    have h7 : X * c ≤ (C + ε) * c := h2
    have h8 : (C + ε) * c ≤ X * c := h6.le
    have h9 : (C + ε) * c = X * c := le_antisymm h8 h7
    exact h6.ne h9
  exact not_le.mpr hε_lt h3

/-- Sharp Hausdorff-form isoperimetry for a bounded open set with smooth boundary covers. -/
theorem smooth_isoperimetric_hausdorff {m : ℕ} [Nonempty (Fin m)]
    {U : Set (E (m + 1))} (hU : IsOpen U) (hBdd : Bornology.IsBounded U)
    (hvol_pos : 0 < volume U) (hH_lt_top : μHE[m] (frontier U) < ⊤)
    (hcover : ∀ ε : ENNReal, 0 < ε → ε < ⊤ → SmoothBoundaryCover U ε) :
    ((m + 1 : ℕ) : ENNReal) * (volume U) ^ ((m : ℝ) / (m + 1)) *
      (volume (unitBall (m + 1))) ^ (1 / ((m + 1 : ℝ))) ≤ μHE[m] (frontier U) := by
  have h1 : HasUpperMinkowskiContent (m + 1) U (μHE[m] (frontier U)) :=
    smooth_outer_minkowski_content hU hBdd hcover hH_lt_top
  have h_pos : 0 < m :=
    Nonempty.elim (inferInstance : Nonempty (Fin m)) fun i => Fin.pos i
  have hmn : 2 ≤ m + 1 := by linarith
  have h_main := isoperimetric_of_minkowski_content' (m + 1) hmn hU hBdd hvol_pos h1
  have h_cast1 : (((m + 1 : ℕ) : ℝ) - 1) = (m : ℝ) := by
    simp [Nat.cast_add]
  have h_cast2 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
    simp [Nat.cast_add]
  rw [h_cast1, h_cast2] at h_main
  exact h_main

/-- Hausdorff measure of compactly supported level sets is measurable in the level. -/
lemma level_set_hausdorff_measurable
    {n : ℕ} {u : E n → ℝ} (hu : ContDiff ℝ 1 u) (h_supp : HasCompactSupport u)
    (hn : 2 ≤ n) :
    Measurable fun s : ℝ => μHE[n - 1] {x | u x = s} := by
  letI : Nonempty (Fin n) := ⟨⟨0, by linarith⟩⟩
  let K := tsupport u
  have hK_compact : IsCompact K := h_supp.isCompact
  have h_cont : Continuous u := hu.continuous
  let H_full : ℝ → ENNReal := fun s => μHE[n - 1] (K ∩ {x | u x = s})
  have hH_full_meas : Measurable H_full :=
    levelSetMeasure_compact_measurable hn hK_compact h_cont
  let H : ℝ → ENNReal := fun s => μHE[n - 1] {x | u x = s}
  have h_eq_ne_zero : ∀ s ≠ 0, H s = H_full s := by
    intro s hs
    have h_sub : {x | u x = s} ⊆ K := by
      intro x hx
      have h6 : u x ≠ 0 := by
        rw [hx]
        exact hs
      exact subset_closure (Function.mem_support.mpr h6)
    have h9 : K ∩ {x | u x = s} = {x | u x = s} := Set.inter_eq_right.mpr h_sub
    dsimp only [H, H_full]
    rw [h9]
  have h_meas : Measurable H := by
    have h1 : H = fun s : ℝ => if s = 0 then H 0 else H_full s := by
      funext s
      by_cases h : s = 0
      · subst h
        simp
      · rw [if_neg h]
        exact h_eq_ne_zero s h
    rw [h1]
    exact Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const hH_full_meas
  exact h_meas

/-- Markov's inequality in the form used for selecting a common good level. -/
private lemma mul_measure_lt_le_lintegral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ENNReal} (hf : Measurable f) {c : ENNReal} (hc_pos : 0 < c) :
    c * μ {x | f x > c} ≤ ∫⁻ x, f x ∂μ := by
  let S : Set α := {x | f x > c}
  have hS : MeasurableSet S := hf measurableSet_Ioi
  have h4 : ∫⁻ x in S, (c : ENNReal) ∂μ ≤ ∫⁻ x in S, f x ∂μ := by
    apply setLIntegral_mono' hS
    intro x hx
    exact hx.le
  have h5 : ∫⁻ x in S, (c : ENNReal) ∂μ = c * μ S := by
    simp
  calc
    c * μ S ≤ ∫⁻ x in S, f x ∂μ := by rw [← h5]; exact h4
    _ ≤ ∫⁻ x, f x ∂μ := setLIntegral_le_lintegral _ _

/-- Select a level in `(0,1)` satisfying simultaneous Hausdorff and volume bounds. -/
lemma level_set_selection_Ioo {H V : ℝ → ENNReal}
    (hH : Measurable H) (hV : Measurable V)
    (P : ENNReal) (hP_pos : 0 < P) (hP_lt_top : P < ⊤)
    (δ η : ℝ) (hδ_pos : 0 < δ) (hη_pos : 0 < η)
    (J I : ENNReal)
    (hJ : ∫⁻ s in Set.Ioo (0 : ℝ) 1, H s = J)
    (hI : ∫⁻ s in Set.Ioo (0 : ℝ) 1, V s = I)
    (h_sum : I / ENNReal.ofReal η + J / (P + ENNReal.ofReal δ) < 1) :
    ∃ s ∈ Set.Ioo (0 : ℝ) 1,
      H s ≤ P + ENNReal.ofReal δ ∧ V s ≤ ENNReal.ofReal η := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  have hμ_univ : μ Set.univ = 1 := by
    have h9 : volume (Set.Ioo (0 : ℝ) 1) = 1 := by
      rw [Real.volume_Ioo]
      norm_num
    simpa [μ] using h9
  let bH : ENNReal := P + ENNReal.ofReal δ
  let bV : ENNReal := ENNReal.ofReal η
  have hbH_pos : 0 < bH := by positivity
  have hbH_ne_top : bH ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨hP_lt_top.ne, ENNReal.ofReal_ne_top⟩
  have hbV_pos : 0 < bV := by positivity
  have hbV_ne_top : bV ≠ ⊤ := ENNReal.ofReal_ne_top
  let A : Set ℝ := {s | V s > bV}
  let B : Set ℝ := {s | H s > bH}
  have hA_meas : MeasurableSet A := hV measurableSet_Ioi
  have hB_meas : MeasurableSet B := hH measurableSet_Ioi
  have h1 : bV * μ A ≤ I := by
    have h_markov : bV * μ A ≤ ∫⁻ s, V s ∂μ :=
      mul_measure_lt_le_lintegral hV hbV_pos
    have h_int : ∫⁻ s, V s ∂μ = I := by simpa [μ] using hI
    rwa [h_int] at h_markov
  have hμA_le : μ A ≤ I / bV := by
    by_contra h
    have h' : I / bV < μ A := lt_of_not_ge h
    have h'' : bV * (I / bV) < bV * μ A :=
      ENNReal.mul_lt_mul_right hbV_pos.ne' hbV_ne_top h'
    rw [ENNReal.mul_div_cancel hbV_pos.ne' hbV_ne_top] at h''
    exact not_le.mpr h'' h1
  have h2 : bH * μ B ≤ J := by
    have h_markov : bH * μ B ≤ ∫⁻ s, H s ∂μ :=
      mul_measure_lt_le_lintegral hH hbH_pos
    have h_int : ∫⁻ s, H s ∂μ = J := by simpa [μ] using hJ
    rwa [h_int] at h_markov
  have hμB_le : μ B ≤ J / bH := by
    by_contra h
    have h' : J / bH < μ B := lt_of_not_ge h
    have h'' : bH * (J / bH) < bH * μ B :=
      ENNReal.mul_lt_mul_right hbH_pos.ne' hbH_ne_top h'
    rw [ENNReal.mul_div_cancel hbH_pos.ne' hbH_ne_top] at h''
    exact not_le.mpr h'' h2
  have h3 : μ A + μ B < 1 := by
    calc
      μ A + μ B ≤ I / bV + J / bH := by gcongr
      _ = I / ENNReal.ofReal η + J / (P + ENNReal.ofReal δ) := by rfl
      _ < 1 := h_sum
  have h4 : μ (A ∪ B) ≤ μ A + μ B := measure_union_le _ _
  have h5 : μ (A ∪ B) < 1 := h4.trans_lt h3
  have h6 : ¬(Set.Ioo (0 : ℝ) 1 ⊆ A ∪ B) := by
    intro h_sub
    have h7 : μ (Set.Ioo (0 : ℝ) 1) ≤ μ (A ∪ B) := measure_mono h_sub
    have h8 : μ (Set.Ioo (0 : ℝ) 1) = 1 := by
      have h9 : volume (Set.Ioo (0 : ℝ) 1) = 1 := by
        rw [Real.volume_Ioo]
        norm_num
      simpa [μ] using h9
    rw [h8] at h7
    exact not_le.mpr h5 h7
  have h7 : ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∉ A ∪ B := by
    simpa [Set.not_subset] using h6
  rcases h7 with ⟨s, h_s_in, hs⟩
  have h_notA : s ∉ A := fun hA => hs (Or.inl hA)
  have h_notB : s ∉ B := fun hB => hs (Or.inr hB)
  have hH_le : H s ≤ bH := by
    by_contra h
    exact h_notB (lt_of_not_ge h)
  have hV_le : V s ≤ bV := by
    by_contra h
    exact h_notA (lt_of_not_ge h)
  exact ⟨s, h_s_in, hH_le, hV_le⟩

end Geometry
