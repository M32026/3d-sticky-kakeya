import MyLeanRepo.Kakeya.Cinematic.Targets.RectanglePacking

/-!
# Generalized rectangle packing bound

This module extracts the core area/overlap argument from RectanglePacking
but allows the containing region to have an arbitrary interval length H,
rather than forcing H = sqrt(lambda * delta / t).

The resulting bound is:
  R.card ≤ 42 * lambda^2 * H / sqrt(delta / t)

where H is the length of the containing interval.
-/

noncomputable section

open MeasureTheory Set

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace
attribute [local instance] Classical.propDecidable

namespace Kakeya.Cinematic

theorem generalized_packing_bound
    {K : ℝ} (hK : 1 ≤ K)
    {family : Set C2Function}
    {I : ParameterInterval} (hI : I.IsShort K)
    {delta t lambda : ℝ}
    (hdelta : 0 < delta) (hdt : delta ≤ t) (hlambda : 100 ≤ lambda)
    {center : C2Function}
    {R : RectangleFamily delta t}
    (hCenters : R.CentersIn family)
    (hOver : R.IsOverCentralQuarterOf I)
    (hIncomp : R.IsPairwiseIncomparable family 100)
    (hdist : ∀ i, c2Distance center (R.rectangle i).function ≤ 3 * t)
    {J : ParameterInterval} {g : C2Function}
    (hcontain : ∀ i, (R.rectangle i).carrier ⊆
        verticalNeighborhoodOn g (lambda * delta) J) :
    (R.card : ℝ) ≤ 42 * lambda^2 * J.length / Real.sqrt (delta / t) := by
  let half : Fin R.card → Set (UnitPoint × ℝ) :=
    fun i => (R.rectangle i).halfCarrier
  have h_half_mble : ∀ i : Fin R.card, MeasurableSet (half i) := by
    intro i; exact mble_verticalNeighborhoodOn _ _ _
  have h_half_sub : ∀ i : Fin R.card, half i ⊆
      verticalNeighborhoodOn g (lambda * delta) J := by
    intro i
    have h1 : half i ⊆ (R.rectangle i).carrier :=
      (R.rectangle i).halfCarrier_subset_carrier
    exact h1.trans (hcontain i)
  have h_area_half : ∀ i : Fin R.card,
      volume (half i) = ENNReal.ofReal (delta * Real.sqrt (delta / t)) := by
    intro i
    rw [(R.rectangle i).volume_halfCarrier hdelta.le, (R.rectangle i).interval_length]
    <;> ring
  let Ucarrier := verticalNeighborhoodOn g (lambda * delta) J
  have hU_mble : MeasurableSet Ucarrier :=
    mble_verticalNeighborhoodOn g (lambda * delta) J
  have hlamδ : 0 ≤ lambda * delta := by positivity
  have h_area_U : volume Ucarrier =
      ENNReal.ofReal (2 * lambda * delta * J.length) := by
    change volume (verticalNeighborhoodOn g (lambda * delta) J) =
      ENNReal.ofReal (2 * lambda * delta * J.length)
    convert volume_verticalNeighborhoodOn g (lambda * delta) J hlamδ using 1
    ring_nf
  /- KEY BOUNDED-OVERLAP STATEMENT -/
  have h_mult : ∀ (p : UnitPoint × ℝ), p ∈ Ucarrier →
      (∑ i ∈ Finset.univ, (half i).indicator (fun _ => (1 : ENNReal)) p) ≤
        ENNReal.ofReal (21 * lambda) := by
    intro p hp
    let θ₀ : UnitPoint := p.1
    let y₀ : ℝ := p.2
    let S : Finset (Fin R.card) := Finset.univ.filter (fun i => p ∈ half i)
    have h_sum_eq : ∑ i ∈ Finset.univ, (half i).indicator (fun _ => (1 : ENNReal)) p =
        (S.card : ENNReal) := by
      have h1 : ∀ i ∈ Finset.univ, (half i).indicator (fun _ => (1 : ENNReal)) p =
          (if p ∈ half i then (1 : ENNReal) else (0 : ENNReal)) := by
        intro i _; rw [Set.indicator_apply]
      have h2 : ∑ i ∈ Finset.univ, (half i).indicator (fun _ => (1 : ENNReal)) p =
          ∑ i ∈ Finset.univ, (if p ∈ half i then (1 : ENNReal) else (0 : ENNReal)) := by
        apply Finset.sum_congr rfl; exact h1
      rw [h2]
      have h3 : ∑ i ∈ Finset.univ, (if p ∈ half i then (1 : ENNReal) else (0 : ENNReal)) =
          ∑ i ∈ S, (1 : ENNReal) := by
        rw [←Finset.sum_filter]
        <;> rfl
      rw [h3]; simp <;> norm_cast
    rw [h_sum_eq]
    by_cases hS_empty : S = ∅
    · rw [hS_empty]; simp <;> positivity
    have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
    let i₀ := Finset.min' S hS_nonempty
    have hi₀_in : i₀ ∈ S := Finset.min'_mem S hS_nonempty
    let f : Fin R.card → C2Function := fun i => (R.rectangle i).function
    let D : Fin R.card → ℝ := fun i => (f i).firstDeriv θ₀
    let d : ℝ := Real.sqrt (delta * t)
    have ht_pos : 0 < t := by linarith [hdelta, hdt]
    have hd_pos : 0 < d := Real.sqrt_pos.mpr (mul_pos hdelta ht_pos)
    have hθ₀_half : ∀ i ∈ S, θ₀ ∈ (R.rectangle i).interval.half.carrier := by
      intro i hi
      have h : p ∈ half i := (Finset.mem_filter.mp hi).2
      exact h.1
    have hy₀ : ∀ i ∈ S, |y₀ - f i θ₀| ≤ delta := by
      intro i hi
      have h : p ∈ half i := (Finset.mem_filter.mp hi).2
      exact h.2
    have hdist6 : ∀ i j, c2Distance (f i) (f j) ≤ 6 * t := by
      intro i j
      have h1 : c2Distance (f i) center ≤ 3 * t := by
        have h1a : c2Distance center (f i) ≤ 3 * t := hdist i
        have h_sym : c2Distance (f i) center = c2Distance center (f i) := by
          rw [c2Distance_eq_dist, c2Distance_eq_dist, dist_comm]
        rw [h_sym]; exact h1a
      have h2 : c2Distance center (f j) ≤ 3 * t := hdist j
      have h3 : c2Distance (f i) (f j) ≤ c2Distance (f i) center + c2Distance center (f j) := by
        have h4 : c2Distance (f i) (f j) = dist (f i) (f j) := c2Distance_eq_dist (f i) (f j)
        have h5 : c2Distance (f i) center = dist (f i) center := c2Distance_eq_dist (f i) center
        have h6 : c2Distance center (f j) = dist center (f j) := c2Distance_eq_dist center (f j)
        rw [h4, h5, h6]
        exact dist_triangle (f i) center (f j)
      linarith
    have hval2 : ∀ i ∈ S, ∀ j ∈ S, |f i θ₀ - f j θ₀| ≤ 2 * delta := by
      intro i hi j hj
      have hi' : |f i θ₀ - y₀| ≤ delta := by
        have h : |y₀ - f i θ₀| ≤ delta := hy₀ i hi
        have h' : |f i θ₀ - y₀| = |y₀ - f i θ₀| := by rw [abs_sub_comm]
        rw [h']; exact h
      have hj' : |y₀ - f j θ₀| ≤ delta := hy₀ j hj
      calc
        |f i θ₀ - f j θ₀| ≤ |f i θ₀ - y₀| + |y₀ - f j θ₀| := by
          exact abs_sub_le (f i θ₀) y₀ (f j θ₀)
        _ ≤ delta + delta := by gcongr
        _ = 2 * delta := by ring
    let L : ℝ := Real.sqrt (delta / t) / 4
    have hθ₁_in : (θ₀ : ℝ) + L ≤ 1 := by
      have h1 : θ₀ ∈ (R.rectangle i₀).interval.half.carrier := hθ₀_half i₀ hi₀_in
      have h2 : (θ₀ : ℝ) ≤ (R.rectangle i₀).interval.half.right := h1.2
      have h_right_up : (R.rectangle i₀).interval.right ≤ 1 :=
        (R.rectangle i₀).interval.right_mem.2
      have h_len : (R.rectangle i₀).interval.length = Real.sqrt (delta / t) :=
        (R.rectangle i₀).interval_length
      have h3 : (R.rectangle i₀).interval.half.right =
          (R.rectangle i₀).interval.right - (R.rectangle i₀).interval.length / 4 := by rfl
      rw [h3, h_len] at h2
      have h4 : (θ₀ : ℝ) + Real.sqrt (delta / t) / 4 ≤
          (R.rectangle i₀).interval.right := by linarith
      have h5 : (θ₀ : ℝ) + L ≤ (R.rectangle i₀).interval.right := by
        have hL_eq : L = Real.sqrt (delta / t) / 4 := by rfl
        rw [hL_eq]; exact h4
      linarith [h_right_up, h5]
    have h_x_in_interval : ∀ i ∈ S, ∀ (x : UnitPoint),
        (θ₀ : ℝ) ≤ (x : ℝ) → (x : ℝ) ≤ (θ₀ : ℝ) + L →
        x ∈ (R.rectangle i).interval.carrier := by
      intro i hi x hx1 hx2
      have h1 : θ₀ ∈ (R.rectangle i).interval.half.carrier := hθ₀_half i hi
      have h_left : (R.rectangle i).interval.left ≤ (x : ℝ) := by
        have h2 : (R.rectangle i).interval.half.left ≤ (θ₀ : ℝ) := h1.1
        have h3 : (R.rectangle i).interval.left ≤ (R.rectangle i).interval.half.left := by
          simp [ParameterInterval.half] <;> linarith [(R.rectangle i).interval.length_nonneg]
        linarith
      have h_right : (x : ℝ) ≤ (R.rectangle i).interval.right := by
        have h2 : (θ₀ : ℝ) ≤ (R.rectangle i).interval.half.right := h1.2
        have h4 : (R.rectangle i).interval.half.right =
            (R.rectangle i).interval.right - (R.rectangle i).interval.length / 4 := by rfl
        have h5 : (R.rectangle i).interval.length = Real.sqrt (delta / t) :=
          (R.rectangle i).interval_length
        rw [h4, h5] at h2
        have h6 : (x : ℝ) ≤ (θ₀ : ℝ) + Real.sqrt (delta / t) / 4 := hx2
        linarith
      exact ⟨h_left, h_right⟩
    have h_J_contains : ∀ i ∈ S, ∀ (x : UnitPoint),
        (θ₀ : ℝ) ≤ (x : ℝ) → (x : ℝ) ≤ (θ₀ : ℝ) + L →
        x ∈ J.carrier := by
      intro i hi x hx1 hx2
      have hxi : x ∈ (R.rectangle i).interval.carrier := h_x_in_interval i hi x hx1 hx2
      have hpt : (x, (R.rectangle i).function x) ∈ (R.rectangle i).carrier := by
        have h_zero : |(R.rectangle i).function x - (R.rectangle i).function x| = 0 := by simp
        exact ⟨hxi, by rw [h_zero] <;> linarith [hdelta]⟩
      have h_in_U : (x, (R.rectangle i).function x) ∈ Ucarrier := hcontain i hpt
      exact h_in_U.1
    have hbound : ∀ i ∈ S, ∀ j ∈ S, ∀ (x : UnitPoint),
        (θ₀ : ℝ) ≤ (x : ℝ) → (x : ℝ) ≤ (θ₀ : ℝ) + L →
        |f i x - f j x| ≤ 2 * lambda * delta := by
      intro i hi j hj x hx1 hx2
      have hxi_J : x ∈ J.carrier := h_J_contains i hi x hx1 hx2
      have hxj_J : x ∈ J.carrier := h_J_contains j hj x hx1 hx2
      have h_i_car : (x, f i x) ∈ (R.rectangle i).carrier := by
        have hxi : x ∈ (R.rectangle i).interval.carrier := h_x_in_interval i hi x hx1 hx2
        have h_zero : |f i x - f i x| = 0 := by simp
        exact ⟨hxi, by rw [h_zero] <;> linarith [hdelta]⟩
      have h_j_car : (x, f j x) ∈ (R.rectangle j).carrier := by
        have hxj : x ∈ (R.rectangle j).interval.carrier := h_x_in_interval j hj x hx1 hx2
        have h_zero : |f j x - f j x| = 0 := by simp
        exact ⟨hxj, by rw [h_zero] <;> linarith [hdelta]⟩
      have h_i_U : (x, f i x) ∈ Ucarrier := hcontain i h_i_car
      have h_j_U : (x, f j x) ∈ Ucarrier := hcontain j h_j_car
      have h_i_bound : |f i x - g x| ≤ lambda * delta := h_i_U.2
      have h_j_bound : |f j x - g x| ≤ lambda * delta := h_j_U.2
      have h_j_bound' : |g x - f j x| ≤ lambda * delta := by
        have h : |g x - f j x| = |f j x - g x| := by rw [abs_sub_comm]
        rw [h]; exact h_j_bound
      have h_tri : |f i x - f j x| ≤ |f i x - g x| + |g x - f j x| := by
        calc
          |f i x - f j x| = |(f i x - g x) + (g x - f j x)| := by ring_nf
          _ ≤ |f i x - g x| + |g x - f j x| := by
            exact abs_add_le (f i x - g x) (g x - f j x)
      linarith [h_i_bound, h_j_bound', h_tri]
    have h_upper : ∀ i ∈ S, ∀ j ∈ S, |D i - D j| ≤ 10 * lambda * d := by
      intro i hi j hj
      exact derivative_upper_bound (f i) (f j) θ₀ delta t lambda hdelta ht_pos hlambda
        (hdist6 i j) (hval2 i hi j hj) L rfl hθ₁_in (hbound i hi j hj)
    have h_lower : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → |D i - D j| > d := by
      intro i hi j hj hne
      by_contra h
      have h' : |D i - D j| ≤ d := by linarith
      have h_comp : (R.rectangle i).AreLambdaComparable (R.rectangle j) family 100 :=
        derivative_lower_bound hdelta ht_pos hK hI
          (hOver i) (hOver j)
          (hθ₀_half i hi) (hθ₀_half j hj)
          (hCenters i) (hdist6 i j) (hval2 i hi j hj) h'
      have h_incomp : (R.rectangle i).AreLambdaIncomparable (R.rectangle j) family 100 :=
        hIncomp i j hne
      exact h_incomp h_comp
    let a : ℝ := D i₀ - 10 * lambda * d
    let b : ℝ := D i₀ + 10 * lambda * d
    have hab : a ≤ b := by
      dsimp only [a, b]
      have h : 0 ≤ 20 * lambda * d := by positivity
      linarith
    let S' : Finset ℝ := Finset.image D S
    have hS'_sub : ∀ x ∈ S', x ∈ Set.Icc a b := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have h : |D i - D i₀| ≤ 10 * lambda * d := h_upper i hi i₀ hi₀_in
      have h5 : a ≤ D i := by
        have h6 := (abs_le.mp h).1
        dsimp only [a] at * <;> linarith
      have h7 : D i ≤ b := by
        have h8 := (abs_le.mp h).2
        dsimp only [b] at * <;> linarith
      exact ⟨h5, h7⟩
    have hS'_sep : ∀ x ∈ S', ∀ y ∈ S', x ≠ y → |x - y| > d := by
      intro x hx y hy hxy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      have hne : i ≠ j := by
        intro h
        rw [h] at hxy
        simp at hxy
      exact h_lower i hi j hj hne
    have h_inj : Set.InjOn D S := by
      intro i hi j hj h
      by_contra hne
      have h_sep : |D i - D j| > d := h_lower i hi j hj hne
      have h_eq : |D i - D j| = 0 := by
        have h' : D i = D j := h
        rw [h'] <;> simp
      linarith [hd_pos, h_sep, h_eq]
    have h_card : S'.card = S.card :=
      Finset.card_image_of_injOn h_inj
    have h_pack2 : (S'.card : ℝ) ≤ (b - a) / d + 1 :=
      point_packing_bound hd_pos hab S' hS'_sub hS'_sep
    have h_ba : b - a = 20 * lambda * d := by
      dsimp only [a, b] <;> ring
    rw [h_card] at h_pack2
    rw [h_ba] at h_pack2
    have h_final : (S.card : ℝ) ≤ 21 * lambda := by
      have h9 : (S.card : ℝ) ≤ 20 * lambda + 1 := by
        have h10 : (20 * lambda * d) / d = 20 * lambda := by
          field_simp [hd_pos.ne'] <;> ring
        rw [h10] at h_pack2
        exact h_pack2
      have h11 : 20 * lambda + 1 ≤ 21 * lambda := by
        have h12 : 1 ≤ lambda := by linarith
        linarith
      linarith
    have h_ennreal : (S.card : ENNReal) ≤ ENNReal.ofReal (21 * lambda) := by
      have h13 : (S.card : ENNReal) = ENNReal.ofReal (S.card : ℝ) := by norm_cast
      rw [h13]
      have h14 : 0 ≤ (S.card : ℝ) := by positivity
      exact ENNReal.ofReal_le_ofReal h_final
    exact h_ennreal
  /- Apply bounded overlap -/
  have h_half_mble' : ∀ i ∈ Finset.univ, MeasurableSet (half i) := by
    intro i _; exact h_half_mble i
  have h_half_sub' : ∀ i ∈ Finset.univ, half i ⊆ Ucarrier := by
    intro i _; exact h_half_sub i
  have h_pack : ∑ i ∈ Finset.univ, volume (half i) ≤
      ENNReal.ofReal (21 * lambda) * volume Ucarrier :=
    bounded_overlap_ennreal
      (s := Finset.univ) (A := half) (U := Ucarrier)
      hU_mble h_half_mble' h_half_sub'
      (ENNReal.ofReal (21 * lambda)) h_mult
  /- Compute left side -/
  have h_sum : ∑ i ∈ Finset.univ, volume (half i) =
      (R.card : ENNReal) * ENNReal.ofReal (delta * Real.sqrt (delta / t)) := by
    have h4 : ∀ i ∈ Finset.univ, volume (half i) =
        ENNReal.ofReal (delta * Real.sqrt (delta / t)) := by
      intro i _; exact h_area_half i
    rw [Finset.sum_congr rfl h4]
    simp [Finset.sum_const]
  rw [h_sum] at h_pack
  /- Compute right side -/
  rw [h_area_U] at h_pack
  have h_nonneg1 : 0 ≤ 21 * lambda := by linarith
  have hJlen : 0 ≤ J.length := J.length_nonneg
  have h_nonneg2 : 0 ≤ 2 * lambda * delta * J.length := by positivity
  have h_mul : ENNReal.ofReal (21 * lambda) *
      ENNReal.ofReal (2 * lambda * delta * J.length) =
      ENNReal.ofReal ((21 * lambda) * (2 * lambda * delta * J.length)) := by
    exact Eq.symm (ENNReal.ofReal_mul h_nonneg1)
  rw [h_mul] at h_pack
  have h_combine1 : (R.card : ENNReal) * ENNReal.ofReal (delta * Real.sqrt (delta / t)) =
      ENNReal.ofReal ((R.card : ℝ) * (delta * Real.sqrt (delta / t))) := by
    have h_cast : (R.card : ENNReal) = ENNReal.ofReal (R.card : ℝ) := by norm_cast
    rw [h_cast]
    rw [←ENNReal.ofReal_mul (by positivity)]
  rw [h_combine1] at h_pack
  have h_rhs : (21 * lambda) * (2 * lambda * delta * J.length) =
      42 * lambda^2 * J.length * delta := by ring
  rw [h_rhs] at h_pack
  have ht_pos : 0 < t := by linarith [hdelta, hdt]
  have hdt_pos : 0 < delta / t := by positivity
  have h_sqrt_pos : 0 < Real.sqrt (delta / t) := Real.sqrt_pos.mpr hdt_pos
  have h_pos2 : 0 < delta * Real.sqrt (delta / t) := by positivity
  have h_nonneg3 : 0 ≤ (R.card : ℝ) * (delta * Real.sqrt (delta / t)) := by positivity
  have h_nonneg4 : 0 ≤ 42 * lambda^2 * J.length * delta := by positivity
  have h_iff : ENNReal.ofReal ((R.card : ℝ) * (delta * Real.sqrt (delta / t))) ≤
      ENNReal.ofReal (42 * lambda^2 * J.length * delta) ↔
      (R.card : ℝ) * (delta * Real.sqrt (delta / t)) ≤
      42 * lambda^2 * J.length * delta := by
    exact ENNReal.ofReal_le_ofReal_iff h_nonneg4
  have h_pack_real : (R.card : ℝ) * (delta * Real.sqrt (delta / t)) ≤
      42 * lambda^2 * J.length * delta := h_iff.mp h_pack
  have h_final_real : (R.card : ℝ) ≤ 42 * lambda^2 * J.length / Real.sqrt (delta / t) := by
    calc
      (R.card : ℝ)
        = ((R.card : ℝ) * (delta * Real.sqrt (delta / t))) / (delta * Real.sqrt (delta / t)) := by
          field_simp [h_pos2.ne'] <;> ring
      _ ≤ (42 * lambda^2 * J.length * delta) / (delta * Real.sqrt (delta / t)) := by gcongr
      _ = 42 * lambda^2 * J.length / Real.sqrt (delta / t) := by
          field_simp [hdelta.ne', h_sqrt_pos.ne'] <;> ring
  exact h_final_real

end Kakeya.Cinematic
