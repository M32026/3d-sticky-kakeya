/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Area of a 2D strip intersected with a rectangle

Area bounds for planar strips in a symmetric rectangle `[-b, b] × [-c, c]`, and the
three-dimensional box-strip estimates obtained by slicing.  The unit-square and unit-box
statements are the special case `b = c = 1`.
-/

open MeasureTheory Metric Set

@[expose] public section

noncomputable section

namespace MeasureTheory

/-- Fiber length bound for a one-dimensional strip `|a · y - c| ≤ r` when `a ≠ 0`. -/
lemma volume_strip_fiber_le {a c r : ℝ} (ha : a ≠ 0) (hr : 0 ≤ r) :
    volume {y : ℝ | |a * y - c| ≤ r} ≤ ENNReal.ofReal (2 * r / |a|) := by
  have habs_pos : 0 < |a| := abs_pos.mpr ha
  have hρ_nonneg : (0 : ℝ) ≤ r / |a| := div_nonneg hr habs_pos.le
  rw [mul_div_assoc]
  refine (measure_mono fun y hy => ?_).trans_eq (Real.volume_closedBall (c / a) (r / |a|))
  rw [mem_closedBall, Real.dist_eq, le_div_iff₀ habs_pos, mul_comm, ← abs_mul, mul_sub,
    mul_div_cancel₀ _ ha]
  exact hy

/-- 2D strip area bound for a rectangle `[-b,b] × [-c,c]` when `a₂ ≠ 0`
(the coefficient of `p.2` is nonzero, so we fix `p.1` and integrate over `p.2`).
Bound: `4·b·r / |a₂|`. -/
theorem volume_strip_inter_rectangle_le_of_b_ne_zero {a₁ a₂ C r b c : ℝ} (ha₂ : a₂ ≠ 0)
    (hr : 0 ≤ r) (_ : 0 ≤ b) (_ : 0 ≤ c) :
    volume ({p : ℝ × ℝ | p.1 ∈ Set.Icc (-b) b ∧ p.2 ∈ Set.Icc (-c) c ∧
                          |a₁ * p.1 + a₂ * p.2 - C| ≤ r}) ≤
      ENNReal.ofReal (4 * b * r / |a₂|) := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 ∈ Set.Icc (-b) b ∧ p.2 ∈ Set.Icc (-c) c ∧
      |a₁ * p.1 + a₂ * p.2 - C| ≤ r} :=
    (measurable_fst measurableSet_Icc).inter ((measurable_snd measurableSet_Icc).inter
      (measurableSet_le (((measurable_fst.const_mul a₁).add
        (measurable_snd.const_mul a₂)).sub_const C).abs measurable_const))
  rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_apply hmeas]
  refine (lintegral_mono (g := (Set.Icc (-b) b).indicator
      fun _ => ENNReal.ofReal (2 * r / |a₂|)) fun x => ?_).trans ?_
  · by_cases hx : x ∈ Set.Icc (-b) b
    · rw [Set.indicator_of_mem hx]
      refine (measure_mono fun y hy => ?_).trans (volume_strip_fiber_le (c := C - a₁ * x) ha₂ hr)
      exact (congrArg abs (by ring : a₂ * y - (C - a₁ * x) = a₁ * x + a₂ * y - C)).trans_le hy.2.2
    · rw [Set.indicator_of_notMem hx]
      exact (measure_mono_null (fun y hy => hx hy.1) measure_empty).le
  · rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc,
      ← ENNReal.ofReal_mul (div_nonneg (by linarith) (abs_nonneg a₂))]
    exact (congrArg ENNReal.ofReal (by ring)).le

/-- 2D strip area bound for a rectangle `[-b,b] × [-c,c]` when `a₁ ≠ 0`
(the coefficient of `p.1` is nonzero, so we swap coordinates and use
`volume_strip_inter_rectangle_le_of_b_ne_zero`).  Bound: `4·c·r / |a₁|`. -/
theorem volume_strip_inter_rectangle_le_of_a_ne_zero {a₁ a₂ C r b c : ℝ} (ha₁ : a₁ ≠ 0)
    (hr : 0 ≤ r) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    volume ({p : ℝ × ℝ | p.1 ∈ Set.Icc (-b) b ∧ p.2 ∈ Set.Icc (-c) c ∧
                          |a₁ * p.1 + a₂ * p.2 - C| ≤ r}) ≤
      ENNReal.ofReal (4 * c * r / |a₁|) := by
  have hPS : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
      (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact Measure.measurePreserving_swap
  have hswap : {p : ℝ × ℝ | p.1 ∈ Set.Icc (-b) b ∧ p.2 ∈ Set.Icc (-c) c ∧
        |a₁ * p.1 + a₂ * p.2 - C| ≤ r} =
      Prod.swap ⁻¹' {p : ℝ × ℝ | p.1 ∈ Set.Icc (-c) c ∧ p.2 ∈ Set.Icc (-b) b ∧
        |a₂ * p.1 + a₁ * p.2 - C| ≤ r} := by
    ext ⟨x, y⟩
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Prod.swap_prod_mk,
      show a₂ * y + a₁ * x - C = a₁ * x + a₂ * y - C from by ring]
    exact and_left_comm
  rw [hswap, hPS.measure_preimage_emb
    (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).measurableEmbedding]
  exact volume_strip_inter_rectangle_le_of_b_ne_zero ha₁ hr hc hb

/-- 2D strip area bound for a rectangle `[-b,b] × [-c,c]` with `b ≤ c`.
The strip `|a₁·y₁ + a₂·y₂ - C| ≤ r` has area at most `4·c·r / max|a₁||a₂|`. -/
theorem volume_strip_inter_rectangle_le_max {a₁ a₂ C r b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbc : b ≤ c) (hr : 0 ≤ r) (hpos : 0 < max |a₁| |a₂|) :
    volume ({p : ℝ × ℝ | p.1 ∈ Set.Icc (-b) b ∧ p.2 ∈ Set.Icc (-c) c ∧
                          |a₁ * p.1 + a₂ * p.2 - C| ≤ r}) ≤
      ENNReal.ofReal (4 * c * r / max |a₁| |a₂|) := by
  rcases le_total |a₁| |a₂| with h | h
  · rw [max_eq_right h] at hpos ⊢
    exact (volume_strip_inter_rectangle_le_of_b_ne_zero (abs_pos.mp hpos) hr hb hc).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hr) (abs_nonneg _)))
  · rw [max_eq_left h] at hpos ⊢
    exact volume_strip_inter_rectangle_le_of_a_ne_zero (abs_pos.mp hpos) hr hb hc

/-- Weighted 2D strip area bound for a rectangle `[-h,h] × [-h',h']`: the strip
`|a₁·y₁ + a₂·y₂ - C| ≤ r` has area at most `4·h·h'·r / max (|a₁|·h) (|a₂|·h')`.

Both branches are the unweighted bound in disguise: when the max is `|a₂|·h'` the bound
`4·h·r / |a₂|` from `volume_strip_inter_rectangle_le_of_b_ne_zero` is literally
`4·h·h'·r / (|a₂|·h')`, and symmetrically for `|a₁|·h`. -/
theorem volume_strip_inter_rectangle_le_max_weighted {a₁ a₂ C r h h' : ℝ} (hr : 0 ≤ r)
    (hh : 0 < h) (hh' : 0 < h') (hpos : 0 < max (|a₁| * h) (|a₂| * h')) :
    volume ({p : ℝ × ℝ | p.1 ∈ Set.Icc (-h) h ∧ p.2 ∈ Set.Icc (-h') h' ∧
                          |a₁ * p.1 + a₂ * p.2 - C| ≤ r}) ≤
      ENNReal.ofReal (4 * h * h' * r / max (|a₁| * h) (|a₂| * h')) := by
  have hne : h ≠ 0 := hh.ne'
  have hne' : h' ≠ 0 := hh'.ne'
  rcases le_total (|a₁| * h) (|a₂| * h') with hle | hle
  · rw [max_eq_right hle] at hpos ⊢
    have habs : |a₂| ≠ 0 := fun h0 => by simp [h0] at hpos
    refine (volume_strip_inter_rectangle_le_of_b_ne_zero (abs_ne_zero.mp habs) hr hh.le
      hh'.le).trans_eq (congrArg ENNReal.ofReal
        (by rw [show 4 * h * h' * r = 4 * h * r * h' from by ring,
          mul_div_mul_right _ _ hne']))
  · rw [max_eq_left hle] at hpos ⊢
    have habs : |a₁| ≠ 0 := fun h0 => by simp [h0] at hpos
    refine (volume_strip_inter_rectangle_le_of_a_ne_zero (abs_ne_zero.mp habs) hr hh.le
      hh'.le).trans_eq (congrArg ENNReal.ofReal
        (by rw [show 4 * h * h' * r = 4 * h' * r * h from by ring,
          mul_div_mul_right _ _ hne]))

/-- Slicing the symmetric three-dimensional box `[-t₀, t₀] × [-t₁, t₁] × [-t₂, t₂]` intersected
with a linear strip `|c₀ · y₀ + c₁ · y₁ + c₂ · y₂ - β| ≤ r` along the coordinate `i`: if every
two-dimensional slice (taken in the two remaining coordinates `j₀ = i.succAbove 0`,
`j₁ = i.succAbove 1`) has area at most `K`, then the whole set has volume at most `2 · s · K`,
where `s` is the half-width `tᵢ` of the sliced coordinate.

The data of the two surviving coordinates is passed as plain scalars — half-widths `u, u'` and
coefficients `d, d'`, together with the equations identifying them — so that a call site can hand
over an off-the-shelf two-dimensional estimate with no reindexing on its side. -/
theorem volume_box_inter_linear_strip_le_of_slice
    {t₀ t₁ t₂ c₀ c₁ c₂ β r K s u u' d d' : ℝ} {i j₀ j₁ : Fin 3}
    (hj₀ : i.succAbove 0 = j₀) (hj₁ : i.succAbove 1 = j₁)
    (hs : (![t₀, t₁, t₂] : Fin 3 → ℝ) i = s) (hs0 : 0 ≤ s)
    (hu : (![t₀, t₁, t₂] : Fin 3 → ℝ) j₀ = u) (hu' : (![t₀, t₁, t₂] : Fin 3 → ℝ) j₁ = u')
    (hd : (![c₀, c₁, c₂] : Fin 3 → ℝ) j₀ = d) (hd' : (![c₀, c₁, c₂] : Fin 3 → ℝ) j₁ = d')
    (hK : ∀ γ : ℝ, volume {p : ℝ × ℝ | p.1 ∈ Set.Icc (-u) u ∧ p.2 ∈ Set.Icc (-u') u' ∧
        |d * p.1 + d' * p.2 - γ| ≤ r} ≤ ENNReal.ofReal K) :
    volume ((Set.Icc (![-t₀, -t₁, -t₂] : Fin 3 → ℝ) ![t₀, t₁, t₂]) ∩
        {y : Fin 3 → ℝ | |c₀ * y 0 + c₁ * y 1 + c₂ * y 2 - β| ≤ r}) ≤
      ENNReal.ofReal (2 * s * K) := by
  subst hj₀ hj₁ hs hu hu' hd hd'
  rw [show (![-t₀, -t₁, -t₂] : Fin 3 → ℝ) = -![t₀, t₁, t₂] from by simp,
    show {y : Fin 3 → ℝ | |c₀ * y 0 + c₁ * y 1 + c₂ * y 2 - β| ≤ r} =
        {y : Fin 3 → ℝ | |∑ j, (![c₀, c₁, c₂] : Fin 3 → ℝ) j * y j - β| ≤ r} from by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]]
  set t : Fin 3 → ℝ := ![t₀, t₁, t₂]
  set co : Fin 3 → ℝ := ![c₀, c₁, c₂]
  set e : (Fin 3 → ℝ) ≃ᵐ ℝ × (Fin 2 → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i
  have hP := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) i
  set R : Set (ℝ × (Fin 2 → ℝ)) :=
    {p | p.1 ∈ Set.Icc (-t i) (t i) ∧
         p.2 0 ∈ Set.Icc (-t (i.succAbove 0)) (t (i.succAbove 0)) ∧
         p.2 1 ∈ Set.Icc (-t (i.succAbove 1)) (t (i.succAbove 1)) ∧
         |co (i.succAbove 0) * p.2 0 + co (i.succAbove 1) * p.2 1 - (β - co i * p.1)| ≤ r}
  have hsnd : ∀ k : Fin 2, Measurable fun p : ℝ × (Fin 2 → ℝ) => p.2 k :=
    fun k => (measurable_pi_apply k).comp measurable_snd
  have hR_meas : MeasurableSet R :=
    (measurable_fst measurableSet_Icc).inter ((hsnd 0 measurableSet_Icc).inter
      ((hsnd 1 measurableSet_Icc).inter (measurableSet_le
        ((((hsnd 0).const_mul _).add ((hsnd 1).const_mul _)).sub
          ((measurable_fst.const_mul _).const_sub _)).abs measurable_const)))
  have hB_subset : Set.Icc (-t) t ∩ {y : Fin 3 → ℝ | |∑ j, co j * y j - β| ≤ r} ⊆ e ⁻¹' R :=
    fun y hy => show (y i, fun j : Fin 2 => y (i.succAbove j)) ∈ R from
      ⟨⟨hy.1.1 i, hy.1.2 i⟩, ⟨hy.1.1 _, hy.1.2 _⟩, ⟨hy.1.1 _, hy.1.2 _⟩, by
        rw [show co (i.succAbove 0) * y (i.succAbove 0) + co (i.succAbove 1) * y (i.succAbove 1) -
            (β - co i * y i) = ∑ j, co j * y j - β from by
          rw [Fin.sum_univ_succAbove (fun j => co j * y j) i, Fin.sum_univ_two]; ring]
        exact hy.2⟩
  have hP₂ := volume_preserving_piFinTwo fun _ : Fin 2 => ℝ
  have h_slice : ∀ y₀, volume (Prod.mk y₀ ⁻¹' R) ≤
      (Set.Icc (-t i) (t i)).indicator (fun _ => ENNReal.ofReal K) y₀ := fun y₀ => by
    by_cases hy0 : y₀ ∈ Set.Icc (-t i) (t i)
    · rw [Set.indicator_of_mem hy0]
      refine (measure_mono ?_).trans ((hP₂.measure_preimage_emb
          (MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ).measurableEmbedding _).trans_le
        (hK (β - co i * y₀)))
      exact fun z hz => ⟨hz.2.1, hz.2.2.1, hz.2.2.2⟩
    · rw [Set.indicator_of_notMem hy0, show Prod.mk y₀ ⁻¹' R = ∅ from
        Set.eq_empty_iff_forall_notMem.mpr fun _ hp => hy0 hp.1, measure_empty]
  calc volume (Set.Icc (-t) t ∩ {y : Fin 3 → ℝ | |∑ j, co j * y j - β| ≤ r})
      ≤ volume R :=
        (measure_mono hB_subset).trans_eq (hP.measure_preimage_emb e.measurableEmbedding R)
    _ = ∫⁻ y₀, volume (Prod.mk y₀ ⁻¹' R) ∂(volume : Measure ℝ) := by
        rw [Measure.volume_eq_prod ℝ (Fin 2 → ℝ)]; exact Measure.prod_apply hR_meas
    _ ≤ _ := lintegral_mono h_slice
    _ = ENNReal.ofReal (2 * t i * K) := by
        rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc,
          ← ENNReal.ofReal_mul' (by linarith : (0 : ℝ) ≤ t i - -t i)]
        congr 1
        ring

/-- Volume of the symmetric box `[-t₀, t₀] × [-t₁, t₁] × [-t₂, t₂]` intersected with the linear
strip `|a₀·y₀ + a₁·y₁ + a₂·y₂ - β| ≤ r`, for `t₁ ≤ t₂`: slicing along the first coordinate and
applying `volume_strip_inter_rectangle_le_max` to each slice gives `8·t₀·t₂·r / max |a₁| |a₂|`. -/
theorem volume_box_inter_linear_strip_le_general {t₀ t₁ t₂ a₀ a₁ a₂ β r : ℝ}
    (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (ht : t₁ ≤ t₂) (hr : 0 ≤ r)
    (hpos : 0 < max |a₁| |a₂|) :
    volume ((Set.Icc (![-t₀, -t₁, -t₂] : Fin 3 → ℝ) ![t₀, t₁, t₂]) ∩
            {y : Fin 3 → ℝ | |a₀ * y 0 + a₁ * y 1 + a₂ * y 2 - β| ≤ r}) ≤
      ENNReal.ofReal (8 * t₀ * t₂ * r / max |a₁| |a₂|) := by
  refine (volume_box_inter_linear_strip_le_of_slice (i := 0) (j₀ := 1) (j₁ := 2)
    (s := t₀) (u := t₁) (u' := t₂) (d := a₁) (d' := a₂)
    (by decide) (by decide) rfl ht₀ rfl rfl rfl rfl
    fun γ => volume_strip_inter_rectangle_le_max (C := γ) ht₁ ht₂ ht hr hpos).trans_eq ?_
  congr 1
  ring

/-- Area bound for a strip in the unit square, using `b ≠ 0`. -/
theorem volume_strip_inter_unit_square_le_of_b_ne_zero
    {a b c r : ℝ} (hb : b ≠ 0) (hr : 0 ≤ r) :
    volume ({p : ℝ × ℝ | p.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ p.2 ∈ Set.Icc (-1 : ℝ) 1 ∧
                          |a * p.1 + b * p.2 - c| ≤ r}) ≤
      ENNReal.ofReal (4 * r / |b|) := by
  simpa using (volume_strip_inter_rectangle_le_of_b_ne_zero (a₁ := a) (a₂ := b) (C := c)
    (b := 1) (c := 1) hb hr (by norm_num) (by norm_num))

/-- Area bound for a strip in the unit square, using `a ≠ 0`. -/
theorem volume_strip_inter_unit_square_le_of_a_ne_zero
    {a b c r : ℝ} (ha : a ≠ 0) (hr : 0 ≤ r) :
    volume ({p : ℝ × ℝ | p.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ p.2 ∈ Set.Icc (-1 : ℝ) 1 ∧
                          |a * p.1 + b * p.2 - c| ≤ r}) ≤
      ENNReal.ofReal (4 * r / |a|) := by
  simpa using (volume_strip_inter_rectangle_le_of_a_ne_zero (a₁ := a) (a₂ := b) (C := c)
    (b := 1) (c := 1) ha hr (by norm_num) (by norm_num))

/-- Area bound for a strip in the unit square, controlled by `max |a₁| |a₂|`. -/
theorem volume_strip_inter_unit_square_le_max
    {a₁ a₂ c r : ℝ} (hr : 0 ≤ r) (hpos : 0 < max |a₁| |a₂|) :
    volume ({p : ℝ × ℝ | p.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ p.2 ∈ Set.Icc (-1 : ℝ) 1 ∧
                          |a₁ * p.1 + a₂ * p.2 - c| ≤ r}) ≤
      ENNReal.ofReal (4 * r / max |a₁| |a₂|) := by
  exact (volume_strip_inter_rectangle_le_max (a₁ := a₁) (a₂ := a₂) (C := c) (b := 1) (c := 1)
    (r := r) (by norm_num) (by norm_num) (by norm_num : (1 : ℝ) ≤ 1) hr hpos).trans_eq
    (congrArg ENNReal.ofReal (by ring))

/-- Volume of a three-dimensional box intersected with a linear strip. -/
theorem volume_box_inter_linear_strip_le
    {a₀ a₁ a₂ β d r : ℝ} (hd : 0 ≤ d) (hr : 0 ≤ r)
    (hpos : 0 < max |a₁| |a₂|) :
    volume ((Set.Icc (![-d, -1, -1] : Fin 3 → ℝ) ![d, 1, 1]) ∩
            {y : Fin 3 → ℝ | |a₀ * y 0 + a₁ * y 1 + a₂ * y 2 - β| ≤ r}) ≤
      ENNReal.ofReal (8 * d * r / max |a₁| |a₂|) := by
  exact (volume_box_inter_linear_strip_le_general (t₀ := d) (t₁ := 1) (t₂ := 1) hd
    (by norm_num) (by norm_num) le_rfl hr hpos).trans_eq
    (congrArg ENNReal.ofReal (by ring))

end MeasureTheory

end

end
