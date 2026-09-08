/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Analysis.EuclideanNet
public import Kakeya.Mathlib.Analysis.IsSeparated
public import Kakeya.Tube.Basic

/-!
# Separated nets and closeness of tubes

Elementary geometry of `δ`-tubes: maximal separated finsets, when two tubes with nearby endpoints
contain one another after a rescaling, and the `L¹`-box counting bound for a separated family.
None of it mentions uniformity or a chain of scales, and it is read from outside the tree
construction by the fibre and Katz–Tao bridges.
-/

@[expose] public section


open MeasureTheory Real

open scoped ENNReal NNReal

namespace Tube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Product-grid covering core.** If a `σ`-tube `U` and a `ρ`-tube `W` have
directions within `ε_dir` and midpoints within `ε_pos`, and the slack condition
`ε_pos + ε_dir/2 + σ ≤ ρ` holds, then `U.carrier ⊆ W.carrier` (factor-1
containment). This is the density-covering replacement for the false
`comparability_of_notED`. -/
theorem tube_carrier_subset_of_close
    {σ ρ : NNReal} (U : Tube σ E) (W : Tube ρ E)
    {ε_dir ε_pos : ℝ}
    (hdir : ‖U.direction - W.direction‖ ≤ ε_dir)
    (hmid : ‖U.midpoint - W.midpoint‖ ≤ ε_pos)
    (hcond : ε_pos + ε_dir / 2 + (σ : ℝ) ≤ (ρ : ℝ)) :
    U.carrier ⊆ W.carrier := by
  have hσ_nn : (0 : ℝ) ≤ (σ : ℝ) := σ.coe_nonneg
  have hε_dir_nn : 0 ≤ ε_dir := le_trans (norm_nonneg _) hdir
  have hε_pos_nn : 0 ≤ ε_pos := le_trans (norm_nonneg _) hmid
  have hgap_nn : (0 : ℝ) ≤ (ρ : ℝ) - (σ : ℝ) := by linarith
  have hUx : U.x = U.midpoint - (1/2 : ℝ) • U.direction := by
    simp only [Tube.midpoint, Tube.direction]; module
  have hUy : U.y = U.midpoint + (1/2 : ℝ) • U.direction := by
    simp only [Tube.midpoint, Tube.direction]; module
  have hWx : W.x = W.midpoint - (1/2 : ℝ) • W.direction := by
    simp only [Tube.midpoint, Tube.direction]; module
  have hWy : W.y = W.midpoint + (1/2 : ℝ) • W.direction := by
    simp only [Tube.midpoint, Tube.direction]; module
  have hstep1 : segment ℝ U.x U.y
      ⊆ Metric.cthickening ((ρ : ℝ) - (σ : ℝ)) (segment ℝ W.x W.y) := by
    intro p hp
    obtain ⟨a, b, ha, hb, hab, hpeq⟩ := hp
    refine Metric.mem_cthickening_of_dist_le p (a • W.x + b • W.y) _ _
      ⟨a, b, ha, hb, hab, rfl⟩ ?_
    rw [dist_eq_norm, ← hpeq]
    have hpq : a • U.x + b • U.y - (a • W.x + b • W.y)
        = (U.midpoint - W.midpoint) + (b - a) • ((1/2 : ℝ) • (U.direction - W.direction)) := by
      rw [hUx, hUy, hWx, hWy]
      have hab' : a = 1 - b := by linarith
      subst hab'
      module
    rw [hpq]
    refine (norm_add_le _ _).trans ?_
    have hba : |b - a| ≤ 1 := by
      rw [abs_le]; constructor <;> [nlinarith; nlinarith]
    have h2 : ‖(b - a) • ((1/2 : ℝ) • (U.direction - W.direction))‖ ≤ ε_dir / 2 := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have : |(1/2 : ℝ)| = 1/2 := by norm_num
      rw [this]
      calc |b - a| * (1/2 * ‖U.direction - W.direction‖)
          ≤ 1 * (1/2 * ε_dir) := by
            gcongr
        _ = ε_dir / 2 := by ring
    calc ‖U.midpoint - W.midpoint‖ + ‖(b - a) • ((1/2 : ℝ) • (U.direction - W.direction))‖
        ≤ ε_pos + ε_dir / 2 := by gcongr
      _ ≤ (ρ : ℝ) - (σ : ℝ) := by linarith
  rw [U.carrier_eq_cthickening, W.carrier_eq_cthickening]
  intro x hx
  have hmono : x ∈ Metric.cthickening (σ : ℝ)
      (Metric.cthickening ((ρ : ℝ) - (σ : ℝ)) (segment ℝ W.x W.y)) := by
    have h1 : Metric.infEDist x (Metric.cthickening ((ρ : ℝ) - (σ : ℝ)) (segment ℝ W.x W.y))
        ≤ Metric.infEDist x (segment ℝ U.x U.y) := Metric.infEDist_anti hstep1
    rw [Metric.mem_cthickening_iff] at hx ⊢
    exact le_trans h1 hx
  have hcomp : Metric.cthickening (σ : ℝ)
      (Metric.cthickening ((ρ : ℝ) - (σ : ℝ)) (segment ℝ W.x W.y))
      ⊆ Metric.cthickening (ρ : ℝ) (segment ℝ W.x W.y) := by
    refine (Metric.cthickening_cthickening_subset hσ_nn hgap_nn _).trans ?_
    rw [show (σ : ℝ) + ((ρ : ℝ) - (σ : ℝ)) = (ρ : ℝ) by ring]
  exact hcomp hmono

open Classical in
/-- **L1-box volume packing.** A finite family of index points whose two
coordinate images `fx`, `fy` are pairwise `r`-separated in the `L¹` product
metric (`r ≤ ‖fx a - fx b‖ + ‖fy a - fy b‖`) and lie in `R`-balls about fixed
centers has cardinality `≤ ((R + r/4)/(r/4))^(2n)`. -/
theorem card_le_of_L1_separated_in_box
    {α : Type*} (s : Finset α) (fx fy : α → E) (cx cy : E) {R r : ℝ}
    (hr : 0 < r)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ ‖fx a - fx b‖ + ‖fy a - fy b‖)
    (hinx : ∀ a ∈ s, ‖fx a - cx‖ ≤ R) (hiny : ∀ a ∈ s, ‖fy a - cy‖ ≤ R) :
    (s.card : ℝ) ≤ ((R + r/4) / (r/4)) ^ (2 * Module.finrank ℝ E) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hr4 : (0 : ℝ) < r / 4 := by linarith
  rcases s.eq_empty_or_nonempty with hempty | hne
  · rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact (even_two_mul _).pow_nonneg _
  obtain ⟨a0, ha0⟩ := hne
  have hR0 : (0 : ℝ) ≤ R := le_trans (norm_nonneg _) (hinx a0 ha0)
  have hRr4 : (0 : ℝ) < R + r / 4 := by linarith
  set u : ENNReal := volume (Metric.ball (0 : E) 1) with hu
  have hu_pos : u ≠ 0 := (Metric.measure_ball_pos volume _ zero_lt_one).ne'
  have hu_lt : u ≠ ∞ := MeasureTheory.measure_ball_ne_top
  set φ : α → Set (E × E) := fun a => Metric.ball (fx a) (r/4) ×ˢ Metric.ball (fy a) (r/4)
    with hφ
  have hdisj : (s : Set α).PairwiseDisjoint φ := by
    intro a ha b hb hab
    have hsep' := hsep a ha b hb hab
    have : r / 2 ≤ ‖fx a - fx b‖ ∨ r / 2 ≤ ‖fy a - fy b‖ := by
      by_contra h
      rw [not_or] at h
      obtain ⟨h1, h2⟩ := h
      rw [not_le] at h1 h2
      linarith
    rcases this with hx | hy
    · have hballdisj : Disjoint (Metric.ball (fx a) (r/4)) (Metric.ball (fx b) (r/4)) := by
        apply Metric.ball_disjoint_ball
        rw [dist_eq_norm]; linarith
      refine Disjoint.mono (Set.prod_subset_preimage_fst _ _) (Set.prod_subset_preimage_fst _ _) ?_
      exact (hballdisj.preimage Prod.fst)
    · have hballdisj : Disjoint (Metric.ball (fy a) (r/4)) (Metric.ball (fy b) (r/4)) := by
        apply Metric.ball_disjoint_ball
        rw [dist_eq_norm]; linarith
      refine Disjoint.mono (Set.prod_subset_preimage_snd _ _) (Set.prod_subset_preimage_snd _ _) ?_
      exact (hballdisj.preimage Prod.snd)
  have hmeas : ∀ a, MeasurableSet (φ a) :=
    fun a => (measurableSet_ball).prod (measurableSet_ball)
  have hvol_one : ∀ a, volume (φ a) = ENNReal.ofReal ((r/4) ^ n) ^ 2 * u ^ 2 := by
    intro a
    rw [hφ, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
      MeasureTheory.Measure.addHaar_ball volume _ hr4.le,
      MeasureTheory.Measure.addHaar_ball volume _ hr4.le, hn_def, hu]
    ring
  have hunion_vol : volume (⋃ a ∈ s, φ a)
      = (s.card : ENNReal) * (ENNReal.ofReal ((r/4) ^ n) ^ 2 * u ^ 2) := by
    rw [measure_biUnion_finset hdisj (fun a _ => hmeas a)]
    simp only [hvol_one, Finset.sum_const, nsmul_eq_mul]
  have hsub : (⋃ a ∈ s, φ a)
      ⊆ Metric.ball cx (R + r/4) ×ˢ Metric.ball cy (R + r/4) := by
    refine Set.iUnion₂_subset (fun a ha => ?_)
    rw [hφ]
    apply Set.prod_mono
    · refine Metric.ball_subset_ball' ?_
      have := hinx a ha; rw [dist_eq_norm]; linarith
    · refine Metric.ball_subset_ball' ?_
      have := hiny a ha; rw [dist_eq_norm]; linarith
  have hbox_vol : volume (Metric.ball cx (R + r/4) ×ˢ Metric.ball cy (R + r/4))
      = ENNReal.ofReal ((R + r/4) ^ n) ^ 2 * u ^ 2 := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
      MeasureTheory.Measure.addHaar_ball volume _ hRr4.le,
      MeasureTheory.Measure.addHaar_ball volume _ hRr4.le, hn_def, hu]
    ring
  have hle : (s.card : ENNReal) * (ENNReal.ofReal ((r/4) ^ n) ^ 2 * u ^ 2)
      ≤ ENNReal.ofReal ((R + r/4) ^ n) ^ 2 * u ^ 2 := by
    rw [← hunion_vol, ← hbox_vol]; exact measure_mono hsub
  have hu2_pos : u ^ 2 ≠ 0 := pow_ne_zero 2 hu_pos
  have hu2_lt : u ^ 2 ≠ ∞ := by
    rw [sq]; exact ENNReal.mul_ne_top hu_lt hu_lt
  have hle' : u ^ 2 * ((s.card : ENNReal) * ENNReal.ofReal ((r/4) ^ n) ^ 2)
      ≤ u ^ 2 * ENNReal.ofReal ((R + r/4) ^ n) ^ 2 := by
    rw [show u ^ 2 * ((s.card : ENNReal) * ENNReal.ofReal ((r/4) ^ n) ^ 2)
          = (s.card : ENNReal) * (ENNReal.ofReal ((r/4) ^ n) ^ 2 * u ^ 2) by ring,
        show u ^ 2 * ENNReal.ofReal ((R + r/4) ^ n) ^ 2
          = ENNReal.ofReal ((R + r/4) ^ n) ^ 2 * u ^ 2 by ring]
    exact hle
  have hle2 : (s.card : ENNReal) * ENNReal.ofReal ((r/4) ^ n) ^ 2
      ≤ ENNReal.ofReal ((R + r/4) ^ n) ^ 2 :=
    (ENNReal.mul_le_mul_iff_right hu2_pos hu2_lt).1 hle'
  have hofr : ENNReal.ofReal ((r/4) ^ n) ^ 2 = ENNReal.ofReal (((r/4) ^ n) ^ 2) := by
    rw [← ENNReal.ofReal_pow (by positivity)]
  have hofR : ENNReal.ofReal ((R + r/4) ^ n) ^ 2 = ENNReal.ofReal (((R + r/4) ^ n) ^ 2) := by
    rw [← ENNReal.ofReal_pow (by positivity)]
  rw [hofr, hofR] at hle2
  have hcard_nonneg : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
  have hpos2 : (0 : ℝ) ≤ ((r/4) ^ n) ^ 2 := by positivity
  have hpos3 : (0 : ℝ) ≤ ((R + r/4) ^ n) ^ 2 := by positivity
  have hreal : (s.card : ℝ) * ((r/4) ^ n) ^ 2 ≤ ((R + r/4) ^ n) ^ 2 := by
    have hlhs : (s.card : ENNReal) * ENNReal.ofReal (((r/4) ^ n) ^ 2)
        = ENNReal.ofReal ((s.card : ℝ) * ((r/4) ^ n) ^ 2) := by
      rw [ENNReal.ofReal_mul hcard_nonneg]; congr 1; exact (ENNReal.ofReal_natCast _).symm
    rw [hlhs] at hle2
    exact (ENNReal.ofReal_le_ofReal_iff hpos3).mp hle2
  have hden_pos : (0 : ℝ) < ((r/4) ^ n) ^ 2 := by positivity
  have : (s.card : ℝ) ≤ ((R + r/4) ^ n) ^ 2 / ((r/4) ^ n) ^ 2 := by
    rw [le_div_iff₀ hden_pos]; exact hreal
  calc (s.card : ℝ) ≤ ((R + r/4) ^ n) ^ 2 / ((r/4) ^ n) ^ 2 := this
    _ = (((R + r/4) ^ n) / ((r/4) ^ n)) ^ 2 := (div_pow _ _ _).symm
    _ = (((R + r/4) / (r/4)) ^ n) ^ 2 := by rw [← div_pow]
    _ = ((R + r/4) / (r/4)) ^ (2 * n) := by rw [← pow_mul, mul_comm n 2]

open Classical in
/-- **Rectangular L1 volume packing.** This is the two-radius form of
`Tube.card_le_of_L1_separated_in_box`: the first and second coordinates may range in balls of
different radii.  Keeping the two factors separate is what preserves an anisotropic gain. -/
theorem card_le_of_L1_separated_in_rectangle
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    {α : Type*} (s : Finset α) (fx fy : α → E) (cx cy : E) {Rx Ry r : ℝ}
    (hr : 0 < r) (hRx0 : 0 ≤ Rx) (hRy0 : 0 ≤ Ry)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r ≤ ‖fx a - fx b‖ + ‖fy a - fy b‖)
    (hinx : ∀ a ∈ s, ‖fx a - cx‖ ≤ Rx) (hiny : ∀ a ∈ s, ‖fy a - cy‖ ≤ Ry) :
    (s.card : ℝ) ≤
      ((Rx + r / 4) / (r / 4)) ^ Module.finrank ℝ E *
        ((Ry + r / 4) / (r / 4)) ^ Module.finrank ℝ E := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hr4 : (0 : ℝ) < r / 4 := by linarith
  rcases s.eq_empty_or_nonempty with hempty | hne
  · rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨a0, ha0⟩ := hne
  have hRxr4 : (0 : ℝ) < Rx + r / 4 := by linarith
  have hRyr4 : (0 : ℝ) < Ry + r / 4 := by linarith
  set u : ENNReal := volume (Metric.ball (0 : E) 1) with hu
  have hu_pos : u ≠ 0 := (Metric.measure_ball_pos volume _ zero_lt_one).ne'
  have hu_lt : u ≠ ∞ := MeasureTheory.measure_ball_ne_top
  set φ : α → Set (E × E) := fun a ↦
    Metric.ball (fx a) (r / 4) ×ˢ Metric.ball (fy a) (r / 4) with hφ
  have hdisj : (s : Set α).PairwiseDisjoint φ := by
    intro a ha b hb hab
    have hsep' := hsep a ha b hb hab
    have hcoord : r / 2 ≤ ‖fx a - fx b‖ ∨ r / 2 ≤ ‖fy a - fy b‖ := by
      by_contra h
      rw [not_or] at h
      obtain ⟨h1, h2⟩ := h
      rw [not_le] at h1 h2
      linarith
    rcases hcoord with hx | hy
    · have hd : Disjoint (Metric.ball (fx a) (r / 4)) (Metric.ball (fx b) (r / 4)) := by
        apply Metric.ball_disjoint_ball
        rw [dist_eq_norm]
        linarith
      refine Disjoint.mono (Set.prod_subset_preimage_fst _ _)
        (Set.prod_subset_preimage_fst _ _) (hd.preimage Prod.fst)
    · have hd : Disjoint (Metric.ball (fy a) (r / 4)) (Metric.ball (fy b) (r / 4)) := by
        apply Metric.ball_disjoint_ball
        rw [dist_eq_norm]
        linarith
      refine Disjoint.mono (Set.prod_subset_preimage_snd _ _)
        (Set.prod_subset_preimage_snd _ _) (hd.preimage Prod.snd)
  have hmeas : ∀ a, MeasurableSet (φ a) :=
    fun a ↦ measurableSet_ball.prod measurableSet_ball
  have hvol_one : ∀ a, volume (φ a) = ENNReal.ofReal ((r / 4) ^ n) ^ 2 * u ^ 2 := by
    intro a
    rw [hφ, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
      MeasureTheory.Measure.addHaar_ball volume _ hr4.le,
      MeasureTheory.Measure.addHaar_ball volume _ hr4.le, hn_def, hu]
    ring
  have hunion_vol : volume (⋃ a ∈ s, φ a) =
      (s.card : ENNReal) * (ENNReal.ofReal ((r / 4) ^ n) ^ 2 * u ^ 2) := by
    rw [measure_biUnion_finset hdisj (fun a _ ↦ hmeas a)]
    simp only [hvol_one, Finset.sum_const, nsmul_eq_mul]
  have hsub : (⋃ a ∈ s, φ a) ⊆
      Metric.ball cx (Rx + r / 4) ×ˢ Metric.ball cy (Ry + r / 4) := by
    refine Set.iUnion₂_subset (fun a ha ↦ ?_)
    rw [hφ]
    apply Set.prod_mono
    · refine Metric.ball_subset_ball' ?_
      have := hinx a ha
      rw [dist_eq_norm]
      linarith
    · refine Metric.ball_subset_ball' ?_
      have := hiny a ha
      rw [dist_eq_norm]
      linarith
  have hbox_vol : volume
      (Metric.ball cx (Rx + r / 4) ×ˢ Metric.ball cy (Ry + r / 4)) =
        ENNReal.ofReal ((Rx + r / 4) ^ n) * ENNReal.ofReal ((Ry + r / 4) ^ n) * u ^ 2 := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
      MeasureTheory.Measure.addHaar_ball volume _ hRxr4.le,
      MeasureTheory.Measure.addHaar_ball volume _ hRyr4.le, hn_def, hu]
    ring
  have hle : (s.card : ENNReal) * (ENNReal.ofReal ((r / 4) ^ n) ^ 2 * u ^ 2) ≤
      ENNReal.ofReal ((Rx + r / 4) ^ n) * ENNReal.ofReal ((Ry + r / 4) ^ n) * u ^ 2 := by
    rw [← hunion_vol, ← hbox_vol]
    exact measure_mono hsub
  have hu2_pos : u ^ 2 ≠ 0 := pow_ne_zero 2 hu_pos
  have hu2_lt : u ^ 2 ≠ ∞ := by
    rw [sq]
    exact ENNReal.mul_ne_top hu_lt hu_lt
  have hle' : (s.card : ENNReal) * ENNReal.ofReal ((r / 4) ^ n) ^ 2 ≤
      ENNReal.ofReal ((Rx + r / 4) ^ n) * ENNReal.ofReal ((Ry + r / 4) ^ n) := by
    apply (ENNReal.mul_le_mul_iff_right hu2_pos hu2_lt).1
    simpa [mul_assoc, mul_left_comm, mul_comm] using hle
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ (r / 4) ^ n)] at hle'
  have hsmall0 : 0 ≤ ((r / 4) ^ n) ^ 2 := by positivity
  have hlarge0 : 0 ≤ (Rx + r / 4) ^ n * (Ry + r / 4) ^ n := by positivity
  have hcard_nonneg : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
  have hreal : (s.card : ℝ) * ((r / 4) ^ n) ^ 2 ≤
      (Rx + r / 4) ^ n * (Ry + r / 4) ^ n := by
    have hlhs : (s.card : ENNReal) * ENNReal.ofReal (((r / 4) ^ n) ^ 2) =
        ENNReal.ofReal ((s.card : ℝ) * ((r / 4) ^ n) ^ 2) := by
      rw [ENNReal.ofReal_mul hcard_nonneg]
      congr 1
      exact (ENNReal.ofReal_natCast _).symm
    have hrhs : ENNReal.ofReal ((Rx + r / 4) ^ n) *
        ENNReal.ofReal ((Ry + r / 4) ^ n) =
          ENNReal.ofReal ((Rx + r / 4) ^ n * (Ry + r / 4) ^ n) := by
      rw [ENNReal.ofReal_mul]
      positivity
    rw [hlhs, hrhs] at hle'
    exact (ENNReal.ofReal_le_ofReal_iff hlarge0).mp hle'
  have hden_pos : (0 : ℝ) < ((r / 4) ^ n) ^ 2 := by positivity
  calc
    (s.card : ℝ) ≤
        ((Rx + r / 4) ^ n * (Ry + r / 4) ^ n) / ((r / 4) ^ n) ^ 2 := by
      rw [le_div_iff₀ hden_pos]
      exact hreal
    _ = ((Rx + r / 4) ^ n / (r / 4) ^ n) *
        ((Ry + r / 4) ^ n / (r / 4) ^ n) := by
      field_simp [pow_ne_zero n (ne_of_gt hr4)]
    _ = ((Rx + r / 4) / (r / 4)) ^ n * ((Ry + r / 4) / (r / 4)) ^ n := by
      rw [div_pow, div_pow]
      congr 2 <;> rw [← div_pow]
      exact (div_pow _ _ _).symm

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- **Endpoint localization (longitudinal lock).** If unit segment `[a,b]` lies
within Hausdorff distance `ρ` of unit segment `[c,d]` (one-sided), then their
endpoints correspond up to `3ρ`, in one of the two orientations. -/
private theorem seg_endpoints_close {a b c d : E} (hab : ‖b - a‖ = 1) (hcd : ‖d - c‖ = 1)
    {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (hclose : ∀ p ∈ segment ℝ a b, ∃ q ∈ segment ℝ c d, dist p q ≤ ρ) :
    (‖a - c‖ ≤ 3 * ρ ∧ ‖b - d‖ ≤ 3 * ρ) ∨ (‖a - d‖ ≤ 3 * ρ ∧ ‖b - c‖ ≤ 3 * ρ) := by
  obtain ⟨pa, hpa_mem, hpa_le⟩ := hclose a (left_mem_segment ℝ a b)
  obtain ⟨pb, hpb_mem, hpb_le⟩ := hclose b (right_mem_segment ℝ a b)
  rw [segment_eq_image] at hpa_mem hpb_mem
  obtain ⟨s, hs_mem, hs_eq⟩ := hpa_mem
  obtain ⟨t, ht_mem, ht_eq⟩ := hpb_mem
  obtain ⟨hs0, hs1⟩ := hs_mem
  obtain ⟨ht0, ht1⟩ := ht_mem
  have hpa_eq : pa = (1 - s) • c + s • d := hs_eq.symm
  have hpb_eq : pb = (1 - t) • c + t • d := ht_eq.symm
  have hpa_norm : ‖a - pa‖ ≤ ρ := by rw [← dist_eq_norm]; exact hpa_le
  have hpb_norm : ‖b - pb‖ ≤ ρ := by rw [← dist_eq_norm]; exact hpb_le
  have hgap : 1 - 2 * ρ ≤ |t - s| := by
    have hps_pt : pa - pb = (s - t) • (d - c) := by rw [hpa_eq, hpb_eq]; module
    have hnorm_ps_pt : ‖pa - pb‖ = |t - s| := by
      rw [hps_pt, norm_smul, Real.norm_eq_abs, hcd, mul_one, abs_sub_comm]
    have htri : ‖b - a‖ ≤ ‖b - pb‖ + ‖pb - pa‖ + ‖pa - a‖ := by
      calc ‖b - a‖ = ‖(b - pb) + (pb - pa) + (pa - a)‖ := by congr 1; abel
        _ ≤ ‖b - pb‖ + ‖pb - pa‖ + ‖pa - a‖ := by
            apply (norm_add_le _ _).trans; gcongr; exact norm_add_le _ _
    rw [hab] at htri
    rw [norm_sub_rev pb pa, norm_sub_rev pa a, hnorm_ps_pt] at htri
    linarith [htri, hpa_norm, hpb_norm]
  have ha_c : ‖a - c‖ ≤ s + ρ := by
    have hac : a - c = (a - pa) + s • (d - c) := by rw [hpa_eq]; module
    rw [hac]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, hcd, mul_one, abs_of_nonneg hs0]
    linarith
  have ha_d : ‖a - d‖ ≤ (1 - s) + ρ := by
    have had : a - d = (a - pa) + (1 - s) • (c - d) := by rw [hpa_eq]; module
    rw [had]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, norm_sub_rev c d, hcd, mul_one,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s)]
    linarith
  have hb_c : ‖b - c‖ ≤ t + ρ := by
    have hbc : b - c = (b - pb) + t • (d - c) := by rw [hpb_eq]; module
    rw [hbc]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, hcd, mul_one, abs_of_nonneg ht0]
    linarith
  have hb_d : ‖b - d‖ ≤ (1 - t) + ρ := by
    have hbd : b - d = (b - pb) + (1 - t) • (c - d) := by rw [hpb_eq]; module
    rw [hbd]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, norm_sub_rev c d, hcd, mul_one,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
    linarith
  rcases abs_cases (t - s) with ⟨heq, hsign⟩ | ⟨heq, hsign⟩
  · left
    rw [heq] at hgap
    constructor
    · have : s ≤ 2 * ρ := by linarith
      linarith [ha_c]
    · have : 1 - t ≤ 2 * ρ := by linarith
      linarith [hb_d]
  · right
    rw [heq] at hgap
    constructor
    · have : 1 - s ≤ 2 * ρ := by linarith
      linarith [ha_d]
    · have : t ≤ 2 * ρ := by linarith
      linarith [hb_c]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Tube-level endpoint localization: if a `δ'`-tube `A` sits (in the body order)
inside an `s`-tube `B`, then their endpoints correspond up to `3·s`, in one of the
two orientations. -/
theorem endpoints_close_of_body_le {δ' s : NNReal} (A : Tube δ' E) (B : Tube s E)
    (hAB : A.toConvexSpaceBody ≤ B.toConvexSpaceBody) :
    (‖A.x - B.x‖ ≤ 3 * (s : ℝ) ∧ ‖A.y - B.y‖ ≤ 3 * (s : ℝ)) ∨
    (‖A.x - B.y‖ ≤ 3 * (s : ℝ) ∧ ‖A.y - B.x‖ ≤ 3 * (s : ℝ)) := by
  have hA_unit : ‖A.y - A.x‖ = 1 := A.norm_direction
  have hB_unit : ‖B.y - B.x‖ = 1 := B.norm_direction
  have hs_nn : (0 : ℝ) ≤ (s : ℝ) := s.coe_nonneg
  have hB_carrier : B.carrier = Metric.cthickening (s : ℝ) (segment ℝ B.x B.y) :=
    B.carrier_eq_cthickening
  have hA_carrier : A.carrier = Metric.cthickening (δ' : ℝ) (segment ℝ A.x A.y) :=
    A.carrier_eq_cthickening
  have hclose : ∀ p ∈ segment ℝ A.x A.y,
      ∃ q ∈ segment ℝ B.x B.y, dist p q ≤ (s : ℝ) := by
    intro p hp
    have hp_carrier : p ∈ A.carrier := by
      rw [hA_carrier]; exact Metric.self_subset_cthickening _ hp
    have hp_out : p ∈ B.carrier := hAB hp_carrier
    rw [hB_carrier, Metric.mem_cthickening_iff] at hp_out
    obtain ⟨q, hq_mem, hq_dist⟩ :=
      isCompact_segment.exists_infDist_eq_dist ⟨B.x, left_mem_segment ℝ _ _⟩ p
    refine ⟨q, hq_mem, ?_⟩
    rw [← hq_dist]
    have hid : Metric.infDist p (segment ℝ B.x B.y)
        = (Metric.infEDist p (segment ℝ B.x B.y)).toReal := rfl
    rw [hid]
    calc (Metric.infEDist p (segment ℝ B.x B.y)).toReal
        ≤ (ENNReal.ofReal (s : ℝ)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hp_out
      _ = (s : ℝ) := ENNReal.toReal_ofReal hs_nn
  have hkey := seg_endpoints_close (a := A.x) (b := A.y) (c := B.x) (d := B.y)
    hA_unit hB_unit hs_nn hclose
  exact hkey

/-- **Consecutive scale gap.** From the ratio bound `δ^(1/M) ≤ 1/2` (`delta_rpow_inv_le_half`), the
consecutive multiscale radii satisfy `2·ρ_{k+1} ≤ ρ_k` for `ρ_k = δ^(k/M)` — the gap the chain needs
to nest/cover one level by the next coarser. -/
theorem rho_scale_gap {δ : NNReal} (hδ : 0 < δ) {M : ℕ} (_hM : 0 < M)
    (hhalf : (δ : ℝ) ^ ((1 : ℝ) / (M : ℝ)) ≤ 1 / 2) (k : ℕ) :
    2 * ((δ : ℝ) ^ (((k : ℝ) + 1) / (M : ℝ))) ≤ (δ : ℝ) ^ ((k : ℝ) / (M : ℝ)) := by
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hexp : ((k : ℝ) + 1) / (M : ℝ) = (k : ℝ) / (M : ℝ) + (1 : ℝ) / (M : ℝ) := by ring
  rw [hexp, Real.rpow_add hδr]
  have hpos : (0 : ℝ) < (δ : ℝ) ^ ((k : ℝ) / (M : ℝ)) := Real.rpow_pos_of_pos hδr _
  nlinarith [mul_nonneg hpos.le (by linarith [hhalf] :
    (0 : ℝ) ≤ 1 / 2 - (δ : ℝ) ^ ((1 : ℝ) / (M : ℝ)))]

omit [ProperSpace E] in
/-- **Separated direction net.** A maximal `ε`-separated subset of the covering direction net
`EuclideanNet.exists_sphere_net` is still a `2ε`-cover of the sphere (maximality), AND
`ε`-separated. -/
theorem sphere_sep_net {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : Finset E, (∀ d ∈ D, ‖d‖ = 1) ∧
      (∀ a ∈ D, ∀ b ∈ D, a ≠ b → ε ≤ ‖a - b‖) ∧
      (∀ u : E, ‖u‖ = 1 → ∃ d ∈ D, ‖u - d‖ ≤ 2 * ε) := by
  obtain ⟨D₀, hD₀_unit, _, hD₀_cover⟩ :=
    Kakeya.EuclideanNet.exists_sphere_net (E := E) hε hε1
  obtain ⟨D, hD_sub, hD_sep, hD_cover⟩ :=
    exists_maximal_separated_finset D₀ (fun a b => ‖a - b‖)
      (fun a => by simp only [sub_self, norm_zero]; exact hε) (fun a b => norm_sub_rev a b)
  refine ⟨D, fun d hd => hD₀_unit d (hD_sub hd), hD_sep, ?_⟩
  intro u hu
  obtain ⟨d₀, hd₀_mem, hd₀_close⟩ := hD₀_cover u hu
  obtain ⟨d, hd_mem, hd_close⟩ := hD_cover d₀ hd₀_mem
  refine ⟨d, hd_mem, ?_⟩
  calc ‖u - d‖ ≤ ‖u - d₀‖ + ‖d₀ - d‖ := norm_sub_le_norm_sub_add_norm_sub u d₀ d
    _ ≤ ε + ε := by
        have h1 : ‖u - d₀‖ ≤ ε := by rw [norm_sub_rev]; exact hd₀_close
        have h2 : ‖d₀ - d‖ ≤ ε := le_of_lt hd_close
        linarith
    _ = 2 * ε := by ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
  [BorelSpace E] in
/-- **Separated midpoint net (self-covering `B_3`).** A maximal `ε`-separated subset of a finite
`ε`-net of `B_3` *contained in* `B_3` (`Metric.finite_approx_of_totallyBounded`) is a `2ε`-cover of
`B_3` (by maximality), `ε`-separated, and stays in `B_3`. Crucially the net points (= grid-tube
midpoints) lie in the SAME ball they cover, so the cover ball equals the midpoint-localization ball
and the per-scale nets nest at a fixed ball. -/
theorem midpoint_sep_net {ε : ℝ} (hε : 0 < ε) :
    ∃ Pm : Finset E, (∀ p ∈ Pm, p ∈ Metric.closedBall (0 : E) 3) ∧
      (∀ a ∈ Pm, ∀ b ∈ Pm, a ≠ b → ε ≤ ‖a - b‖) ∧
      (∀ m : E, m ∈ Metric.closedBall (0 : E) 3 → ∃ p ∈ Pm, ‖m - p‖ ≤ 2 * ε) := by
  classical
  have htb : TotallyBounded (Metric.closedBall (0 : E) 3) :=
    (isCompact_closedBall (0 : E) 3).totallyBounded
  obtain ⟨t, ht_sub, ht_fin, ht_cover⟩ := Metric.finite_approx_of_totallyBounded htb ε hε
  set tF : Finset E := ht_fin.toFinset with htF
  obtain ⟨Pm, hPm_sub, hPm_sep, hPm_cover⟩ :=
    exists_maximal_separated_finset tF (fun a b => ‖a - b‖)
      (fun a => by simp only [sub_self, norm_zero]; exact hε) (fun a b => norm_sub_rev a b)
  refine ⟨Pm, ?_, hPm_sep, ?_⟩
  · intro p hp
    have hp_t : p ∈ tF := hPm_sub hp
    rw [htF, Set.Finite.mem_toFinset] at hp_t
    exact ht_sub hp_t
  · intro m hm
    obtain ⟨y, hy_mem, hy_ball⟩ := Set.mem_iUnion₂.mp (ht_cover hm)
    have hyF : y ∈ tF := by rw [htF, Set.Finite.mem_toFinset]; exact hy_mem
    obtain ⟨p, hp_mem, hp_close⟩ := hPm_cover y hyF
    refine ⟨p, hp_mem, ?_⟩
    have hmy : ‖m - y‖ < ε := by rwa [Metric.mem_ball, dist_eq_norm] at hy_ball
    calc ‖m - p‖ ≤ ‖m - y‖ + ‖y - p‖ := norm_sub_le_norm_sub_add_norm_sub m y p
      _ ≤ ε + ε := by linarith [le_of_lt hp_close, le_of_lt hmy]
      _ = 2 * ε := by ring

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Containment in a representative's rescale.**  If a `σ`-tube `U` has midpoint and direction
within `a` and `b` of a `τ`-tube `W`, and `a + b/2 + σ ≤ r`, then `U` lies in the `r`-rescale of
`W`.  Geometric core of the "parent = rescale of a representative leaf" strengthening. -/
theorem tube_le_rescale_of_close {σ τ : NNReal} (U : Tube σ E) (W : Tube τ E)
    {a b : ℝ} {r : NNReal}
    (hmid : ‖U.midpoint - W.midpoint‖ ≤ a) (hdir : ‖U.direction - W.direction‖ ≤ b)
    (hcond : a + b / 2 + (σ : ℝ) ≤ (r : ℝ)) :
    U.toConvexSpaceBody ≤ (W.rescale r).toConvexSpaceBody := by
  have hmideq : (W.rescale r).midpoint = W.midpoint := by
    simp only [Tube.rescale, Tube.midpoint, Tube.mk'_x, Tube.mk'_y]
  have hdireq : (W.rescale r).direction = W.direction := by
    simp only [Tube.rescale, Tube.direction, Tube.mk'_x, Tube.mk'_y]
  have hmid' : ‖U.midpoint - (W.rescale r).midpoint‖ ≤ a := by rw [hmideq]; exact hmid
  have hdir' : ‖U.direction - (W.rescale r).direction‖ ≤ b := by rw [hdireq]; exact hdir
  exact Tube.tube_carrier_subset_of_close U (W.rescale r) (ε_dir := b) (ε_pos := a)
    hdir' hmid' hcond

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Prefix-offset chain nesting.**  A child tube `c` sitting (in the body order) inside a parent
`P` of scale `σcs`, fattened to `ρsucc` and then translated by a vector of norm at most `t`, still
lies inside `P` fattened to `ρcs`, as soon as `σcs + ρsucc + t ≤ ρcs`.  This is what lets the
translated hierarchy of GWZ Lemma 7.5 be indexed by *cumulative prefix offsets*. -/
theorem translate_rescale_le_rescale_of_body_le
    {σsucc σcs ρsucc ρcs : NNReal} (c : Tube σsucc E) (P : Tube σcs E)
    (hle : c.toConvexSpaceBody ≤ P.toConvexSpaceBody)
    (v : E) {t : ℝ} (ht : 0 ≤ t) (hv : ‖v‖ ≤ t)
    (hbudget : (σcs : ℝ) + (ρsucc : ℝ) + t ≤ (ρcs : ℝ)) :
    ((c.rescale ρsucc).translate v).toConvexSpaceBody
      ≤ (P.rescale ρcs).toConvexSpaceBody := by
  have hle' : (c.rescale ρsucc).toConvexSpaceBody
      ≤ (P.rescale (σcs + ρsucc)).toConvexSpaceBody := by
    apply SetLike.coe_subset_coe.mp
    calc
      (c.rescale ρsucc).carrier = Metric.cthickening (ρsucc : ℝ)
            (segment ℝ (c.rescale ρsucc).x (c.rescale ρsucc).y) := by
        rw [(c.rescale ρsucc).carrier_eq_cthickening]
      _ = Metric.cthickening (ρsucc : ℝ) (segment ℝ c.x c.y) := by simp [Tube.rescale]
      _ ⊆ Metric.cthickening (ρsucc : ℝ) P.carrier :=
        Metric.cthickening_subset_of_subset (ρsucc : ℝ) (by
          have hseg_c : segment ℝ c.x c.y ⊆ c.carrier := by
            rw [c.carrier_eq_cthickening]
            exact Metric.self_subset_cthickening _
          have h_carrier_sub : c.carrier ⊆ P.carrier := SetLike.coe_subset_coe.mpr hle
          exact hseg_c.trans h_carrier_sub)
      _ = (P.rescale (σcs + ρsucc)).carrier := by rw [P.cthickening_carrier ρsucc]
  have hcarrier : ((c.rescale ρsucc).translate v).carrier ⊆ (P.rescale ρcs).carrier := by
    intro x hx
    have htranslate_carrier : ((c.rescale ρsucc).translate v).carrier =
        (v + ·) '' (c.rescale ρsucc).carrier := by
      unfold Tube.translate; rfl
    rw [htranslate_carrier] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy_in_T : y ∈ (P.rescale (σcs + ρsucc)).carrier := by
      have hcarrier_le' : (c.rescale ρsucc).carrier ⊆ (P.rescale (σcs + ρsucc)).carrier :=
        SetLike.coe_subset_coe.mpr hle'
      exact hcarrier_le' hy
    have h_mem_cthick : v + y ∈ Metric.cthickening t ((P.rescale (σcs + ρsucc)).carrier) := by
      rw [Metric.mem_cthickening_iff]
      calc
        Metric.infEDist (v + y) ((P.rescale (σcs + ρsucc)).carrier) ≤ edist (v + y) y :=
          Metric.infEDist_le_edist_of_mem hy_in_T
        _ = ‖v‖ₑ := by simp [edist_dist, dist_eq_norm]
        _ = ENNReal.ofReal ‖v‖ := by simp
        _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal hv
    have hτ_le_r : (σcs + ρsucc : NNReal) ≤ ρcs := by
      have hτr : ((σcs + ρsucc : NNReal) : ℝ) ≤ (ρcs : ℝ) := by
        push_cast; linarith
      exact_mod_cast hτr
    have ht_le : t ≤ (ρcs : ℝ) - ((σcs + ρsucc : NNReal) : ℝ) := by
      push_cast; linarith
    have h_cthick_mono : Metric.cthickening t ((P.rescale (σcs + ρsucc)).carrier) ⊆
        Metric.cthickening ((ρcs : ℝ) - ((σcs + ρsucc : NNReal) : ℝ))
          ((P.rescale (σcs + ρsucc)).carrier) :=
      Metric.cthickening_mono ht_le _
    have h_mem_cthick2 : v + y ∈ Metric.cthickening ((ρcs : ℝ) - ((σcs + ρsucc : NNReal) : ℝ))
        ((P.rescale (σcs + ρsucc)).carrier) := h_cthick_mono h_mem_cthick
    have h_carrier_eq : (P.rescale ρcs).carrier = Metric.cthickening
        ((ρcs : ℝ) - ((σcs + ρsucc : NNReal) : ℝ)) ((P.rescale (σcs + ρsucc)).carrier) := by
      have hbody_eq := (P.rescale (σcs + ρsucc)).toConvexBody_cthickening_sub hτ_le_r
      calc
        (P.rescale ρcs).carrier = ((P.rescale ρcs).toConvexSpaceBody : Set E) := rfl
        _ = (((P.rescale (σcs + ρsucc)).rescale ρcs).toConvexSpaceBody : Set E) := by
            simp [Tube.rescale]
        _ = ((P.rescale (σcs + ρsucc)).toConvexSpaceBody.cthickening
            ((ρcs : ℝ) - ((σcs + ρsucc : NNReal) : ℝ)) : Set E) := by rw [hbody_eq.symm]
        _ = Metric.cthickening ((ρcs : ℝ) - ((σcs + ρsucc : NNReal) : ℝ))
            ((P.rescale (σcs + ρsucc)).carrier) := rfl
    rw [h_carrier_eq]
    exact h_mem_cthick2
  exact SetLike.coe_subset_coe.mp hcarrier

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Sharp prefix-offset nesting.**  A child tube `c` sitting (in the body order) inside a parent
`P` of scale `τ`, then translated by a vector of norm at most `t`, still lies inside `P` fattened to
any `r` with `τ + t ≤ r`.  The sharp form of `translate_rescale_le_rescale_of_body_le`, whose
`8 * σcs` budget is too lossy to keep the fattened parents nested across consecutive scales. -/
theorem translate_le_rescale_of_body_le
    {σ τ r : NNReal} (c : Tube σ E) (P : Tube τ E)
    (hle : c.toConvexSpaceBody ≤ P.toConvexSpaceBody)
    (v : E) {t : ℝ} (ht : 0 ≤ t) (hv : ‖v‖ ≤ t)
    (hbudget : (τ : ℝ) + t ≤ (r : ℝ)) :
    ((c.translate v).toConvexSpaceBody) ≤ (P.rescale r).toConvexSpaceBody := by
  apply SetLike.coe_subset_coe.mp
  intro x hx
  have htranslate_carrier : (c.translate v).carrier = (v + ·) '' c.carrier := by
    unfold Tube.translate
    rfl
  have hx_carrier : x ∈ (c.translate v).carrier := hx
  rw [htranslate_carrier] at hx_carrier
  obtain ⟨y, hy, rfl⟩ := hx_carrier
  have h_carrier_sub : c.carrier ⊆ P.carrier := SetLike.coe_subset_coe.mpr hle
  have hy_P : y ∈ P.carrier := h_carrier_sub hy
  have h_mem_cthick : v + y ∈ Metric.cthickening t P.carrier := by
    rw [Metric.mem_cthickening_iff]
    calc
      Metric.infEDist (v + y) P.carrier ≤ edist (v + y) y :=
        Metric.infEDist_le_edist_of_mem hy_P
      _ = ‖v‖ₑ := by
        simp [edist_dist, dist_eq_norm]
      _ = ENNReal.ofReal ‖v‖ := by simp
      _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal hv
  have hτ_le_r : τ ≤ r := by
    have hτr : (τ : ℝ) ≤ (r : ℝ) := by linarith
    exact_mod_cast hτr
  have ht_le : t ≤ (r : ℝ) - (τ : ℝ) := by linarith
  have h_cthick_mono : Metric.cthickening t P.carrier ⊆
      Metric.cthickening ((r : ℝ) - (τ : ℝ)) P.carrier :=
    Metric.cthickening_mono ht_le P.carrier
  have h_mem_cthick2 : v + y ∈ Metric.cthickening ((r : ℝ) - (τ : ℝ)) P.carrier :=
    h_cthick_mono h_mem_cthick
  have h_carrier_eq : (P.rescale r).carrier = Metric.cthickening ((r : ℝ) - (τ : ℝ)) P.carrier := by
    have hbody_eq := P.toConvexBody_cthickening_sub hτ_le_r
    calc
      (P.rescale r).carrier = ((P.rescale r).toConvexSpaceBody : Set E) := rfl
      _ = (P.toConvexSpaceBody.cthickening ((r : ℝ) - (τ : ℝ)) : Set E) := by rw [hbody_eq]
      _ = Metric.cthickening ((r : ℝ) - (τ : ℝ)) P.carrier := rfl
  change v + y ∈ (P.rescale r).carrier
  rw [h_carrier_eq]
  exact h_mem_cthick2

end Tube
