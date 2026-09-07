import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.SlopeRescaling
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Combined mass and slope selection

Select a subinterval [c,d] of [a,b] of length (b-a)/50 that both
has at least 1/50 of the shaded mass and has the derivative
bracketed between m and 2m (for nonsingular rescaling).
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/--
Combined mass and slope selection from interval-local derivative data.

Given `[a,b]` with `|g'| ≥ b-a`, an upper bound by one, a one-Lipschitz
absolute derivative, and a lower bound on shaded mass, select `[c,d]` of
length `(b-a)/50` that has at least `1/50` of the mass and on which
`|g'|` is bracketed between `m` and `2m`.

This formulation deliberately does not require a globally bundled
`SlopeFunction`: the Proposition 6.5 source is only `C²` on `[-1,1]`.
-/
lemma mass_slope_selection_tight_of_local
    {δ : ℝ} {F : Kakeya.Streamlined.BodyFamily}
    (g : ℝ → ℝ)
    {a b : ℝ} (hab : a < b)
    (h_cont_abs : ContinuousOn (fun z => |deriv g z|) (Set.Icc a b))
    (h_abs_lipschitz :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |(|deriv g x| - |deriv g y|)| ≤ |x - y|)
    (h_low : ∀ z ∈ Set.Icc a b, b - a ≤ |deriv g z|)
    (h_high : ∀ z ∈ Set.Icc a b, |deriv g z| ≤ 1)
    (Y : Kakeya.Streamlined.Shading F)
    {theta : ℝ}
    (hmass : Kakeya.realRpowENN δ theta * ENNReal.ofReal (b - a) ≤
              shadedMassInSlab Y a b) :
    ∃ c d : ℝ,
      a ≤ c ∧ c < d ∧ d ≤ b ∧
      d - c = (b - a) / 50 ∧
      (∃ m : ℝ, 0 < m ∧ b - a ≤ m ∧ m ≤ 1 ∧
        (∀ z ∈ Set.Icc c d, m ≤ |deriv g z| ∧ |deriv g z| ≤ 2 * m) ∧
        (∀ z ∈ Set.Icc c d, |deriv g z| ≤ m + (b - a) / 50)) ∧
      shadedMassInSlab Y a b / 50 ≤
        shadedMassInSlab Y c d ∧
      Kakeya.realRpowENN δ theta * ENNReal.ofReal (b - a) / 50 ≤
        shadedMassInSlab Y c d := by
  let L : ℝ := b - a
  have hL_pos : 0 < L := by linarith

  let c_j (j : ℕ) : ℝ := a + (j : ℝ) * L / 50
  let d_j (j : ℕ) : ℝ := a + ((j : ℝ) + 1) * L / 50

  -- The 50 subinterval slabs cover the full slab
  have h_cover : horizontalSlab a b ⊆ ⋃ j : Fin 50, horizontalSlab (c_j j) (d_j j) := by
    intro x hx
    have hz1 : a ≤ x 2 := hx.1
    have hz2 : x 2 ≤ b := hx.2
    let y : ℝ := (x 2 - a) / (L / 50)
    have hy0 : 0 ≤ y := by positivity
    have hy50 : y ≤ 50 := by
      dsimp only [y]
      have h : (x 2 - a) / (L / 50) ≤ 50 := by
        calc (x 2 - a) / (L / 50) ≤ (b - a) / (L / 50) := by gcongr
          _ = 50 := by
            field_simp [hL_pos.ne'] <;> ring
      exact h
    have h_main : ∃ (j : ℕ), j < 50 ∧ (j : ℝ) ≤ y ∧ y ≤ (j : ℝ) + 1 := by
      by_cases h : y < 50
      · have hfy : 0 ≤ ⌊y⌋ := Int.floor_nonneg.mpr hy0
        let k : ℕ := ⌊y⌋.toNat
        have hk_eq : (k : ℤ) = ⌊y⌋ := by
          simp [k, Int.toNat_of_nonneg hfy]
        have hk_lt50 : k < 50 := by
          have h1 : (k : ℤ) < 50 := by
            rw [hk_eq]
            have h2 : ⌊y⌋ ≤ y := Int.floor_le y
            have h3 : (⌊y⌋ : ℝ) < 50 := by linarith
            exact_mod_cast h3
          exact_mod_cast h1
        have hk_le : (k : ℝ) ≤ y := by
          have h4 : (k : ℤ) = ⌊y⌋ := hk_eq
          have h5 : (k : ℝ) = (⌊y⌋ : ℝ) := by exact_mod_cast h4
          rw [h5]
          exact Int.floor_le y
        have hk_gt : y < (k : ℝ) + 1 := by
          have h4 : (k : ℤ) = ⌊y⌋ := hk_eq
          have h5 : (k : ℝ) = (⌊y⌋ : ℝ) := by exact_mod_cast h4
          rw [h5]
          exact Int.lt_floor_add_one y
        exact ⟨k, hk_lt50, hk_le, by linarith⟩
      · have hy_eq : y = 50 := by linarith
        refine ⟨49, by norm_num, ?_, ?_⟩
        · rw [hy_eq] <;> norm_num
        · rw [hy_eq] <;> norm_num
    rcases h_main with ⟨j, hj_lt50, hj_le, hj_le2⟩
    let jfin : Fin 50 := ⟨j, hj_lt50⟩
    have hpos : 0 < L / 50 := by positivity
    have h1 : c_j j ≤ x 2 := by
      dsimp only [c_j]
      have h2 : (j : ℝ) * (L / 50) ≤ y * (L / 50) := by
        exact mul_le_mul_of_nonneg_right hj_le hpos.le
      have h3 : a + (j : ℝ) * (L / 50) ≤ a + y * (L / 50) := by linarith
      have h4 : a + y * (L / 50) = x 2 := by
        dsimp only [y] <;> field_simp [hL_pos.ne'] <;> ring
      linarith
    have h2 : x 2 ≤ d_j j := by
      dsimp only [d_j]
      have h3 : y * (L / 50) ≤ ((j : ℝ) + 1) * (L / 50) := by
        exact mul_le_mul_of_nonneg_right hj_le2 hpos.le
      have h4 : a + y * (L / 50) ≤ a + ((j : ℝ) + 1) * (L / 50) := by linarith
      have h5 : a + y * (L / 50) = x 2 := by
        dsimp only [y] <;> field_simp [hL_pos.ne'] <;> ring
      linarith
    exact Set.mem_iUnion.mpr ⟨jfin, ⟨h1, h2⟩⟩

  -- Mass of full slab ≤ sum of masses of subinterval slabs
  have h_mass_sum : shadedMassInSlab Y a b ≤
      ∑ j : Fin 50, shadedMassInSlab Y (c_j j) (d_j j) := by
    simp only [shadedMassInSlab]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i _
    have h1 : Y.carrier i ∩ horizontalSlab a b ⊆
        ⋃ j : Fin 50, Y.carrier i ∩ horizontalSlab (c_j j) (d_j j) := by
      intro x hx
      have h2 : x ∈ Y.carrier i := hx.1
      have h3 : x ∈ horizontalSlab a b := hx.2
      have h4 : x ∈ ⋃ j : Fin 50, horizontalSlab (c_j j) (d_j j) := h_cover h3
      rcases Set.mem_iUnion.mp h4 with ⟨j, hj⟩
      exact Set.mem_iUnion.mpr ⟨j, ⟨h2, hj⟩⟩
    calc
      volume (Y.carrier i ∩ horizontalSlab a b)
        ≤ volume (⋃ j : Fin 50, Y.carrier i ∩ horizontalSlab (c_j j) (d_j j)) :=
          measure_mono h1
      _ ≤ ∑ j : Fin 50, volume (Y.carrier i ∩ horizontalSlab (c_j j) (d_j j)) := by
          exact measure_iUnion_fintype_le volume fun j : Fin 50 => Y.carrier i ∩ horizontalSlab (c_j j) (d_j j)

  -- Pigeonhole: one subinterval has ≥ total/50
  have h_pigeonhole : ∃ j : Fin 50,
      shadedMassInSlab Y a b / 50 ≤ shadedMassInSlab Y (c_j j) (d_j j) := by
    let a_j : Fin 50 → ENNReal := fun j => shadedMassInSlab Y (c_j j) (d_j j)
    have h_nonempty : Finset.Nonempty (Finset.univ : Finset (Fin 50)) := by
      exact ⟨0, by simp⟩
    obtain ⟨j0, _, hj0_max⟩ := Finset.exists_max_image Finset.univ a_j h_nonempty
    have h_max : ∀ j : Fin 50, a_j j ≤ a_j j0 := by
      intro j
      exact hj0_max j (Finset.mem_univ j)
    have h_sum_le : ∑ j : Fin 50, a_j j ≤ 50 * a_j j0 := by
      calc
        ∑ j : Fin 50, a_j j ≤ ∑ j : Fin 50, a_j j0 := Finset.sum_le_sum fun j _ => h_max j
        _ = 50 * a_j j0 := by
          simp [Finset.sum_const]
    have h : shadedMassInSlab Y a b ≤ 50 * a_j j0 := h_mass_sum.trans h_sum_le
    have h50_ne : (50 : ENNReal) ≠ 0 := by norm_num
    have h50_top : (50 : ENNReal) ≠ ⊤ := by norm_num
    have h_iff : shadedMassInSlab Y a b / 50 ≤ a_j j0 ↔
        shadedMassInSlab Y a b ≤ (50 : ENNReal) * a_j j0 := by
      exact ENNReal.div_le_iff' h50_ne h50_top
    have h_final : shadedMassInSlab Y a b / 50 ≤ a_j j0 := h_iff.mpr h
    exact ⟨j0, h_final⟩
  rcases h_pigeonhole with ⟨j, hj_mass⟩

  let c0 := c_j j
  let d0 := d_j j
  have hcd_len : d0 - c0 = L / 50 := by
    simp [c0, d0, c_j, d_j] <;> ring
  have hc : a ≤ c0 := by
    dsimp only [c0, c_j]
    have h2 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have h3 : a ≤ a + (j : ℝ) * L / 50 := by
      have h4 : 0 ≤ (j : ℝ) * L / 50 := by positivity
      linarith
    exact h3
  have hd : d0 ≤ b := by
    dsimp only [d0, d_j]
    have h3 : (j : ℝ) + 1 ≤ 50 := by
      have h4 : j.val ≤ 49 := by
        have h5 : j.val < 50 := j.prop
        omega
      have h6 : (j : ℝ) ≤ 49 := by exact_mod_cast h4
      linarith
    have h5 : a + ((j : ℝ) + 1) * L / 50 ≤ b := by
      have h6 : ((j : ℝ) + 1) * L / 50 ≤ L := by
        have h7 : ((j : ℝ) + 1) / 50 ≤ 1 := by linarith
        have h8 : ((j : ℝ) + 1) * L / 50 = (((j : ℝ) + 1) / 50) * L := by ring
        rw [h8]
        have h9 : (((j : ℝ) + 1) / 50) * L ≤ 1 * L :=
          mul_le_mul_of_nonneg_right h7 hL_pos.le
        simpa using h9
      linarith
    exact h5
  have hcd : c0 < d0 := by linarith

  -- Find minimum of |deriv g| on [c0, d0]
  have h_compact : IsCompact (Set.Icc c0 d0) := isCompact_Icc
  obtain ⟨z_min, hz_min, hmin⟩ : ∃ z_min ∈ Set.Icc c0 d0,
      ∀ z ∈ Set.Icc c0 d0, |deriv g z_min| ≤ |deriv g z| :=
    h_compact.exists_isMinOn ⟨c0, by linarith, by linarith⟩
      (h_cont_abs.mono fun z hz => ⟨hc.trans hz.1, hz.2.trans hd⟩)
  have hz_min_ab : z_min ∈ Set.Icc a b :=
    ⟨hc.trans hz_min.1, hz_min.2.trans hd⟩
  let m : ℝ := |deriv g z_min|
  have hm_pos : 0 < m := by
    have h : L ≤ |deriv g z_min| := h_low z_min hz_min_ab
    linarith
  have hm_low : L ≤ m := h_low z_min hz_min_ab
  have hm_high : m ≤ 1 := h_high z_min hz_min_ab

  have h_tight : ∀ z ∈ Set.Icc c0 d0, |deriv g z| ≤ m + L / 50 := by
    intro z hz
    have h_var : |(|deriv g z| - m)| ≤ |z - z_min| :=
      h_abs_lipschitz z
        ⟨hc.trans hz.1, hz.2.trans hd⟩ z_min hz_min_ab
    have h_dist : |z - z_min| ≤ L / 50 := by
      have h1 : c0 ≤ z := hz.1
      have h2 : z ≤ d0 := hz.2
      have h3 : c0 ≤ z_min := hz_min.1
      have h4 : z_min ≤ d0 := hz_min.2
      rw [abs_le] at *
      constructor <;> linarith
    have h6 : |(|deriv g z| - m)| ≤ L / 50 := h_var.trans h_dist
    have h7 : |deriv g z| - m ≤ L / 50 := (abs_le.mp h6).2
    linarith

  have h_bracket : ∀ z ∈ Set.Icc c0 d0, m ≤ |deriv g z| ∧ |deriv g z| ≤ 2 * m := by
    intro z hz
    constructor
    · exact hmin z hz
    · have h5 : |deriv g z| ≤ m + L / 50 := h_tight z hz
      have h8 : m + L / 50 ≤ 2 * m := by
        have h9 : L / 50 ≤ m := by linarith
        linarith
      linarith

  have h_mass_final : Kakeya.realRpowENN δ theta * ENNReal.ofReal L / 50 ≤
      shadedMassInSlab Y c0 d0 := by
    calc
      Kakeya.realRpowENN δ theta * ENNReal.ofReal L / 50
          = (Kakeya.realRpowENN δ theta * ENNReal.ofReal L) / 50 := by ring
      _ ≤ shadedMassInSlab Y a b / 50 := by
          exact ENNReal.div_le_div hmass (by norm_num)
      _ ≤ shadedMassInSlab Y c0 d0 := hj_mass

  exact ⟨c0, d0, hc, hcd, hd, hcd_len,
    ⟨m, hm_pos, hm_low, hm_high, h_bracket, by simpa [L] using h_tight⟩,
    hj_mass, h_mass_final⟩

/-- Paper-literal one-hundredth version used by the direct Proposition 6.5
route.  It refines the closed fiftieth selector by one mass-preserving
bisection and then recomputes the derivative minimum on the retained half. -/
lemma mass_slope_selection_tight_hundredth_of_local
    {δ : ℝ} {F : Kakeya.Streamlined.BodyFamily}
    (g : ℝ → ℝ)
    {a b : ℝ} (hab : a < b)
    (h_cont_abs : ContinuousOn (fun z => |deriv g z|) (Set.Icc a b))
    (h_abs_lipschitz :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |(|deriv g x| - |deriv g y|)| ≤ |x - y|)
    (h_low : ∀ z ∈ Set.Icc a b, b - a ≤ |deriv g z|)
    (h_high : ∀ z ∈ Set.Icc a b, |deriv g z| ≤ 1)
    (Y : Kakeya.Streamlined.Shading F)
    {theta : ℝ}
    (hmass : Kakeya.realRpowENN δ theta * ENNReal.ofReal (b - a) ≤
              shadedMassInSlab Y a b) :
    ∃ c d : ℝ,
      a ≤ c ∧ c < d ∧ d ≤ b ∧
      d - c = (b - a) / 100 ∧
      (∃ m : ℝ, 0 < m ∧ b - a ≤ m ∧ m ≤ 1 ∧
        (∀ z ∈ Set.Icc c d, m ≤ |deriv g z| ∧ |deriv g z| ≤ 2 * m) ∧
        (∀ z ∈ Set.Icc c d, |deriv g z| ≤ m + (b - a) / 100)) ∧
      shadedMassInSlab Y a b / 100 ≤
        shadedMassInSlab Y c d ∧
      Kakeya.realRpowENN δ theta * ENNReal.ofReal (b - a) / 100 ≤
        shadedMassInSlab Y c d := by
  rcases mass_slope_selection_tight_of_local g hab h_cont_abs
      h_abs_lipschitz h_low h_high Y hmass with
    ⟨c0, d0, hac0, hc0d0, hd0, hlength50,
      ⟨_m0, _hm0, _hm0Lower, _hm0One, _hband0, _htight0⟩,
      hmass50, hmassFinal50⟩
  let midpoint : ℝ := (c0 + d0) / 2
  have hc0mid : c0 < midpoint := by
    dsimp only [midpoint]
    linarith
  have hmidd0 : midpoint < d0 := by
    dsimp only [midpoint]
    linarith
  have hcover : horizontalSlab c0 d0 ⊆
      horizontalSlab c0 midpoint ∪ horizontalSlab midpoint d0 := by
    intro point hpoint
    by_cases hz : point 2 ≤ midpoint
    · exact Or.inl ⟨hpoint.1, hz⟩
    · exact Or.inr ⟨le_of_not_ge hz, hpoint.2⟩
  have hmassSum : shadedMassInSlab Y c0 d0 ≤
      shadedMassInSlab Y c0 midpoint +
        shadedMassInSlab Y midpoint d0 := by
    simp only [shadedMassInSlab]
    calc
      (∑ index, volume (Y.carrier index ∩ horizontalSlab c0 d0)) ≤
          ∑ index,
            (volume (Y.carrier index ∩ horizontalSlab c0 midpoint) +
              volume (Y.carrier index ∩ horizontalSlab midpoint d0)) := by
        apply Finset.sum_le_sum
        intro index _
        calc
          volume (Y.carrier index ∩ horizontalSlab c0 d0) ≤
              volume ((Y.carrier index ∩ horizontalSlab c0 midpoint) ∪
                (Y.carrier index ∩ horizontalSlab midpoint d0)) := by
            apply measure_mono
            intro point hpoint
            rcases hcover hpoint.2 with hleft | hright
            · exact Or.inl ⟨hpoint.1, hleft⟩
            · exact Or.inr ⟨hpoint.1, hright⟩
          _ ≤ volume (Y.carrier index ∩ horizontalSlab c0 midpoint) +
              volume (Y.carrier index ∩ horizontalSlab midpoint d0) :=
            measure_union_le _ _
      _ = (∑ index, volume (Y.carrier index ∩ horizontalSlab c0 midpoint)) +
          ∑ index, volume (Y.carrier index ∩ horizontalSlab midpoint d0) :=
        Finset.sum_add_distrib
  have hhalf : shadedMassInSlab Y c0 d0 / 2 ≤
        shadedMassInSlab Y c0 midpoint ∨
      shadedMassInSlab Y c0 d0 / 2 ≤
        shadedMassInSlab Y midpoint d0 := by
    by_cases htop : shadedMassInSlab Y c0 d0 = ⊤
    · have hsum : shadedMassInSlab Y c0 midpoint +
          shadedMassInSlab Y midpoint d0 = ⊤ := by
        rw [htop] at hmassSum
        exact top_le_iff.mp hmassSum
      rcases ENNReal.add_eq_top.mp hsum with hleft | hright
      · exact Or.inl (by rw [htop, hleft]; simp)
      · exact Or.inr (by rw [htop, hright]; simp)
    · by_cases hleft : shadedMassInSlab Y c0 d0 / 2 ≤
          shadedMassInSlab Y c0 midpoint
      · exact Or.inl hleft
      · right
        by_contra hright
        have hleft' : shadedMassInSlab Y c0 midpoint <
            shadedMassInSlab Y c0 d0 / 2 := lt_of_not_ge hleft
        have hright' : shadedMassInSlab Y midpoint d0 <
            shadedMassInSlab Y c0 d0 / 2 := lt_of_not_ge hright
        have hsum : shadedMassInSlab Y c0 midpoint +
              shadedMassInSlab Y midpoint d0 <
            shadedMassInSlab Y c0 d0 / 2 +
              shadedMassInSlab Y c0 d0 / 2 :=
          ENNReal.add_lt_add hleft' hright'
        have hhalves : shadedMassInSlab Y c0 d0 / 2 +
              shadedMassInSlab Y c0 d0 / 2 =
            shadedMassInSlab Y c0 d0 :=
          ENNReal.add_halves _
        rw [hhalves] at hsum
        exact (not_lt_of_ge hmassSum) hsum
  obtain ⟨c, d, hc0, hcd, hdd0, hlength, hhalfMass⟩ :
      ∃ c d : ℝ, c0 ≤ c ∧ c < d ∧ d ≤ d0 ∧
        d - c = (b - a) / 100 ∧
        shadedMassInSlab Y c0 d0 / 2 ≤ shadedMassInSlab Y c d := by
    rcases hhalf with hleft | hright
    · refine ⟨c0, midpoint, le_rfl, hc0mid, hmidd0.le, ?_, hleft⟩
      rw [show midpoint - c0 = (d0 - c0) / 2 by
        dsimp only [midpoint]
        ring]
      rw [hlength50]
      ring
    · refine ⟨midpoint, d0, hc0mid.le, hmidd0, le_rfl, ?_, hright⟩
      rw [show d0 - midpoint = (d0 - c0) / 2 by
        dsimp only [midpoint]
        ring]
      rw [hlength50]
      ring
  have hca : a ≤ c := hac0.trans hc0
  have hdb : d ≤ b := hdd0.trans hd0
  have hcompact : IsCompact (Set.Icc c d) := isCompact_Icc
  obtain ⟨zmin, hzmin, hmin⟩ : ∃ zmin ∈ Set.Icc c d,
      ∀ z ∈ Set.Icc c d, |deriv g zmin| ≤ |deriv g z| :=
    hcompact.exists_isMinOn ⟨c, le_rfl, hcd.le⟩
      (h_cont_abs.mono fun z hz => ⟨hca.trans hz.1, hz.2.trans hdb⟩)
  have hzminAB : zmin ∈ Set.Icc a b :=
    ⟨hca.trans hzmin.1, hzmin.2.trans hdb⟩
  let m : ℝ := |deriv g zmin|
  have hm : 0 < m := by
    have := h_low zmin hzminAB
    dsimp only [m]
    linarith
  have hmLower : b - a ≤ m := h_low zmin hzminAB
  have hmOne : m ≤ 1 := h_high zmin hzminAB
  have htight : ∀ z ∈ Set.Icc c d,
      |deriv g z| ≤ m + (b - a) / 100 := by
    intro z hz
    have hvariation : |(|deriv g z| - m)| ≤ |z - zmin| :=
      h_abs_lipschitz z ⟨hca.trans hz.1, hz.2.trans hdb⟩ zmin hzminAB
    have hdistance : |z - zmin| ≤ (b - a) / 100 := by
      rw [← hlength, abs_le]
      constructor <;> linarith [hz.1, hz.2, hzmin.1, hzmin.2]
    linarith [(abs_le.mp (hvariation.trans hdistance)).2]
  have hband : ∀ z ∈ Set.Icc c d,
      m ≤ |deriv g z| ∧ |deriv g z| ≤ 2 * m := by
    intro z hz
    refine ⟨hmin z hz, (htight z hz).trans ?_⟩
    have : (b - a) / 100 ≤ m := by linarith [hmLower]
    linarith
  have hmassHundred : shadedMassInSlab Y a b / 100 ≤
      shadedMassInSlab Y c d := by
    calc
      shadedMassInSlab Y a b / 100 =
          shadedMassInSlab Y a b / ((50 : ENNReal) * 2) := by norm_num
      _ = (shadedMassInSlab Y a b / 50) / 2 := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.div_eq_inv_mul, ENNReal.mul_inv]
        · ring
        · norm_num
        · norm_num
      _ ≤ shadedMassInSlab Y c0 d0 / 2 :=
        ENNReal.div_le_div hmass50 (by norm_num)
      _ ≤ shadedMassInSlab Y c d := hhalfMass
  have hmassFinalHundred :
      Kakeya.realRpowENN δ theta * ENNReal.ofReal (b - a) / 100 ≤
        shadedMassInSlab Y c d := by
    calc
      Kakeya.realRpowENN δ theta * ENNReal.ofReal (b - a) / 100 =
          (Kakeya.realRpowENN δ theta * ENNReal.ofReal (b - a)) /
            ((50 : ENNReal) * 2) := by norm_num
      _ = (Kakeya.realRpowENN δ theta * ENNReal.ofReal (b - a) / 50) / 2 := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.div_eq_inv_mul, ENNReal.mul_inv]
        · ring
        · norm_num
        · norm_num
      _ ≤ shadedMassInSlab Y c0 d0 / 2 :=
        ENNReal.div_le_div hmassFinal50 (by norm_num)
      _ ≤ shadedMassInSlab Y c d := hhalfMass
  exact ⟨c, d, hca, hcd, hdb, hlength,
    ⟨m, hm, hmLower, hmOne, hband, htight⟩,
    hmassHundred, hmassFinalHundred⟩

/-- Backwards-compatible globally bundled form. -/
lemma mass_slope_selection_tight
    {δ : ℝ} {F : Kakeya.Streamlined.BodyFamily}
    (g : SlopeFunction) (hg_norm : g.IsNormalized)
    {a b : ℝ} (hab : a < b)
    (h_sub : Set.Icc a b ⊆ Set.Icc (-1 : ℝ) 1)
    (h_low : ∀ z ∈ Set.Icc a b, b - a ≤ |deriv g z|)
    (Y : Kakeya.Streamlined.Shading F)
    {theta : ℝ}
    (hmass : Kakeya.realRpowENN δ theta * ENNReal.ofReal (b - a) ≤
              shadedMassInSlab Y a b) :
    ∃ c d : ℝ,
      a ≤ c ∧ c < d ∧ d ≤ b ∧
      d - c = (b - a) / 50 ∧
      (∃ m : ℝ, 0 < m ∧ b - a ≤ m ∧ m ≤ 1 ∧
        (∀ z ∈ Set.Icc c d, m ≤ |deriv g z| ∧ |deriv g z| ≤ 2 * m) ∧
        (∀ z ∈ Set.Icc c d, |deriv g z| ≤ m + (b - a) / 50)) ∧
      shadedMassInSlab Y a b / 50 ≤
        shadedMassInSlab Y c d ∧
      Kakeya.realRpowENN δ theta * ENNReal.ofReal (b - a) / 50 ≤
        shadedMassInSlab Y c d := by
  have hdf_cd : ContDiff ℝ 1 (deriv g) := by
    have h : ContDiff ℝ (1 + 1) g.toFun := g.contDiff
    exact h.deriv'
  have hdf_diff : Differentiable ℝ (deriv g) :=
    hdf_cd.differentiable (by norm_num)
  have hderivLipschitz :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |deriv g x - deriv g y| ≤ |x - y| := by
    have h : LipschitzOnWith 1 (deriv g) (Set.Icc a b) := by
      apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le
      · intro z _
        exact hdf_diff.differentiableAt
      · intro z hz
        apply NNReal.coe_le_coe.mp
        simpa [Real.norm_eq_abs] using (hg_norm z (h_sub hz)).2.2
    intro x hx y hy
    calc
      |deriv g x - deriv g y| = dist (deriv g x) (deriv g y) := by
        rw [Real.dist_eq]
      _ ≤ dist x y := by simpa using h.dist_le_mul x hx y hy
      _ = |x - y| := Real.dist_eq x y
  exact mass_slope_selection_tight_of_local g hab
    hdf_diff.continuous.abs.continuousOn
    (fun x hx y hy =>
      (abs_abs_sub_abs_le _ _).trans (hderivLipschitz x hx y hy))
    h_low (fun z hz => (hg_norm z (h_sub hz)).2.1) Y hmass

/-- Backwards-compatible form of `mass_slope_selection_tight`. -/
lemma mass_slope_selection
    {δ : ℝ} {F : Kakeya.Streamlined.BodyFamily}
    (g : SlopeFunction) (hg_norm : g.IsNormalized)
    {a b : ℝ} (hab : a < b)
    (h_sub : Set.Icc a b ⊆ Set.Icc (-1 : ℝ) 1)
    (h_low : ∀ z ∈ Set.Icc a b, b - a ≤ |deriv g z|)
    (Y : Kakeya.Streamlined.Shading F)
    {theta : ℝ}
    (hmass : Kakeya.realRpowENN δ theta * ENNReal.ofReal (b - a) ≤
              shadedMassInSlab Y a b) :
    ∃ c d : ℝ,
      a ≤ c ∧ c < d ∧ d ≤ b ∧
      d - c = (b - a) / 50 ∧
      (∃ m : ℝ, 0 < m ∧ b - a ≤ m ∧ m ≤ 1 ∧
        (∀ z ∈ Set.Icc c d, m ≤ |deriv g z| ∧ |deriv g z| ≤ 2 * m)) ∧
      shadedMassInSlab Y a b / 50 ≤
        shadedMassInSlab Y c d ∧
      Kakeya.realRpowENN δ theta * ENNReal.ofReal (b - a) / 50 ≤
        shadedMassInSlab Y c d := by
  rcases mass_slope_selection_tight g hg_norm hab h_sub h_low Y hmass with
    ⟨c, d, hc, hcd, hd, hlength,
      ⟨m, hm, hmWidth, hmOne, hband, _htight⟩, hmassFraction, hmassFinal⟩
  exact ⟨c, d, hc, hcd, hd, hlength,
    ⟨m, hm, hmWidth, hmOne, hband⟩, hmassFraction, hmassFinal⟩

end Kakeya.Assouad
