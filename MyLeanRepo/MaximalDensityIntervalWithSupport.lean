module

/-
# Maximal Density Interval with Support Endpoint

Strengthened version of `maximal_density_interval_C` that guarantees
the left endpoint `x₀` lies in `μ.support`.

If the convex hull of `μ.support ∩ I₀` has length ≥ δ, the original maximizer
already has its left endpoint in the support.  Otherwise the support is
concentrated in a sub-interval of length < δ; we shift to `[a, a+δ]` starting
at the leftmost support point `a`, which has length δ, so the self-similarity
condition is trivial.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.AllScaleFrostman
public import MyLeanRepo.MaximalDensityInterval
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Classical

namespace WeakTwoEndsSumProduct

/-- Strengthened maximal density interval: same conclusions as
`maximal_density_interval_C`, plus `x₀ ∈ μ.support`. -/
lemma maximal_density_interval_C_with_support
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    {κ C : ℝ} (hκ_pos : 0 < κ) (hC_pos : 0 < C)
    {μ : Measure ℝ} (hμ : IsDirectionFrostman δ κ C μ) :
    ∃ (x₀ r₀ : ℝ),
      δ ≤ r₀ ∧ r₀ ≤ 1 ∧
      x₀ ∈ μ.support ∧
      0 < μ (Set.Icc x₀ (x₀ + r₀)) ∧
      C ^ (-2 / κ) ≤ r₀ ∧
      ENNReal.ofReal (r₀ ^ (κ / 2)) ≤ μ (Set.Icc x₀ (x₀ + r₀)) ∧
      ∀ (a b : ℝ), Set.Icc a b ⊆ Set.Icc x₀ (x₀ + r₀) → δ ≤ b - a →
        μ (Set.Icc a b) ≤
          μ (Set.Icc x₀ (x₀ + r₀)) *
            ENNReal.ofReal (((b - a) / r₀) ^ (κ / 2)) := by
  have h_main := maximal_density_interval_C hδ_pos hδ_le_one hκ_pos hC_pos hμ
  rcases h_main with ⟨x_old, r_old, hr_geδ, hr_le1, hμ_pos, h_lower, h_density, h_self_sim⟩
  let I_old : Set ℝ := Set.Icc x_old (x_old + r_old)
  let K : Set ℝ := μ.support ∩ I_old
  have hμ_univ : μ Set.univ = 1 := hμ.1
  have hμ_frost := hμ.2.2

  have hK_nonempty : K.Nonempty := by
    by_contra h
    have h_empty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h1 : I_old ⊆ (μ.support)ᶜ := by
      intro x hx
      intro h2
      have h3 : x ∈ K := ⟨h2, hx⟩
      rw [h_empty] at h3
      simpa using h3
    have h4 : μ I_old = 0 := measure_mono_null h1 Measure.measure_compl_support
    exact hμ_pos.ne' h4

  have hK_closed : IsClosed K :=
    Measure.isClosed_support.inter isClosed_Icc
  have hI_compact : IsCompact I_old := isCompact_Icc
  have hK_sub : K ⊆ I_old := Set.inter_subset_right
  have hK_compact : IsCompact K :=
    IsCompact.of_isClosed_subset hI_compact hK_closed hK_sub
  have hK_bddAbove : BddAbove K := hI_compact.bddAbove.mono hK_sub
  have hK_bddBelow : BddBelow K := hI_compact.bddBelow.mono hK_sub

  let a : ℝ := sInf K
  let b : ℝ := sSup K
  have haK : a ∈ K := hK_compact.sInf_mem hK_nonempty
  have hbK : b ∈ K := hK_compact.sSup_mem hK_nonempty
  have ha_support : a ∈ μ.support := haK.1
  have haI : a ∈ I_old := haK.2
  have hbI : b ∈ I_old := hbK.2
  have h_a_le_b : a ≤ b := by
    have h1 : a ≤ b := csInf_le hK_bddBelow hbK
    exact h1
  have h_ab_le : b - a ≤ r_old := by
    have h1 : x_old ≤ a := haI.1
    have h2 : b ≤ x_old + r_old := hbI.2
    linarith

  have h_μ_ab : μ (Set.Icc a b) = μ I_old := by
    have h1 : I_old \ Set.Icc a b ⊆ (μ.support)ᶜ := by
      intro x hx
      have h2 : x ∈ I_old := hx.1
      have h3 : x ∉ Set.Icc a b := hx.2
      intro h4_support
      have h5 : x ∈ K := ⟨h4_support, h2⟩
      have h6 : a ≤ x := csInf_le hK_bddBelow h5
      have h7 : x ≤ b := le_csSup hK_bddAbove h5
      exact h3 ⟨h6, h7⟩
    have h4 : μ (I_old \ Set.Icc a b) = 0 :=
      measure_mono_null h1 Measure.measure_compl_support
    have h_ab_sub_old : Set.Icc a b ⊆ I_old := by
      intro y hy
      exact ⟨by linarith [haI.1, hy.1], by linarith [hbI.2, hy.2]⟩
    have h5 : I_old = Set.Icc a b ∪ (I_old \ Set.Icc a b) := by
      ext x
      simp only [Set.mem_union, Set.mem_sdiff]
      constructor
      · intro hx
        by_cases h : x ∈ Set.Icc a b
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      · rintro (h | h)
        · exact h_ab_sub_old h
        · exact h.1
    rw [h5]
    have h6 : Disjoint (Set.Icc a b) (I_old \ Set.Icc a b) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact hx2.2 hx1
    have h7 : MeasurableSet (I_old \ Set.Icc a b) :=
      measurableSet_Icc.diff measurableSet_Icc
    rw [measure_union h6 h7, h4, add_zero]

  by_cases h_case : δ ≤ b - a
  · -- Case 1: convex hull length ≥ δ
    have h1 : Set.Icc a b ⊆ I_old := by
      intro x hx
      exact ⟨by linarith [haI.1, hx.1], by linarith [hbI.2, hx.2]⟩
    have h2 : μ (Set.Icc a b) ≤ μ I_old * ENNReal.ofReal (((b - a) / r_old) ^ (κ / 2)) :=
      h_self_sim a b h1 h_case
    rw [h_μ_ab] at h2
    have hμI_ne_top : μ I_old ≠ ⊤ := by
      have h : μ I_old ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      rw [hμ_univ] at h
      exact ne_top_of_le_ne_top (by simp) h
    have h_cancel : (μ I_old)⁻¹ * (μ I_old * ENNReal.ofReal (((b - a) / r_old) ^ (κ / 2))) =
        ENNReal.ofReal (((b - a) / r_old) ^ (κ / 2)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hμ_pos.ne' hμI_ne_top, one_mul]
    have h3 : (1 : ENNReal) ≤ ENNReal.ofReal (((b - a) / r_old) ^ (κ / 2)) := by
      have h4 : (μ I_old)⁻¹ * μ I_old ≤ (μ I_old)⁻¹ * (μ I_old * ENNReal.ofReal (((b - a) / r_old) ^ (κ / 2))) := by
        gcongr
      rw [ENNReal.inv_mul_cancel hμ_pos.ne' hμI_ne_top] at h4
      rw [h_cancel] at h4
      exact h4
    have h7 : 0 ≤ b - a := by linarith
    have h8 : 0 < r_old := by linarith
    have h9 : 0 ≤ (b - a) / r_old := by positivity
    have h10 : (b - a) / r_old ≤ 1 := by
      have h101 : b - a ≤ r_old := h_ab_le
      have h102 : 0 < r_old := h8
      exact (div_le_one h102).mpr h101
    have h11 : 1 ≤ ((b - a) / r_old) ^ (κ / 2) := by
      have h111 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
      rw [h111] at h3
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
    have h12 : (b - a) / r_old = 1 := by
      by_cases h13 : (b - a) / r_old < 1
      · have h14 : ((b - a) / r_old) ^ (κ / 2) < 1 :=
          Real.rpow_lt_one h9 h13 (by linarith)
        linarith
      · have h15 : (b - a) / r_old = 1 := by linarith
        exact h15
    have h16 : b - a = r_old := by
      field_simp [h8.ne'] at h12 <;> linarith
    have h17 : a = x_old := by linarith [haI.1, hbI.2, h16]
    refine ⟨x_old, r_old, hr_geδ, hr_le1, ?_, hμ_pos, h_lower, h_density, h_self_sim⟩
    rw [h17] at ha_support
    exact ha_support

  · -- Case 2: convex hull length < δ; shift to [a, a+δ]
    have h_case' : b - a < δ := by linarith
    let x_new : ℝ := a
    let r_new : ℝ := δ
    have h_xnew_support : x_new ∈ μ.support := ha_support
    have hrnew_geδ : δ ≤ r_new := by simp [show r_new = δ from rfl]
    have hrnew_le1 : r_new ≤ 1 := by
      simp [show r_new = δ from rfl]
      exact hδ_le_one
    have h_rnew_pos : 0 < r_new := by
      simp [show r_new = δ from rfl]
      exact hδ_pos

    have h_ab_sub : Set.Icc a b ⊆ Set.Icc x_new (x_new + r_new) := by
      intro z hz
      have h1 : a ≤ z := hz.1
      have h2 : z ≤ b := hz.2
      have h3 : b < a + δ := by linarith [h_case']
      have h4 : z ≤ a + δ := by linarith
      have h5 : x_new + r_new = a + δ := by
        dsimp only [x_new, r_new] <;> ring
      have h6 : z ≤ x_new + r_new := by
        rw [h5] <;> exact h4
      exact ⟨h1, h6⟩

    have h_μ_new_pos : 0 < μ (Set.Icc x_new (x_new + r_new)) := by
      have h1 : μ (Set.Icc a b) ≤ μ (Set.Icc x_new (x_new + r_new)) := measure_mono h_ab_sub
      rw [h_μ_ab] at h1
      exact hμ_pos.trans_le h1

    have h_density_new : ENNReal.ofReal (r_new ^ (κ / 2)) ≤ μ (Set.Icc x_new (x_new + r_new)) := by
      have h1 : ENNReal.ofReal (r_old ^ (κ / 2)) ≤ μ I_old := h_density
      have h2 : μ I_old ≤ μ (Set.Icc x_new (x_new + r_new)) := by
        rw [← h_μ_ab]
        exact measure_mono h_ab_sub
      have h3 : δ ^ (κ / 2) ≤ r_old ^ (κ / 2) := by
        have h4 : δ ≤ r_old := hr_geδ
        have h5 : 0 ≤ δ := by linarith
        exact Real.rpow_le_rpow h5 h4 (by linarith)
      have h4 : ENNReal.ofReal (δ ^ (κ / 2)) ≤ ENNReal.ofReal (r_old ^ (κ / 2)) :=
        ENNReal.ofReal_le_ofReal h3
      have h5 : ENNReal.ofReal (r_new ^ (κ / 2)) = ENNReal.ofReal (δ ^ (κ / 2)) := by
        congr <;> simp [show r_new = δ from rfl]
      rw [h5]
      exact h4.trans (h1.trans h2)

    have h_frost_upper : μ (Set.Icc x_new (x_new + r_new)) ≤ ENNReal.ofReal (C * r_new ^ κ) := by
      have h1 : Set.Icc x_new (x_new + r_new) ⊆ Set.Icc (x_new - r_new) (x_new + r_new) := by
        intro z hz
        have h2 : x_new ≤ z := hz.1
        have h3 : z ≤ x_new + r_new := hz.2
        constructor <;> linarith
      have h2 : δ ≤ r_new := hrnew_geδ
      have h3 : r_new ≤ 1 := hrnew_le1
      have h4 := hμ_frost x_new r_new h2 h3
      exact measure_mono h1 |>.trans h4

    have h_lower_new : C ^ (-2 / κ) ≤ r_new := by
      have h4 : ENNReal.ofReal (r_new ^ (κ / 2)) ≤ ENNReal.ofReal (C * r_new ^ κ) :=
        h_density_new.trans h_frost_upper
      have h5 : r_new ^ (κ / 2) ≤ C * r_new ^ κ := by
        have h51 : 0 ≤ r_new ^ (κ / 2) := by positivity
        have h52 : 0 ≤ C * r_new ^ κ := by positivity
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h4
      have h6 : 0 < r_new := h_rnew_pos
      have h7 : 0 < r_new ^ (κ / 2) := Real.rpow_pos_of_pos h6 _
      have h8 : 1 ≤ C * r_new ^ (κ / 2) := by
        have h9 : r_new ^ κ = r_new ^ (κ / 2) * r_new ^ (κ / 2) := by
          rw [← Real.rpow_add h6] <;> ring_nf
        calc (1 : ℝ)
          = r_new ^ (κ / 2) / r_new ^ (κ / 2) := by field_simp [h7.ne']
        _ ≤ (C * r_new ^ κ) / r_new ^ (κ / 2) := by gcongr
        _ = C * r_new ^ (κ / 2) := by rw [h9]; field_simp [h7.ne'] <;> ring
      have h10 : C ^ (-1 : ℝ) ≤ r_new ^ (κ / 2) := by
        have h11 : C ^ (-1 : ℝ) = 1 / C := by simp [Real.rpow_neg_one]
        rw [h11]
        have h12 : 0 < C := hC_pos
        calc 1 / C ≤ (C * r_new ^ (κ / 2)) / C := by gcongr
             _ = r_new ^ (κ / 2) := by field_simp [h12.ne'] <;> ring
      have h12 : (C ^ (-1 : ℝ)) ^ (2 / κ) ≤ (r_new ^ (κ / 2)) ^ (2 / κ) := by gcongr
      have h13 : (C ^ (-1 : ℝ)) ^ (2 / κ) = C ^ (-2 / κ) := by
        rw [← Real.rpow_mul hC_pos.le] <;> ring_nf
      have h14 : (r_new ^ (κ / 2)) ^ (2 / κ) = r_new := by
        rw [← Real.rpow_mul h6.le]
        have h15 : (κ / 2) * (2 / κ) = 1 := by field_simp [hκ_pos.ne'] <;> ring
        rw [h15, Real.rpow_one]
      rw [h13, h14] at h12
      exact h12

    have h_self_sim_new : ∀ (c d : ℝ), Set.Icc c d ⊆ Set.Icc x_new (x_new + r_new) → δ ≤ d - c →
        μ (Set.Icc c d) ≤ μ (Set.Icc x_new (x_new + r_new)) * ENNReal.ofReal (((d - c) / r_new) ^ (κ / 2)) := by
      intro c d h_sub h_len
      have h1 : c ≥ x_new := (h_sub ⟨by linarith, by linarith⟩).1
      have h2 : d ≤ x_new + r_new := (h_sub ⟨by linarith, by linarith⟩).2
      have h3 : d - c ≤ r_new := by linarith
      have h4 : d - c = r_new := by linarith
      have h5 : c = x_new := by linarith
      have h6 : d = x_new + r_new := by linarith
      have h7 : ((d - c) / r_new) ^ (κ / 2) = 1 := by
        rw [h4]
        have h8 : r_new / r_new = 1 := by field_simp [h_rnew_pos.ne']
        rw [h8]
        norm_num
      have h9 : μ (Set.Icc c d) = μ (Set.Icc x_new (x_new + r_new)) := by
        rw [h5, h6]
      rw [h9, h7, ENNReal.ofReal_one, mul_one]

    exact ⟨x_new, r_new, hrnew_geδ, hrnew_le1, h_xnew_support, h_μ_new_pos, h_lower_new, h_density_new, h_self_sim_new⟩

/-- All-scale version of `maximal_density_interval_C_with_support`.

Derives `IsDirectionFrostman` from `IsAllScaleFrostman` and adds the
`x_min ≤ x₀` bound from the support lower bound. -/
lemma maximal_density_interval_allscale_with_support
    {δ κ C : ℝ} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hκ_pos : 0 < κ) (hC_pos : 0 < C)
    {μ : Measure ℝ} (hμ : IsAllScaleFrostman κ C μ)
    (hμ_supp : μ.support ⊆ Set.Icc 0 1)
    {x_min : ℝ} (hμ_supp_lower : μ.support ⊆ Set.Icc x_min 1) :
    ∃ (x₀ r₀ : ℝ),
      δ ≤ r₀ ∧ r₀ ≤ 1 ∧
      x_min ≤ x₀ ∧
      x₀ ∈ μ.support ∧
      0 < μ (Set.Icc x₀ (x₀ + r₀)) ∧
      C ^ (-2 / κ) ≤ r₀ ∧
      ENNReal.ofReal (r₀ ^ (κ / 2)) ≤ μ (Set.Icc x₀ (x₀ + r₀)) ∧
      ∀ (a b : ℝ), Set.Icc a b ⊆ Set.Icc x₀ (x₀ + r₀) → δ ≤ b - a →
        μ (Set.Icc a b) ≤
          μ (Set.Icc x₀ (x₀ + r₀)) *
            ENNReal.ofReal (((b - a) / r₀) ^ (κ / 2)) := by
  have hμ_univ : μ Set.univ = 1 := hμ.1
  have hμ_frost := hμ.2.2.2
  have h_dir : IsDirectionFrostman δ κ C μ := by
    refine' ⟨hμ_univ, hμ_supp, _⟩
    intro a r hrδ hr1
    have hr_pos : 0 < r := by linarith
    exact hμ_frost a r hr_pos
  have h_main := maximal_density_interval_C_with_support hδ_pos hδ_le_one hκ_pos hC_pos h_dir
  rcases h_main with ⟨x₀, r₀, hr₀_geδ, hr₀_le1, hx0_supp, hμ_pos, h_lower, h_density, h_self_sim⟩
  have h_x0_ge : x_min ≤ x₀ := (hμ_supp_lower hx0_supp).1
  exact ⟨x₀, r₀, hr₀_geδ, hr₀_le1, h_x0_ge, hx0_supp, hμ_pos, h_lower, h_density, h_self_sim⟩

end WeakTwoEndsSumProduct
