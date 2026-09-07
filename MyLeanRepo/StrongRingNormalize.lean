module

/-
# Strong Ring Normalization

Frostman measure normalization away from zero.

Given a `(κ,C₀)`-measure μ supported on (0,1], produce a normalized measure μ'
supported away from 0 on [2δ,1] that is a `(κ,2*C₀)`-measure.

## Proof

Use the Frostman bound at scale δ with center δ to bound μ([0,2δ]) ≤ C₀·δ^κ ≤ 1/2
(using δ ≤ (1/(2C₀))^(1/κ)). Hence the restriction to [2δ,1] has mass ≥ 1/2.
Renormalizing gives a probability measure whose Frostman constant is at most 2·C₀.

This is Step 1 of the strong ring theorem (paper line 587).
-/
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.AllScaleFrostman
public import MyLeanRepo.StrongRingHelpers
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Classical

namespace WeakTwoEndsSumProduct

noncomputable section

/-- Given a `(κ,C₀)`-measure μ supported on (0,1], produce a normalized
measure μ' supported away from 0 that is a `(κ, 2*C₀)`-measure. -/
lemma step1_normalize
    {δ κ C₀ : ℝ} (hδ_pos : 0 < δ) (hδ_le_half : δ ≤ 1 / 2)
    (hκ_pos : 0 < κ) (hC₀_pos : 0 < C₀)
    {μ : Measure ℝ} (hμ : IsDirectionFrostman δ κ C₀ μ)
    (hμ_supp : μ.support ⊆ Set.Ioi 0)
    (hμ_univ : μ Set.univ = 1)
    (hδ_small : δ ≤ (1 / (2 * C₀)) ^ (1 / κ)) :
    ∃ (μ' : Measure ℝ) (r : ℝ),
      0 < r ∧
      IsDirectionFrostman δ κ (2 * C₀) μ' ∧
      μ'.support ⊆ Set.Icc (2 * r) 1 ∧
      μ' Set.univ = 1 ∧
      μ'.support ⊆ μ.support := by
  let r : ℝ := δ
  have hr_pos : 0 < r := hδ_pos
  have h2r_le_one : 2 * r ≤ 1 := by linarith
  let S : Set ℝ := Set.Icc (2 * r) 1
  have hS_nonempty : S.Nonempty := ⟨1, by simp [S, h2r_le_one] <;> linarith⟩
  have hμ_Icc01 : μ (Set.Icc (0 : ℝ) 1) = 1 := by
    have h1 : (Set.Icc (0 : ℝ) 1)ᶜ ⊆ μ.supportᶜ := by
      intro x hx
      exact fun h => hx (hμ.2.1 h)
    have h2 : μ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 :=
      measure_mono_null h1 Measure.measure_compl_support
    have h3 : μ (Set.Icc (0 : ℝ) 1) + μ ((Set.Icc (0 : ℝ) 1)ᶜ) = μ Set.univ := by
      rw [← measure_union (disjoint_compl_right) measurableSet_Icc.compl] <;> simp
    have h4 : μ (Set.Icc (0 : ℝ) 1) = μ Set.univ := by
      rw [h2] at h3 <;> simpa using h3
    rw [h4, hμ_univ]
  have h_frost := hμ.2.2
  have h_Cδ_le_half : C₀ * δ ^ κ ≤ 1 / 2 := by
    have h_pos1 : 0 < 1 / (2 * C₀) := by positivity
    have h9 : (1 / κ : ℝ) * κ = 1 := by field_simp [hκ_pos.ne']
    have h10 : ((1 / (2 * C₀)) ^ (1 / κ)) ^ κ = 1 / (2 * C₀) := by
      rw [← Real.rpow_mul (by positivity), h9]
      simp
    have h11 : δ ^ κ ≤ ((1 / (2 * C₀)) ^ (1 / κ)) ^ κ := by
      gcongr <;> linarith
    have h12 : δ ^ κ ≤ 1 / (2 * C₀) := by
      rw [h10] at h11; exact h11
    have h13 : C₀ * δ ^ κ ≤ C₀ * (1 / (2 * C₀)) := by gcongr
    have h14 : C₀ * (1 / (2 * C₀)) = 1 / 2 := by
      field_simp [hC₀_pos.ne'] <;> ring
    rw [h14] at h13
    exact h13
  have h_interval_eq : Set.Icc (δ - δ) (δ + δ) = Set.Icc (0 : ℝ) (2 * δ) := by
    have h1 : δ - δ = 0 := by ring
    have h2 : δ + δ = 2 * δ := by ring
    rw [h1, h2]
  have h_μ_Icc02δ_le_half : μ (Set.Icc (0 : ℝ) (2 * δ)) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    have h1 : μ (Set.Icc (δ - δ) (δ + δ)) ≤ ENNReal.ofReal (C₀ * δ ^ κ) :=
      h_frost δ δ (by linarith) (by linarith)
    rw [h_interval_eq] at h1
    have h2 : ENNReal.ofReal (C₀ * δ ^ κ) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
      exact ofReal_le_ofReal h_Cδ_le_half
    exact le_trans h1 h2
  have h_disj : Disjoint (Set.Icc (0 : ℝ) (2 * δ)) (Set.Ioc (2 * δ) 1) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : x ≤ 2 * δ := hx1.2
    have h2 : 2 * δ < x := hx2.1
    linarith
  have h_union : Set.Icc (0 : ℝ) (2 * δ) ∪ Set.Ioc (2 * δ) 1 = Set.Icc (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith [h2r_le_one]⟩
      · exact ⟨by linarith, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases h3 : x ≤ 2 * δ
      · exact Or.inl ⟨h1, h3⟩
      · have h4 : 2 * δ < x := by linarith
        exact Or.inr ⟨h4, h2⟩
  have h_add : μ (Set.Icc (0 : ℝ) (2 * δ)) + μ (Set.Ioc (2 * δ) 1) = μ (Set.Icc (0 : ℝ) 1) := by
    rw [← measure_union h_disj measurableSet_Ioc, h_union]
  let a := μ (Set.Icc (0 : ℝ) (2 * δ))
  let b := μ (Set.Ioc (2 * δ) 1)
  have h_ab : a + b = 1 := by
    simpa [a, b] using h_add.trans hμ_Icc01
  have h_Icc02δ_sub : Set.Icc (0 : ℝ) (2 * δ) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    have h1 : 0 ≤ x := hx.1
    have h2 : x ≤ 2 * δ := hx.2
    have h3 : x ≤ 1 := le_trans h2 h2r_le_one
    exact ⟨h1, h3⟩
  have h_Ioc_sub : Set.Ioc (2 * δ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    have h1 : 2 * δ < x := hx.1
    have h2 : x ≤ 1 := hx.2
    have h3 : 0 ≤ x := by linarith
    exact ⟨h3, h2⟩
  have ha_le_one : a ≤ 1 := by
    have h' : μ (Set.Icc (0 : ℝ) (2 * δ)) ≤ μ (Set.Icc (0 : ℝ) 1) := measure_mono h_Icc02δ_sub
    rw [hμ_Icc01] at h'
    exact h'
  have ha_ne_top : a ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) ha_le_one
  have hb_le_one : b ≤ 1 := by
    have h' : μ (Set.Ioc (2 * δ) 1) ≤ μ (Set.Icc (0 : ℝ) 1) := measure_mono h_Ioc_sub
    rw [hμ_Icc01] at h'
    exact h'
  have hb_ne_top : b ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hb_le_one
  have h_b_ge_half : b ≥ ENNReal.ofReal (1 / 2 : ℝ) := by
    have h_eq : b = 1 - a := by
      have h : a + b = 1 := h_ab
      have h' : b = 1 - a := by
        rw [← h]
        rw [ENNReal.add_sub_cancel_left ha_ne_top]
        <;> simp
      exact h'
    rw [h_eq]
    have h4 : 1 - a ≥ 1 - ENNReal.ofReal (1 / 2 : ℝ) :=
      tsub_le_tsub_left h_μ_Icc02δ_le_half 1
    have h5 : 1 - ENNReal.ofReal (1 / 2 : ℝ) = ENNReal.ofReal (1 / 2 : ℝ) := by
      simp [ENNReal.ofReal_add] <;> norm_num
    rw [h5] at h4
    exact h4
  have h_Ioc_sub_S : Set.Ioc (2 * δ) 1 ⊆ S := by
    intro x hx
    have h21 : 2 * δ < x := hx.1
    have h22 : x ≤ 1 := hx.2
    have h23 : 2 * δ ≤ x := by linarith
    exact ⟨h23, h22⟩
  have h_μ_S_ge_half : μ S ≥ ENNReal.ofReal (1 / 2 : ℝ) := by
    have h3 : μ (Set.Ioc (2 * δ) 1) ≤ μ S := measure_mono h_Ioc_sub_S
    have h4 : b ≤ μ S := by simpa [b] using h3
    exact le_trans h_b_ge_half h4
  have h_μ_S_pos : 0 < μ S := by
    have h1 : ENNReal.ofReal (1 / 2 : ℝ) > 0 := by positivity
    exact lt_of_lt_of_le h1 h_μ_S_ge_half
  have h_μ_S_le_one : μ S ≤ 1 := by
    have h1 : μ S ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    rw [hμ_univ] at h1
    exact h1
  have h_μ_S_ne_top : μ S ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) h_μ_S_le_one
  let μ' : Measure ℝ := (μ S)⁻¹ • μ.restrict S
  have hμ'_univ : μ' Set.univ = 1 := by
    have h1 : μ' Set.univ = (μ S)⁻¹ * μ.restrict S Set.univ := by rfl
    rw [h1]
    have h2 : μ.restrict S Set.univ = μ S := by
      simp [Measure.restrict_apply]
    rw [h2]
    exact ENNReal.inv_mul_cancel h_μ_S_pos.ne' h_μ_S_ne_top
  have h_smul_pos : ∀ (t : Set ℝ), μ' t = 0 ↔ (μ.restrict S) t = 0 := by
    intro t
    simp [μ', h_μ_S_pos.ne', h_μ_S_ne_top]
    <;> constructor <;> intro h <;> simpa using h
  have h_supp_smul : μ'.support ⊆ (μ.restrict S).support := by
    intro x hx
    by_contra h
    have h' : x ∉ (μ.restrict S).support := h
    have h_exists : ∃ (U : Set ℝ), U ∈ nhds x ∧ (μ.restrict S) U = 0 :=
      Measure.notMem_support_iff_exists.mp h'
    rcases h_exists with ⟨U, hU_nhds, hμU⟩
    have hμ'U : μ' U = 0 := (h_smul_pos U).mpr hμU
    have h_contra : x ∉ μ'.support :=
      Measure.notMem_support_iff_exists.mpr ⟨U, hU_nhds, hμ'U⟩
    exact h_contra hx
  have h_restrict_supp_subset_S : (μ.restrict S).support ⊆ S := by
    have h2 : (μ.restrict S).support ⊆ closure S ∩ μ.support := Measure.support_restrict_subset
    have h3 : closure S ∩ μ.support ⊆ closure S := by intro x hx; exact hx.1
    have h4 : closure S = S := IsClosed.closure_eq isClosed_Icc
    have h5 : (μ.restrict S).support ⊆ closure S := h2.trans h3
    rw [h4] at h5
    exact h5
  have h_restrict_supp_subset_μsupp : (μ.restrict S).support ⊆ μ.support := by
    have h2 : (μ.restrict S).support ⊆ closure S ∩ μ.support := Measure.support_restrict_subset
    have h3 : closure S ∩ μ.support ⊆ μ.support := by intro x hx; exact hx.2
    exact h2.trans h3
  have hμ'_supp_subset_S : μ'.support ⊆ S :=
    h_supp_smul.trans h_restrict_supp_subset_S
  have hμ'_supp_subset_μsupp : μ'.support ⊆ μ.support :=
    h_supp_smul.trans h_restrict_supp_subset_μsupp
  have hμ'_frost : IsDirectionFrostman δ κ (2 * C₀) μ' := by
    refine' ⟨hμ'_univ, _, _⟩
    · have h1 : μ'.support ⊆ S := hμ'_supp_subset_S
      have h2 : S ⊆ Set.Icc (0 : ℝ) 1 := by
        intro x hx
        have h3 : 2 * δ ≤ x := hx.1
        have h4 : x ≤ 1 := hx.2
        exact ⟨by linarith, h4⟩
      exact h1.trans h2
    · intro a s hsδ hs1
      have h1 : μ' (Set.Icc (a - s) (a + s)) = (μ S)⁻¹ * μ (S ∩ Set.Icc (a - s) (a + s)) := by
        have h_eq : μ' (Set.Icc (a - s) (a + s)) = (μ S)⁻¹ * μ (Set.Icc (a - s) (a + s) ∩ S) := by
          simp [μ', Measure.smul_apply, restrict_apply] <;> rfl
        rw [h_eq]
        have h_comm : Set.Icc (a - s) (a + s) ∩ S = S ∩ Set.Icc (a - s) (a + s) := Set.inter_comm _ _
        rw [h_comm]
      rw [h1]
      have h2 : μ (S ∩ Set.Icc (a - s) (a + s)) ≤ μ (Set.Icc (a - s) (a + s)) :=
        measure_mono Set.inter_subset_right
      have h3 : μ (Set.Icc (a - s) (a + s)) ≤ ENNReal.ofReal (C₀ * s ^ κ) :=
        h_frost a s hsδ hs1
      have h4 : (μ S)⁻¹ ≤ ENNReal.ofReal (2 : ℝ) := by
        have h5 : μ S ≥ ENNReal.ofReal (1 / 2 : ℝ) := h_μ_S_ge_half
        have h6 : (μ S)⁻¹ ≤ (ENNReal.ofReal (1 / 2 : ℝ))⁻¹ :=
          ENNReal.inv_le_inv' h5
        have h7 : (ENNReal.ofReal (1 / 2 : ℝ))⁻¹ = ENNReal.ofReal (2 : ℝ) := by simp
        rw [h7] at h6
        exact h6
      calc
        (μ S)⁻¹ * μ (S ∩ Set.Icc (a - s) (a + s))
          ≤ (μ S)⁻¹ * μ (Set.Icc (a - s) (a + s)) := by gcongr
        _ ≤ (μ S)⁻¹ * ENNReal.ofReal (C₀ * s ^ κ) := by gcongr
        _ ≤ ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (C₀ * s ^ κ) := by gcongr
        _ = ENNReal.ofReal ((2 * C₀) * s ^ κ) := by
          have h_eq1 : ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (C₀ * s ^ κ) =
              ENNReal.ofReal ((2 : ℝ) * (C₀ * s ^ κ)) := by
            rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          rw [h_eq1]
          have h_eq2 : (2 : ℝ) * (C₀ * s ^ κ) = (2 * C₀) * s ^ κ := by ring
          rw [h_eq2]
  exact ⟨μ', r, hr_pos, hμ'_frost, hμ'_supp_subset_S, hμ'_univ, hμ'_supp_subset_μsupp⟩

/-- **All-scale Step 1**: Normalize an all-scale `(κ,C)`-Frostman measure μ
    supported on `[0,1]` to a measure μ' supported on `[2^{-1/κ},1]` that is
    all-scale `(κ,2C)`-Frostman.

    Proof: `μ[0,2^{-1/κ}] ≤ C·(2^{-1/κ})^κ = 1/2` by all-scale Frostman.
    Restrict to `[2^{-1/κ},1]` and renormalize. Constant doubles. -/
lemma step1_normalize_allscale
    {κ C : ℝ} (hκ_pos : 0 < κ) (hC_pos : 0 < C)
    (hC_le : C ≤ 2 ^ κ)
    {μ : Measure ℝ} (hμ : IsAllScaleFrostman κ C μ)
    (hμ_supp : μ.support ⊆ Set.Icc 0 1)
    (hμ_univ : μ Set.univ = 1) :
    ∃ (μ' : Measure ℝ),
      IsAllScaleFrostman κ (2 * C) μ' ∧
      μ'.support ⊆ Set.Icc ((2 : ℝ) ^ (-(1/κ))) 1 ∧
      μ' Set.univ = 1 ∧
      μ'.support ⊆ μ.support := by
  let a : ℝ := (2 : ℝ) ^ (-(1/κ))
  have ha_pos : 0 < a := by positivity
  have ha_le_one : a ≤ 1 := by
    have h1 : (1 : ℝ) / κ > 0 := by positivity
    have h2 : a = (2 : ℝ) ^ (-(1 / κ)) := rfl
    rw [h2]
    have h3 : (2 : ℝ) ^ (-(1 / κ)) ≤ (2 : ℝ) ^ (0 : ℝ) := by gcongr <;> linarith
    simpa using h3
  let half_a : ℝ := a / 2
  have h_half_a_pos : 0 < half_a := by positivity
  have h_power : half_a ^ κ = (2 : ℝ) ^ (-1 - κ) := by
    have h1 : half_a = (2 : ℝ) ^ (-(1 / κ) - 1) := by
      dsimp only [half_a, a]
      have h2 : (2 : ℝ) ^ (-(1 / κ)) / 2 = (2 : ℝ) ^ (-(1 / κ)) * (2 : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one] <;> ring
      rw [h2]
      have h3 : (2 : ℝ) ^ (-(1 / κ)) * (2 : ℝ) ^ (-1 : ℝ) = (2 : ℝ) ^ ((-(1 / κ)) + (-1 : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)] <;> ring
      rw [h3] <;> ring_nf
    rw [h1]
    have h4 : ((-(1 / κ) - 1 : ℝ) * κ) = -1 - κ := by
      field_simp [hκ_pos.ne'] <;> ring
    rw [← Real.rpow_mul (by norm_num), h4]
  have h_frost := hμ.2.2.2
  have h_interval : Set.Icc (half_a - half_a) (half_a + half_a) = Set.Icc (0 : ℝ) a := by
    have h11 : half_a - half_a = 0 := by ring
    have h12 : half_a + half_a = a := by dsimp only [half_a] <;> ring
    rw [h11, h12]
  have h1 : μ (Set.Icc (0 : ℝ) a) ≤ ENNReal.ofReal (C * half_a ^ κ) := by
    have h_frost' := h_frost half_a half_a h_half_a_pos
    have h_eq : Set.Icc (half_a - half_a) (half_a + half_a) = Set.Icc (0 : ℝ) a := h_interval
    rw [h_eq] at h_frost'
    exact h_frost'
  have h2 : C * half_a ^ κ ≤ 1 / 2 := by
    rw [h_power]
    have h4 : (2 : ℝ) ^ (-1 - κ) = 1 / (2 * (2 : ℝ) ^ κ) := by
      have h5 : (-1 - κ : ℝ) = - (1 + κ) := by ring
      rw [h5, Real.rpow_neg (by norm_num)]
      have h6 : (2 : ℝ) ^ (1 + κ) = 2 * (2 : ℝ) ^ κ := by
        rw [Real.rpow_add (by norm_num)] <;> ring
      rw [h6] <;> ring
    rw [h4]
    have h_div : C * (1 / (2 * (2 : ℝ) ^ κ)) = C / (2 * (2 : ℝ) ^ κ) := by ring
    rw [h_div]
    have h6 : C / (2 * (2 : ℝ) ^ κ) ≤ 1 / 2 := by
      calc C / (2 * (2 : ℝ) ^ κ)
        ≤ (2 : ℝ) ^ κ / (2 * (2 : ℝ) ^ κ) := by gcongr
      _ = 1 / 2 := by
        field_simp [show (0 : ℝ) < (2 : ℝ) ^ κ by positivity] <;> ring
    exact h6
  have h_μ_Icc0a_le_half : μ (Set.Icc (0 : ℝ) a) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    calc μ (Set.Icc (0 : ℝ) a)
      ≤ ENNReal.ofReal (C * half_a ^ κ) := h1
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr h2
  have hμ_Icc01 : μ (Set.Icc (0 : ℝ) 1) = 1 := by
    have h1 : (Set.Icc (0 : ℝ) 1)ᶜ ⊆ μ.supportᶜ := by
      intro x hx
      exact fun h => hx (hμ_supp h)
    have h2 : μ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 :=
      measure_mono_null h1 Measure.measure_compl_support
    have h3 : μ (Set.Icc (0 : ℝ) 1) + μ ((Set.Icc (0 : ℝ) 1)ᶜ) = μ Set.univ := by
      rw [← measure_union (disjoint_compl_right) measurableSet_Icc.compl] <;> simp
    have h4 : μ (Set.Icc (0 : ℝ) 1) = μ Set.univ := by
      rw [h2] at h3 <;> simpa using h3
    rw [h4, hμ_univ]
  let S : Set ℝ := Set.Icc a 1
  have hS_nonempty : S.Nonempty := by
    refine' ⟨1, _⟩
    simp only [S, Set.mem_Icc]
    constructor <;> linarith [ha_le_one]
  have hS_meas : MeasurableSet S := measurableSet_Icc
  have h_disj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a 1) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : x ≤ a := hx1.2
    have h2 : a < x := hx2.1
    linarith
  have h_union : Set.Icc (0 : ℝ) a ∪ Set.Ioc a 1 = Set.Icc (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨by linarith, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases h3 : x ≤ a
      · exact Or.inl ⟨h1, h3⟩
      · have h4 : a < x := by linarith
        exact Or.inr ⟨h4, h2⟩
  have h_add : μ (Set.Icc (0 : ℝ) a) + μ (Set.Ioc a 1) = μ (Set.Icc (0 : ℝ) 1) := by
    rw [← measure_union h_disj measurableSet_Ioc, h_union]
  have h_Ioc0a_sub : Set.Icc (0 : ℝ) a ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    have h_x2 : x ≤ a := hx.2
    have h_x3 : x ≤ 1 := by linarith [ha_le_one, h_x2]
    exact ⟨hx.1, h_x3⟩
  have h_μ_Icc0a_ne_top : μ (Set.Icc (0 : ℝ) a) ≠ ⊤ := by
    have h_le : μ (Set.Icc (0 : ℝ) a) ≤ μ (Set.Icc (0 : ℝ) 1) := measure_mono h_Ioc0a_sub
    rw [hμ_Icc01] at h_le
    exact ne_top_of_le_ne_top (by norm_num) h_le
  have h4 : μ (Set.Ioc a 1) = 1 - μ (Set.Icc (0 : ℝ) a) := by
    have h : μ (Set.Icc (0 : ℝ) a) + μ (Set.Ioc a 1) = 1 := h_add.trans hμ_Icc01
    rw [← h]
    rw [ENNReal.add_sub_cancel_left h_μ_Icc0a_ne_top] <;> simp
  have h_Ioc_sub_S : Set.Ioc a 1 ⊆ S := by
    intro x hx
    have h_ax : a < x := hx.1
    have h_ax' : a ≤ x := le_of_lt h_ax
    exact ⟨h_ax', hx.2⟩
  have h_μ_S_ge : μ S ≥ ENNReal.ofReal (1 / 2 : ℝ) := by
    have h3 : μ (Set.Ioc a 1) ≤ μ S := measure_mono h_Ioc_sub_S
    have h5 : μ (Set.Ioc a 1) ≥ ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [h4]
      have h6 : 1 - μ (Set.Icc (0 : ℝ) a) ≥ 1 - ENNReal.ofReal (1 / 2 : ℝ) :=
        tsub_le_tsub_left h_μ_Icc0a_le_half 1
      have h7 : 1 - ENNReal.ofReal (1 / 2 : ℝ) = ENNReal.ofReal (1 / 2 : ℝ) := by
        simp <;> norm_num
      rw [h7] at h6
      exact h6
    exact le_trans h5 h3
  have h_μ_S_pos : 0 < μ S := by
    have h1 : (0 : ENNReal) < ENNReal.ofReal (1 / 2 : ℝ) := by positivity
    exact lt_of_lt_of_le h1 h_μ_S_ge
  have h_μ_S_le_one : μ S ≤ 1 := by
    have h1 : μ S ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    rw [hμ_univ] at h1
    exact h1
  have h_μ_S_lt_top : μ S < ⊤ := by
    have h : μ S ≤ 1 := h_μ_S_le_one
    exact lt_of_le_of_lt h (by norm_num)
  have h_μ_S_ne_top : μ S ≠ ⊤ := ne_top_of_lt h_μ_S_lt_top
  rcases hμ.restrict_renormalize hS_meas h_μ_S_pos h_μ_S_lt_top with ⟨ν, hν_frost, hν_supp⟩
  have h_μ_S_real_ge_half : (μ S).toReal ≥ 1 / 2 := by
    have h7 : μ S ≥ ENNReal.ofReal (1 / 2 : ℝ) := h_μ_S_ge
    exact (ENNReal.ofReal_le_iff_le_toReal h_μ_S_ne_top).mp h7
  have h_const_le : C / (μ S).toReal ≤ 2 * C := by
    have h9 : 0 < (μ S).toReal := by positivity
    have h10 : (μ S).toReal ≥ 1 / 2 := h_μ_S_real_ge_half
    calc C / (μ S).toReal
      ≤ C / (1 / 2 : ℝ) := by gcongr
    _ = 2 * C := by ring
  have hν_frost2 : IsAllScaleFrostman κ (2 * C) ν := by
    refine' ⟨hν_frost.1, hν_frost.2.1, by positivity, _⟩
    intro x r hr
    have h11 := hν_frost.2.2.2 x r hr
    calc ν (Set.Icc (x - r) (x + r))
      ≤ ENNReal.ofReal ((C / (μ S).toReal) * r ^ κ) := h11
    _ ≤ ENNReal.ofReal ((2 * C) * r ^ κ) := by gcongr <;> linarith
  have hν_supp_S : ν.support ⊆ S := by
    have h1 : ν.support ⊆ closure S ∩ μ.support := hν_supp
    have h2 : ν.support ⊆ closure S := by
      intro x hx
      have h3 : x ∈ closure S ∩ μ.support := h1 hx
      exact h3.1
    have h3 : closure S = S := IsClosed.closure_eq isClosed_Icc
    rw [h3] at h2
    exact h2
  have hν_supp_mu : ν.support ⊆ μ.support := by
    have h1 : ν.support ⊆ closure S ∩ μ.support := hν_supp
    intro x hx
    have h3 : x ∈ closure S ∩ μ.support := h1 hx
    exact h3.2
  exact ⟨ν, hν_frost2, hν_supp_S, hν_frost.1, hν_supp_mu⟩

/-- **Scaling step**: Given an all-scale `(κ,2C)`-Frostman measure μ' supported
    on `[a,1]` with `a > 0`, scale by `b = sSup(supp μ')` so that `1` is in the
    support. The Frostman constant does not increase since `b ≤ 1`. -/
lemma normalize_support_contains_one
    {κ C : ℝ} (hκ_pos : 0 < κ) (hC_pos : 0 < C)
    (hC_le : C ≤ 2 ^ κ)
    {μ : Measure ℝ} (hμ : IsAllScaleFrostman κ C μ)
    (hμ_supp : μ.support ⊆ Set.Icc 0 1)
    (hμ_univ : μ Set.univ = 1) :
    ∃ (μ'' : Measure ℝ),
      IsAllScaleFrostman κ (2 * C) μ'' ∧
      1 ∈ μ''.support ∧
      μ''.support ⊆ Set.Icc ((2 : ℝ) ^ (-(1/κ))) 1 ∧
      μ'' Set.univ = 1 := by
  rcases step1_normalize_allscale hκ_pos hC_pos hC_le hμ hμ_supp hμ_univ
    with ⟨μ', hμ'_frost, hμ'_supp_Icc, hμ'_univ, _⟩
  let a : ℝ := (2 : ℝ) ^ (-(1/κ))
  have ha_pos : 0 < a := by positivity
  have hμ'_ne_zero : μ' ≠ 0 := by
    intro h
    rw [h] at hμ'_univ
    <;> simp at hμ'_univ <;> norm_num at hμ'_univ
  have hμ'_supp_nonempty : μ'.support.Nonempty :=
    Measure.nonempty_support_iff.mpr hμ'_ne_zero
  have h_bdd_above : BddAbove μ'.support := by
    use 1
    intro x hx
    exact (hμ'_supp_Icc hx).2
  have h_bdd_below : BddBelow μ'.support := by
    use a
    intro x hx
    exact (hμ'_supp_Icc hx).1
  have hIcc_bdd : Bornology.IsBounded (Set.Icc a 1) := by exact Metric.isBounded_Icc a 1
  have hμ'_supp_bdd : Bornology.IsBounded μ'.support :=
    hIcc_bdd.subset hμ'_supp_Icc
  have hμ'_supp_closed : IsClosed μ'.support := Measure.isClosed_support
  let b : ℝ := sSup μ'.support
  have hb_in_supp : b ∈ μ'.support :=
    hμ'_supp_closed.csSup_mem hμ'_supp_nonempty h_bdd_above
  have hb_ge_a : a ≤ b := by
    rcases hμ'_supp_nonempty with ⟨x, hx⟩
    have h2 : a ≤ x := (hμ'_supp_Icc hx).1
    have h3 : x ≤ b := le_csSup h_bdd_above hx
    linarith
  have hb_pos : 0 < b := by linarith [ha_pos]
  have hb_le_one : b ≤ 1 := by
    have h1 : ∀ x ∈ μ'.support, x ≤ 1 := fun x hx => (hμ'_supp_Icc hx).2
    exact csSup_le hμ'_supp_nonempty h1
  let f : ℝ → ℝ := fun x => x / b
  have hf_cont : Continuous f := by fun_prop
  have hf_meas : Measurable f := hf_cont.measurable
  let μ'' : Measure ℝ := Measure.map f μ'
  have hμ''_univ : μ'' Set.univ = 1 := by
    have h_preimage : f ⁻¹' Set.univ = Set.univ := by simp
    rw [Measure.map_apply hf_meas MeasurableSet.univ, h_preimage, hμ'_univ]
  have h_frost' := hμ'_frost.2.2.2
  have h_preimage_eq : ∀ (y r : ℝ),
      f ⁻¹' (Set.Icc (y - r) (y + r)) = Set.Icc (b * y - b * r) (b * y + b * r) := by
    intro y r
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc, f]
    have hb_pos' : 0 < b := hb_pos
    have h_iff : (y - r ≤ x / b ∧ x / b ≤ y + r) ↔
        (b * y - b * r ≤ x ∧ x ≤ b * y + b * r) := by
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · have h : b * (y - r) ≤ b * (x / b) := by gcongr
          have h' : b * (x / b) = x := by field_simp [hb_pos'.ne'] <;> ring
          rw [h'] at h
          have h'' : b * (y - r) = b * y - b * r := by ring
          rw [h''] at h
          exact h
        · have h : b * (x / b) ≤ b * (y + r) := by gcongr
          have h' : b * (x / b) = x := by field_simp [hb_pos'.ne'] <;> ring
          rw [h'] at h
          have h'' : b * (y + r) = b * y + b * r := by ring
          rw [h''] at h
          exact h
      · rintro ⟨h1, h2⟩
        constructor
        · have h : b * (y - r) ≤ x := by
            have h' : b * (y - r) = b * y - b * r := by ring
            rw [h']
            exact h1
          have h'' : (b * (y - r)) / b ≤ x / b := by gcongr
          have h3 : (b * (y - r)) / b = y - r := by field_simp [hb_pos'.ne'] <;> ring
          rw [h3] at h''
          exact h''
        · have h : x ≤ b * (y + r) := by
            have h' : b * (y + r) = b * y + b * r := by ring
            rw [h']
            exact h2
          have h'' : x / b ≤ (b * (y + r)) / b := by gcongr
          have h3 : (b * (y + r)) / b = y + r := by field_simp [hb_pos'.ne'] <;> ring
          rw [h3] at h''
          exact h''
    exact h_iff
  have hμ''_frost : IsAllScaleFrostman κ (2 * C) μ'' := by
    refine' ⟨hμ''_univ, hκ_pos, by positivity, _⟩
    intro y r hr
    have h1 : μ'' (Set.Icc (y - r) (y + r)) =
        μ' (Set.Icc (b * y - b * r) (b * y + b * r)) := by
      rw [Measure.map_apply hf_meas measurableSet_Icc, h_preimage_eq y r]
    rw [h1]
    have h3 : 0 < b * r := mul_pos hb_pos hr
    have h4 := h_frost' (b * y) (b * r) h3
    have h5 : (2 * C) * (b * r) ^ κ ≤ (2 * C) * r ^ κ := by
      have h6 : (b * r) ^ κ ≤ r ^ κ := by
        have h7 : b * r ≤ r := by nlinarith
        gcongr <;> linarith
      gcongr <;> linarith
    calc μ' (Set.Icc (b * y - b * r) (b * y + b * r))
      ≤ ENNReal.ofReal ((2 * C) * (b * r) ^ κ) := h4
    _ ≤ ENNReal.ofReal ((2 * C) * r ^ κ) := by gcongr
  have h_image_supp : f '' μ'.support ⊆ μ''.support := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h_x_in_supp : x ∈ μ'.support := hx
    have h_main : ∀ (U : Set ℝ), U ∈ nhds (f x) → 0 < μ'' U := by
      intro U hU_nhds
      rcases mem_nhds_iff.mp hU_nhds with ⟨V, hV_sub, hV_open, hxV⟩
      have h_preimage_open : IsOpen (f ⁻¹' V) := hf_cont.isOpen_preimage V hV_open
      have h_x_in_preimage : x ∈ f ⁻¹' V := by simpa [f] using hxV
      have h_preimage_nhds : (f ⁻¹' V) ∈ nhds x :=
        h_preimage_open.mem_nhds h_x_in_preimage
      have h_pos : 0 < μ' (f ⁻¹' V) := by
        have h_iff : x ∈ μ'.support ↔ ∀ (W : Set ℝ), W ∈ nhds x → 0 < μ' W :=
          Measure.mem_support_iff_forall x
        exact (h_iff.mp h_x_in_supp) (f ⁻¹' V) h_preimage_nhds
      have h_eq : μ'' V = μ' (f ⁻¹' V) := by
        rw [Measure.map_apply hf_meas hV_open.measurableSet]
      have h_pos_V : 0 < μ'' V := by
        rw [h_eq] <;> exact h_pos
      have h_mono : μ'' V ≤ μ'' U := measure_mono hV_sub
      exact lt_of_lt_of_le h_pos_V h_mono
    have h_iff : f x ∈ μ''.support ↔ ∀ (U : Set ℝ), U ∈ nhds (f x) → 0 < μ'' U :=
      Measure.mem_support_iff_forall (f x)
    exact h_iff.mpr h_main
  have h1_in_supp : 1 ∈ μ''.support := by
    have h_b_in_supp : b ∈ μ'.support := hb_in_supp
    have h_f_b : f b = 1 := by
      simp [f, hb_pos.ne'] <;> field_simp
    have h1 : f b ∈ f '' μ'.support := ⟨b, h_b_in_supp, rfl⟩
    rw [h_f_b] at h1
    exact h_image_supp h1
  have h_supp_subset_image : μ''.support ⊆ f '' μ'.support := by
    let K : Set ℝ := f '' μ'.support
    have hK_compact : IsCompact μ'.support := by exact Metric.isCompact_of_isClosed_isBounded hμ'_supp_closed hμ'_supp_bdd
    have hK_closed : IsClosed K := (hK_compact.image hf_cont).isClosed
    have h2 : μ'.support ⊆ f ⁻¹' K := by
      intro x hx
      exact ⟨x, hx, rfl⟩
    have hK_compl_open : IsOpen Kᶜ := by exact IsClosed.isOpen_compl
    have h3 : μ'' Kᶜ = 0 := by
      rw [Measure.map_apply hf_meas hK_compl_open.measurableSet]
      have h4 : f ⁻¹' Kᶜ ⊆ μ'.supportᶜ := by
        intro z hz
        intro h_contra
        have h5 : f z ∈ K := h2 h_contra
        exact hz h5
      exact measure_mono_null h4 Measure.measure_compl_support
    intro y hy
    by_contra h
    have h5 : Kᶜ ∈ nhds y := hK_compl_open.mem_nhds h
    have h6 : μ'' Kᶜ = 0 := h3
    have h_iff : y ∈ μ''.support ↔ ∀ (U : Set ℝ), U ∈ nhds y → 0 < μ'' U :=
      Measure.mem_support_iff_forall y
    have h7 : ∀ (U : Set ℝ), U ∈ nhds y → 0 < μ'' U := h_iff.mp hy
    have h8 := h7 Kᶜ h5
    rw [h6] at h8
    <;> simp at h8
  have hμ''_supp_Icc : μ''.support ⊆ Set.Icc a 1 := by
    intro y hy
    have h_y_in_image : y ∈ f '' μ'.support := h_supp_subset_image hy
    rcases h_y_in_image with ⟨x, hx, rfl⟩
    have h_x_Icc : x ∈ Set.Icc a 1 := hμ'_supp_Icc hx
    have h_ax : a ≤ x := h_x_Icc.1
    have h_xb : x ≤ b := le_csSup h_bdd_above hx
    have h_fx_ge_a : a ≤ f x := by
      simp only [f]
      have h : a / b ≤ x / b := by gcongr
      have h2 : a ≤ a / b := by
        have h3 : a / b ≥ a := by
          calc a / b
            ≥ a / 1 := by gcongr
          _ = a := by ring
        exact h3
      linarith
    have h_fx_le_one : f x ≤ 1 := by
      simp only [f]
      have h : x / b ≤ 1 := by
        calc x / b
          ≤ b / b := by gcongr
        _ = 1 := by field_simp [hb_pos.ne'] <;> ring
      exact h
    exact ⟨h_fx_ge_a, h_fx_le_one⟩
  exact ⟨μ'', hμ''_frost, h1_in_supp, hμ''_supp_Icc, hμ''_univ⟩

end
end WeakTwoEndsSumProduct
