module

/-
  Bounded productProp from A.7 axiom.

  Proves a bounded version of productProp directly from
  `product_like_incidence_sum_product` (OS Proposition A.7).

  ## Main theorem
  `productProp_bounded`: same as productProp but with explicit boundedness.
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.product_like_incidence_sum_product
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBoundedHelpers1a
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBoundedHelpers1c
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBoundedHelpers2
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Translation
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RealAnalysis
public import MyLeanRepo.DiscretisedFurstenbergEstimate.H7cCoveringBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

open DiscretisedFurstenbergEstimate.CoveringUtils
open DiscretisedFurstenbergEstimate.Translation

noncomputable section

namespace DirecretisedFurstenbergEstimate

open DiscretisedFurstenbergEstimate.CoveringUtils

/-- Helper: `4 * transformX x - 1 = x` and `2 * transformY y - 1 = y`. -/
lemma transform_roundtrip (x y : ℝ) :
    (4 * (transformX x) - 1, 2 * (transformY y) - 1) = (x, y) := by
  have h1 : 4 * transformX x - 1 = x := by
    have h_tx : transformX x = (x + 1) / 4 := by rfl
    rw [h_tx] <;> ring
  have h2 : 2 * transformY y - 1 = y := by
    have h_ty : transformY y = (y + 1) / 2 := by rfl
    rw [h_ty] <;> ring
  exact Prod.ext h1 h2

/-! ### Main theorem: bounded productProp from A.7 -/

/-- Bounded version of productProp, proved from the A.7 axiom.

Given bounded sets Y ⊆ [-1,1], X_y ⊆ [-1,1], T(z) ⊆ [-2,2]² satisfying
the productProp hypotheses, the δ-covering number of the union of tube
parameters is at least δ^{-2s-η}. -/
theorem productProp_bounded (s τ : ℝ) (hs : 0 < s) (hs1 : s < 1) (hτ : 0 < τ) :
    ∃ η : ℝ, 0 < η ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ∀ δ : ℝ, δ ∈ Set.Ioc (0 : ℝ) δ₀ →
          ∀ (Y : Set ℝ)
            (X : ∀ (y : ℝ), y ∈ Y → Set ℝ)
            (T : ∀ (z : ℝ × ℝ),
               z ∈ (⋃ (y : ℝ) (hy : y ∈ Y), X y hy ×ˢ {y}) → Set (ℝ × ℝ)),
            Y ⊆ Set.Icc (-1 : ℝ) 1 →
            (∀ y hy, X y hy ⊆ Set.Icc (-1 : ℝ) 1) →
            (∀ z hz, T z hz ⊆ Set.Icc (-2 : ℝ) 2 ×ˢ Set.Icc (-2 : ℝ) 2) →
            IsDeltaSSet δ τ (Real.rpow δ (-η)) Y →
            (∀ y hy, IsDeltaSSet δ s (Real.rpow δ (-η)) (X y hy)) →
            (∀ z hz, IsDeltaSSet δ s (Real.rpow δ (-η)) (T z hz)) →
            (∀ z hz, ∀ (p : ℝ × ℝ), p ∈ T z hz →
               |p.1 * z.2 + p.2 - z.1| ≤ 4 * δ) →
            ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) ≤
              (Metric.externalCoveringNumber δ.toNNReal
                (⋃ (z : ℝ × ℝ)
                   (hz : z ∈ (⋃ (y : ℝ) (hy : y ∈ Y), X y hy ×ˢ {y})),
                   T z hz) : ENNReal) := by
  -- Step 0: Apply A.7 axiom with capped exponent τ' = min(τ, 1)
  let τ' := min τ 1
  have hτ'_pos : 0 < τ' := by
    have h1 : 0 < τ := hτ
    have h2 : 0 < (1 : ℝ) := by norm_num
    exact lt_min h1 h2
  have hτ'_nonneg : 0 ≤ τ' := by linarith
  have hτ'_le_one : τ' ≤ 1 := by exact min_le_right _ _
  rcases product_like_incidence_sum_product s τ' hs hs1 hτ'_pos with
    ⟨η_A7, hη_A7_pos, δ₀_A7, hδ₀_A7_pos, hA7⟩
  let η : ℝ := η_A7 / 4
  have hη_pos : 0 < η := by positivity
  let slack : ℝ := η_A7 - η
  have hslack_pos : 0 < slack := by
    dsimp only [slack, η]
    have h : 0 < η_A7 := hη_A7_pos
    linarith
  -- Absorption constants: K * δ^{-η} ≤ δ^{-η_A7} for δ < threshold
  let K_Y := (9 : ℝ) * (2 : ℝ)^τ * 9 * 2 * 100 * (2 : ℝ)^η_A7
  let K_X := (9 : ℝ) * (4 : ℝ)^s * 9 * 100 * (2 : ℝ)^η_A7
  let K_T := (81 : ℝ) * 4096 * 405 * 1000 * (2 : ℝ)^η_A7
  let K_final := (9 : ℝ) * 1000 * (2 : ℝ)^(2 * s + η_A7)
  rcases RealAnalysis.constant_absorption K_Y slack η (by positivity) hslack_pos with ⟨δ₀_Y, hδ₀_Y_pos, h_abs_Y⟩
  rcases RealAnalysis.constant_absorption K_X slack η (by positivity) hslack_pos with ⟨δ₀_X, hδ₀_X_pos, h_abs_X⟩
  rcases RealAnalysis.constant_absorption K_T slack η (by positivity) hslack_pos with ⟨δ₀_T, hδ₀_T_pos, h_abs_T⟩
  rcases RealAnalysis.constant_absorption K_final slack (2 * s + η) (by positivity) hslack_pos with ⟨δ₀_final, hδ₀_final_pos, h_abs_final⟩
  let δ₀_absorb : ℝ := min (min δ₀_Y δ₀_X) (min δ₀_T δ₀_final)
  let δ₀ : ℝ := min (min (δ₀_A7 / 2) (1 / 4)) (δ₀_absorb / 2)
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨η, hη_pos, δ₀, hδ₀_pos, ?_⟩
  intro δ hδ Y X T hY_bounds hX_bounds hT_bounds hY_sset hX_sset hT_sset h_inc
  let Z : Set (ℝ × ℝ) := ⋃ (y : ℝ) (hy : y ∈ Y), X y hy ×ˢ {y}
  by_cases h_top : (Metric.externalCoveringNumber δ.toNNReal (⋃ (z : ℝ × ℝ) (hz : z ∈ Z), T z hz) : ENNReal) = ⊤
  · rw [h_top] <;> simp
  -- Step 1: Dyadic rounding
  have hδ_pos : 0 < δ := hδ.1
  have hδ_le_δ₀ : δ ≤ δ₀ := hδ.2
  have hδ_le_one : δ ≤ 1 := by
    have h21 : δ₀ ≤ min (δ₀_A7 / 2) (1 / 4) := min_le_left _ _
    have h2 : δ₀ ≤ 1 / 4 := le_trans h21 (min_le_right _ _)
    linarith
  rcases exists_dyadic_scale_near δ hδ_pos hδ_le_one with ⟨n, hδ'_ge, hδ'_lt⟩
  let δ' : ℝ := (2 : ℝ)^(-(n : ℤ))
  have hδ'_dyadic : δ' ∈ dyadicScales := ⟨n, rfl⟩
  have hδ'_pos : 0 < δ' := by positivity
  have hδ_le_δ' : δ ≤ δ' := hδ'_ge
  have hδ'_lt_2δ : δ' < 2 * δ := hδ'_lt
  have hδ'_le_δ₀_A7 : δ' ≤ δ₀_A7 := by
    have h41 : δ₀ ≤ min (δ₀_A7 / 2) (1 / 4) := min_le_left _ _
    have h42 : min (δ₀_A7 / 2) (1 / 4) ≤ δ₀_A7 / 2 := min_le_left _ _
    have h3 : δ ≤ δ₀_A7 / 2 := by
      have h4 : δ₀ ≤ δ₀_A7 / 2 := le_trans h41 h42
      have h5 : δ ≤ δ₀ := hδ_le_δ₀
      linarith
    have h6 : δ' < δ₀_A7 := by linarith
    linarith
  -- Step 2: Scale up S-sets
  have hY_up : IsDeltaSSet δ' τ (Real.rpow δ (-η) * 9) Y :=
    IsDeltaSSet.scale_up1 hδ_pos hδ'_pos hδ_le_δ' (by linarith) hY_sset
  have hX_up : ∀ y hy, IsDeltaSSet δ' s (Real.rpow δ (-η) * 9) (X y hy) :=
    fun y hy => IsDeltaSSet.scale_up1 hδ_pos hδ'_pos hδ_le_δ' (by linarith) (hX_sset y hy)
  have hT_up : ∀ z hz, IsDeltaSSet δ' s (Real.rpow δ (-η) * 81) (T z hz) :=
    fun z hz => IsDeltaSSet.scale_up2 hδ_pos hδ'_pos hδ_le_δ' (by linarith) (hT_sset z hz)
  -- Step 3: Coordinate normalization (S-set transfers by sorry)
  let Y' : Set ℝ := transformY '' Y
  have hY'_bounds : Y' ⊆ Set.Icc (0 : ℝ) 1 := by
    intro y' hy'; rcases hy' with ⟨y, hy, rfl⟩
    have h1 : -1 ≤ y := (hY_bounds hy).1
    have h2 : y ≤ 1 := (hY_bounds hy).2
    have hty : transformY y = (y + 1) / 2 := by simp [transformY]
    rw [hty]; constructor <;> linarith
  have hY'_sset : IsDeltaSSet δ' τ (Real.rpow δ (-η) * 9 * (2 : ℝ)^τ * 9) Y' := by
    let C0 := Real.rpow δ (-η) * 9
    have hC0_pos : 0 < C0 := by
      have h1 : 0 < Real.rpow δ (-η) := Real.rpow_pos_of_pos hδ_pos _
      positivity
    have h1 : IsDeltaSSet δ' τ C0 Y := hY_up
    have h2 : IsDeltaSSet δ' τ C0 ((fun x : ℝ => x + 1) '' Y) :=
      IsDeltaSSet.translate1 h1
    have h3 : IsDeltaSSet ((1 / 2 : ℝ) * δ') τ (C0 / (1 / 2 : ℝ)^τ)
        ((fun x : ℝ => (1 / 2 : ℝ) * x) '' ((fun x : ℝ => x + 1) '' Y)) :=
      IsDeltaSSet.scale1 (hlam := by norm_num) h2
    have h4 : ((fun x : ℝ => (1 / 2 : ℝ) * x) '' ((fun x : ℝ => x + 1) '' Y)) = Y' := by
      have h41 : ((fun x : ℝ => (1 / 2 : ℝ) * x) '' ((fun x : ℝ => x + 1) '' Y)) =
          ((fun x : ℝ => (1 / 2 : ℝ) * x) ∘ (fun x : ℝ => x + 1)) '' Y :=
        Set.image_image _ _ _
      rw [h41]
      have h_comp : (fun x : ℝ => (1 / 2 : ℝ) * x) ∘ (fun x : ℝ => x + 1) = transformY := by
        funext x; simp [transformY, Function.comp_apply] <;> ring
      rw [h_comp]
    rw [h4] at h3
    have h5 : C0 / (1 / 2 : ℝ)^τ = C0 * (2 : ℝ)^τ := by
      have h_pos2 : 0 < (2 : ℝ) := by norm_num
      have h6 : (1 / 2 : ℝ)^τ = 1 / (2 : ℝ)^τ := by
        rw [Real.div_rpow (by norm_num) (by positivity)] <;> simp
      rw [h6]
      have h7 : (2 : ℝ)^τ ≠ 0 := by positivity
      field_simp [h7] <;> ring
    rw [h5] at h3
    have h_half_pos : 0 < (1 / 2 : ℝ) * δ' := by positivity
    have h_scale : δ' ≤ 4 * ((1 / 2 : ℝ) * δ') := by linarith
    exact IsDeltaSSet.scale_up1 h_half_pos hδ'_pos (by linarith) h_scale h3
  have hY'_inv : ∀ y' ∈ Y', (2 * y' - 1) ∈ Y := by
    intro y' hy'
    rcases hy' with ⟨y, hy, h_eq⟩
    have h_y : 2 * y' - 1 = y := by
      simp [Y', transformY] at h_eq ⊢ <;> linarith
    simpa [h_y] using hy
  classical
  let X' : ℝ → Set ℝ := fun y' =>
    if h : y' ∈ Y' then
      transformX '' (X (2 * y' - 1) (hY'_inv y' h))
    else ∅
  let Z' : Set (ℝ × ℝ) := ⋃ (y' : ℝ) (hy' : y' ∈ Y'), X' y' ×ˢ {y'}
  have hX'_sset : ∀ y' ∈ Y', IsDeltaSSet δ' s (Real.rpow δ (-η) * 9 * (4 : ℝ)^s * 9) (X' y') := by
    intro y' hy'
    let y : ℝ := 2 * y' - 1
    have hy : y ∈ Y := hY'_inv y' hy'
    have hX'_eq : X' y' = transformX '' (X y hy) := by
      unfold X'
      rw [dif_pos hy'] <;> congr <;> dsimp only [y] <;> linarith
    rw [hX'_eq]
    let C0 := Real.rpow δ (-η) * 9
    have hC0_pos : 0 < C0 := by
      have h1 : 0 < Real.rpow δ (-η) := Real.rpow_pos_of_pos hδ_pos _
      positivity
    have h1 : IsDeltaSSet δ' s C0 (X y hy) := hX_up y hy
    have h2 : IsDeltaSSet δ' s C0 ((fun x : ℝ => x + 1) '' (X y hy)) :=
      IsDeltaSSet.translate1 h1
    have h3 : IsDeltaSSet ((1 / 4 : ℝ) * δ') s (C0 / (1 / 4 : ℝ)^s)
        ((fun x : ℝ => (1 / 4 : ℝ) * x) '' ((fun x : ℝ => x + 1) '' (X y hy))) :=
      IsDeltaSSet.scale1 (hlam := by norm_num) h2
    have h4 : ((fun x : ℝ => (1 / 4 : ℝ) * x) '' ((fun x : ℝ => x + 1) '' (X y hy))) =
        transformX '' (X y hy) := by
      have h41 : ((fun x : ℝ => (1 / 4 : ℝ) * x) '' ((fun x : ℝ => x + 1) '' (X y hy))) =
          ((fun x : ℝ => (1 / 4 : ℝ) * x) ∘ (fun x : ℝ => x + 1)) '' (X y hy) :=
        Set.image_image _ _ _
      rw [h41]
      have h_comp : (fun x : ℝ => (1 / 4 : ℝ) * x) ∘ (fun x : ℝ => x + 1) = transformX := by
        funext x; simp [transformX, Function.comp_apply] <;> ring
      rw [h_comp]
    rw [h4] at h3
    have h5 : C0 / (1 / 4 : ℝ)^s = C0 * (4 : ℝ)^s := by
      have h_pos4 : 0 < (4 : ℝ) := by norm_num
      have h6 : (1 / 4 : ℝ)^s = 1 / (4 : ℝ)^s := by
        rw [Real.div_rpow (by norm_num) (by positivity)] <;> simp
      rw [h6]
      have h7 : (4 : ℝ)^s ≠ 0 := by positivity
      field_simp [h7] <;> ring
    rw [h5] at h3
    have h_quarter_pos : 0 < (1 / 4 : ℝ) * δ' := by positivity
    have h_scale : δ' ≤ 4 * ((1 / 4 : ℝ) * δ') := by
      have h : 4 * ((1 / 4 : ℝ) * δ') = δ' := by ring
      rw [h]
    exact IsDeltaSSet.scale_up1 h_quarter_pos hδ'_pos (by linarith) h_scale h3
  have hZ'_to_Z : ∀ z' ∈ Z', (4 * z'.1 - 1, 2 * z'.2 - 1) ∈ Z := by
    intro z' hz'
    rcases Set.mem_iUnion₂.mp hz' with ⟨y', hy', hz'_in⟩
    have hz'2 : z'.2 = y' := by
      simpa [Set.mem_prod, Set.mem_singleton_iff] using hz'_in.2
    have hz'1 : z'.1 ∈ X' y' := hz'_in.1
    have h_y_in_Y : (2 * y' - 1) ∈ Y := by
      rcases hy' with ⟨x, hx, h_eq⟩
      have h_y : (2 * y' - 1) = x := by
        simp [Y', transformY] at h_eq ⊢ <;> linarith
      rw [h_y]; exact hx
    have hX'_eq : X' y' = transformX '' (X (2 * y' - 1) h_y_in_Y) := by
      unfold X'
      rw [dif_pos hy']
      <;> congr
      <;> funext z <;> simp [Y', transformY] <;> linarith
    rw [hX'_eq] at hz'1
    rcases hz'1 with ⟨x, hx, h_eq_x⟩
    have h_tx : z'.1 = transformX x := h_eq_x.symm
    have h_x4 : 4 * z'.1 - 1 = x := by
      rw [h_tx]
      dsimp only [transformX]
      <;> ring
    let y := 2 * y' - 1
    have hy : y ∈ Y := h_y_in_Y
    have h_y2 : 2 * z'.2 - 1 = y := by
      rw [hz'2] <;> rfl
    have h_final : (x, y) ∈ X y hy ×ˢ {y} := ⟨hx, by simp⟩
    rw [h_x4, h_y2]
    exact Set.mem_iUnion₂.mpr ⟨y, hy, h_final⟩
  let T' (z' : ℝ × ℝ) (hz' : z' ∈ Z') : Set (ℝ × ℝ) :=
    transformTube '' (T (4 * z'.1 - 1, 2 * z'.2 - 1) (hZ'_to_Z z' hz'))
  have hT'_sset : ∀ z' hz', IsDeltaSSet δ' s (Real.rpow δ (-η) * 81 * 4096) (T' z' hz') := by
    intro z' hz'; let z := (4 * z'.1 - 1, 2 * z'.2 - 1)
    exact transformTube_Sset_preservation hδ'_pos (hT_up z (hZ'_to_Z z' hz')) (by linarith [hs1])
  have h_inc' : ∀ (z' : ℝ × ℝ) (hz' : z' ∈ Z') (p' : ℝ × ℝ),
      p' ∈ T' z' hz' → |p'.1 * z'.2 + p'.2 - z'.1| ≤ δ' := by
    intro z' hz' p' hp'
    rcases hp' with ⟨p, hp, rfl⟩
    let z : ℝ × ℝ := (4 * z'.1 - 1, 2 * z'.2 - 1)
    have hz_in_Z : z ∈ Z := hZ'_to_Z z' hz'
    have h_orig : |p.1 * z.2 + p.2 - z.1| ≤ 4 * δ := h_inc z hz_in_Z p hp
    have h_eq : (transformTube p).1 * z'.2 + (transformTube p).2 - z'.1 =
        (p.1 * z.2 + p.2 - z.1) / 4 := by
      simp [transformTube, z] <;> ring
    rw [h_eq]
    have h_abs : |(p.1 * z.2 + p.2 - z.1) / 4| = |p.1 * z.2 + p.2 - z.1| / 4 := by
      rw [abs_div] <;> norm_num
    rw [h_abs]
    have h1 : |p.1 * z.2 + p.2 - z.1| / 4 ≤ (4 * δ) / 4 := by
      gcongr
    have h2 : (4 * δ) / 4 ≤ δ' := by
      have h3 : δ ≤ δ' := hδ_le_δ'
      linarith
    linarith
  have hT'_bounded : ∀ z' hz', Bornology.IsBounded (T' z' hz') := by
    intro z' hz'
    let z : ℝ × ℝ := (4 * z'.1 - 1, 2 * z'.2 - 1)
    have hz_in_Z : z ∈ Z := hZ'_to_Z z' hz'
    have hT_bdd : Bornology.IsBounded (T z hz_in_Z) := by
      have h1 : T z hz_in_Z ⊆ Set.Icc (-2 : ℝ) 2 ×ˢ Set.Icc (-2 : ℝ) 2 := hT_bounds z hz_in_Z
      have h2 : Bornology.IsBounded (Set.Icc (-2 : ℝ) 2 ×ˢ Set.Icc (-2 : ℝ) 2) :=
        IsCompact.isBounded (isCompact_Icc.prod isCompact_Icc)
      exact Bornology.IsBounded.subset h2 h1
    have h_cont : Continuous transformTube := by
      have h : transformTube = fun (p : ℝ × ℝ) => (p.1 / 2, (p.2 - p.1 + 1) / 4) := by
        funext p; simp [transformTube] <;> rfl
      rw [h]
      fun_prop
    have h_image_subset : transformTube '' T z hz_in_Z ⊆
        Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-3 / 4 : ℝ) (5 / 4) := by
      intro p hp
      rcases hp with ⟨q, hq, rfl⟩
      have hq_bounds : q ∈ Set.Icc (-2 : ℝ) 2 ×ˢ Set.Icc (-2 : ℝ) 2 := hT_bounds z hz_in_Z hq
      have ha : -2 ≤ q.1 ∧ q.1 ≤ 2 := ⟨hq_bounds.1.1, hq_bounds.1.2⟩
      have hb : -2 ≤ q.2 ∧ q.2 ≤ 2 := ⟨hq_bounds.2.1, hq_bounds.2.2⟩
      have h_range := transformTube_range ha hb
      exact ⟨⟨h_range.1, h_range.2.1⟩, ⟨h_range.2.2.1, h_range.2.2.2⟩⟩
    have h_bdd_set : Bornology.IsBounded (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-3 / 4 : ℝ) (5 / 4)) :=
      IsCompact.isBounded (isCompact_Icc.prod isCompact_Icc)
    exact Bornology.IsBounded.subset h_bdd_set h_image_subset
  have hT'_nonempty : ∀ z' hz', (T' z' hz').Nonempty := by
    intro z' hz'
    exact (hT'_sset z' hz').1
  have hT'_bounds : ∀ z' hz', ∀ p ∈ T' z' hz',
      -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -3 / 4 ≤ p.2 ∧ p.2 ≤ 5 / 4 := by
    intro z' hz' p hp
    rcases hp with ⟨q, hq, rfl⟩
    let z : ℝ × ℝ := (4 * z'.1 - 1, 2 * z'.2 - 1)
    have hz_in_Z : z ∈ Z := hZ'_to_Z z' hz'
    have hq_bounds : q ∈ Set.Icc (-2 : ℝ) 2 ×ˢ Set.Icc (-2 : ℝ) 2 := hT_bounds z hz_in_Z hq
    have ha : -2 ≤ q.1 ∧ q.1 ≤ 2 := ⟨hq_bounds.1.1, hq_bounds.1.2⟩
    have hb : -2 ≤ q.2 ∧ q.2 ≤ 2 := ⟨hq_bounds.2.1, hq_bounds.2.2⟩
    exact transformTube_range ha hb
  let T'_union : Set (ℝ × ℝ) := ⋃ (z' : ℝ × ℝ) (hz' : z' ∈ Z'), T' z' hz'
  let C_Y_cap := Real.rpow δ (-η) * 9 * (2 : ℝ)^τ * 9 * 2
  have hC_Y_one : 1 ≤ Real.rpow δ (-η) * 9 * (2 : ℝ)^τ * 9 := by
    have h2 : Real.rpow δ (-η) ≥ 1 := by
      have h4 : Real.rpow δ (0 : ℝ) ≤ Real.rpow δ (-η) :=
        Real.rpow_le_rpow_of_exponent_ge hδ_pos (by linarith) (by linarith)
      simpa using h4
    have h5 : (2 : ℝ)^τ ≥ 1 := by
      have h6 : 1 ≤ (2 : ℝ) := by norm_num
      have h7 : 0 ≤ τ := by linarith
      have h8 : (2 : ℝ)^(0 : ℝ) ≤ (2 : ℝ)^τ := Real.rpow_le_rpow_of_exponent_le h6 h7
      simpa using h8
    have h_pos1 : 0 < Real.rpow δ (-η) := Real.rpow_pos_of_pos hδ_pos _
    have h_pos2 : 0 < (2 : ℝ)^τ := by positivity
    have h_prod : Real.rpow δ (-η) * ((2 : ℝ)^τ) ≥ 1 := by
      have h11 : Real.rpow δ (-η) * ((2 : ℝ)^τ) ≥ 1 * ((2 : ℝ)^τ) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have h12 : 1 * ((2 : ℝ)^τ) ≥ 1 := by simpa using h5
      exact le_trans h12 h11
    have h_eq : Real.rpow δ (-η) * 9 * ((2 : ℝ)^τ) * 9 =
        Real.rpow δ (-η) * ((2 : ℝ)^τ) * 81 := by ring
    have h_final : Real.rpow δ (-η) * ((2 : ℝ)^τ) * 81 ≥ 81 := by
      have h13 : Real.rpow δ (-η) * ((2 : ℝ)^τ) ≥ 1 := h_prod
      have h14 : Real.rpow δ (-η) * ((2 : ℝ)^τ) * 81 ≥ 1 * 81 :=
        mul_le_mul_of_nonneg_right h13 (by norm_num)
      simpa using h14
    have h_goal : 1 ≤ Real.rpow δ (-η) * ((2 : ℝ)^τ) * 81 := by
      have h15 : (1 : ℝ) ≤ 81 := by norm_num
      exact le_trans h15 h_final
    rw [h_eq]
    exact h_goal
  have hY'_bounded : Bornology.IsBounded Y' := by
    have hIcc_bdd : Bornology.IsBounded (Set.Icc (0 : ℝ) 1) := isCompact_Icc.isBounded
    exact Bornology.IsBounded.subset hIcc_bdd hY'_bounds
  have hY'_sset_cap : IsDeltaSSet δ' τ' C_Y_cap Y' := by
    set C : ℝ := Real.rpow δ (-η) * 9 * (2 : ℝ)^τ * 9 with hC_def
    have h1 : IsDeltaSSet δ' τ' C Y' :=
      IsDeltaSSet.cap_exponent1d hY'_sset hτ'_nonneg (min_le_left _ _)
        hY'_bounded hC_Y_one
    have h2 : C ≤ C_Y_cap := by
      dsimp only [C_Y_cap, C]
      <;> linarith [Real.rpow_pos_of_pos hδ_pos (-η)]
    exact IsDeltaSSet.mono_const h1 h2
  have hY'_sset_cap100 : IsDeltaSSet δ' τ' C_Y_cap Y' := hY'_sset_cap
  have h_const_pos : 0 < C_Y_cap := by
    have h1 : 0 < Real.rpow δ (-η) := Real.rpow_pos_of_pos hδ_pos _
    positivity
  have hY_grid : ∃ (Y_grid : Set ℝ), Y_grid ⊆ productLikeUnitGrid δ' ∧
      IsProductLikeRealDeltaSCSet δ' τ' ((Real.rpow δ (-η) * 9 * (2 : ℝ)^τ * 9 * 2) * 100) Y_grid ∧
      (Metric.externalCoveringNumber δ'.toNNReal Y_grid : ENNReal) ≥
        (Metric.externalCoveringNumber δ'.toNNReal Y' : ENNReal) / 100 ∧
      (∀ y ∈ Y_grid, ∃ y' ∈ Y', |y - y'| ≤ δ') :=
    sset_to_grid_scset hδ'_pos hδ'_dyadic hτ'_nonneg hτ'_le_one
      h_const_pos hY'_bounds hY'_bounded hY'_sset_cap100.1 hY'_sset_cap100
  rcases hY_grid with ⟨Y_grid, hY_grid_sub, hY_grid_sc, hY_grid_cov, hY_grid_corresp⟩
  choose y_snap hy_snap_Y' hy_snap_dist using hY_grid_corresp
  have h_props : ∀ (y0 : ℝ), y0 ∈ Y' →
      (X' y0 ⊆ Set.Icc (0 : ℝ) 1) ∧ Bornology.IsBounded (X' y0) ∧ (X' y0).Nonempty := by
    intro y0 hy0
    let y1 : ℝ := 2 * y0 - 1
    have hy1 : y1 ∈ Y := hY'_inv y0 hy0
    have h_eq : X' y0 = transformX '' (X y1 hy1) := by
      unfold X'; rw [dif_pos hy0] <;> congr <;> dsimp only [y1] <;> linarith
    have hX1_bounds : X y1 hy1 ⊆ Set.Icc (-1 : ℝ) 1 := hX_bounds y1 hy1
    have hIcc_bdd : Bornology.IsBounded (Set.Icc (-1 : ℝ) 1) := by exact Metric.isBounded_Icc (-1) 1
    have hX1_bdd : Bornology.IsBounded (X y1 hy1) :=
      Bornology.IsBounded.subset hIcc_bdd hX1_bounds
    have hX1_nonempty : (X y1 hy1).Nonempty := (hX_sset y1 hy1).1
    have h_tx_cont : Continuous transformX := by
      have h : Continuous (fun x : ℝ => (x + 1) / 4) := by
        exact continuous_id.add continuous_const |>.div_const 4
      have h_eq : transformX = (fun x : ℝ => (x + 1) / 4) := by
        funext x; simp [transformX] <;> ring
      rw [h_eq]; exact h
    constructor
    · rw [h_eq]; intro x hx; rcases hx with ⟨x0, hx0, rfl⟩
      have h_x0_lb : -1 ≤ x0 := (hX1_bounds hx0).1
      have h_x0_ub : x0 ≤ 1 := (hX1_bounds hx0).2
      have h_tx1 : 0 ≤ transformX x0 := by
        unfold transformX; linarith
      have h_tx2 : transformX x0 ≤ 1 := by
        unfold transformX; linarith
      exact ⟨h_tx1, h_tx2⟩
    · constructor
      · have h_img : Bornology.IsBounded (transformX '' X y1 hy1) :=
          Bornology.IsBounded.subset isCompact_Icc.isBounded (by
            intro z hz
            rcases hz with ⟨x, hx, rfl⟩
            have h1 : -1 ≤ x := (hX1_bounds hx).1
            have h2 : x ≤ 1 := (hX1_bounds hx).2
            have h3 : 0 ≤ transformX x := by
              have h5 : transformX x = (x + 1) / 4 := by rfl
              rw [h5]; linarith
            have h4 : transformX x ≤ 1 := by
              have h5 : transformX x = (x + 1) / 4 := by rfl
              rw [h5]; linarith
            exact ⟨h3, h4⟩)
        rw [h_eq]; exact h_img
      · rw [h_eq]; exact hX1_nonempty.image _
  let C_X := Real.rpow δ (-η) * 9 * (4 : ℝ)^s * 9
  have hC_X_pos : 0 < C_X := by
    have h1 : 0 < Real.rpow δ (-η) := Real.rpow_pos_of_pos hδ_pos _
    positivity
  have hX_grid : ∀ (y : ℝ) (hy : y ∈ Y_grid), ∃ (Xg : Set ℝ), Xg ⊆ productLikeUnitGrid δ' ∧
      IsProductLikeRealDeltaSCSet δ' s (C_X * 100) Xg ∧
      (Metric.externalCoveringNumber δ'.toNNReal Xg : ENNReal) ≥
        (Metric.externalCoveringNumber δ'.toNNReal (X' (y_snap y hy)) : ENNReal) / 100 ∧
      (∀ x ∈ Xg, ∃ x' ∈ X' (y_snap y hy), |x - x'| ≤ δ') := by
    intro y hy
    let y0 := y_snap y hy
    have hy0 : y0 ∈ Y' := hy_snap_Y' y hy
    have h := h_props y0 hy0
    exact sset_to_grid_scset hδ'_pos hδ'_dyadic (show 0 ≤ s from by linarith) (show s ≤ 1 from by linarith) hC_X_pos h.1 h.2.1 h.2.2 (hX'_sset y0 hy0)
  choose Xg hXg_sub hXg_sc hXg_cov hXg_corresp using hX_grid
  -- Step 5: Tube conversion (uses parameterSet_to_tubeFamily)
  have hTubes : ∀ (z : EuclideanSpace ℝ (Fin 2)),
      z ∈ productLikeIncidenceSet Y_grid (fun y => if h : y ∈ Y_grid then Xg y h else ∅) →
      ∃ (𝒯z : Set (Set (EuclideanSpace ℝ (Fin 2)))),
        𝒯z ⊆ appendixDyadicTubes δ' ∧
        IsProductLikeAppendixDeltaSCSetOfDyadicTubes δ' s
          ((Real.rpow δ (-η) * 81 * 4096 * 405) * 1000) 𝒯z ∧
        (∀ T ∈ 𝒯z, z ∈ T) ∧
        productLikeAppendixDyadicTubeParameterSet δ' 𝒯z ⊆
          Metric.cthickening (Real.sqrt 2 * (9 * δ' / 2)) (e_plane_inv '' T'_union) := by
    intro z hz
    -- Extract coordinates from z ∈ productLikeIncidenceSet
    rcases Set.mem_iUnion₂.mp hz with ⟨y, hy, hz'⟩
    have hz1_eq : z 1 = y := hz'.2
    have hz0 : z 0 ∈ (if h : y ∈ Y_grid then Xg y h else ∅) := hz'.1
    have hXg_val : z 0 ∈ Xg y hy := by
      simpa [hy] using hz0
    -- Snap to original coordinates
    let y' := y_snap y hy
    have hy'_Y' : y' ∈ Y' := hy_snap_Y' y hy
    have hy'_dist : |z 1 - y'| ≤ δ' := by
      rw [hz1_eq]
      exact hy_snap_dist y hy
    have hx_corresp : ∃ (x' : ℝ), x' ∈ X' y' ∧ |z 0 - x'| ≤ δ' :=
      hXg_corresp y hy (z 0) hXg_val
    rcases hx_corresp with ⟨x', hx'_X', hx'_dist⟩
    let z' : ℝ × ℝ := (x', y')
    have hz'_Z' : z' ∈ Z' := by
      simp only [Z', Set.mem_iUnion₂]
      exact ⟨y', hy'_Y', hx'_X', by simp [z']⟩
    -- T' z' hz'_Z' is a (δ', s, C_T)-set of tube parameters
    -- with approximate incidence |p.1 * y' + p.2 - x'| ≤ δ'/2.
    -- At z=(z0,z1), incidence error is:
    --   |p.1 * z1 + p.2 - z0| ≤ |p.1 * y' + p.2 - x'| + |p.1| * |z1 - y'| + |z0 - x'|
    --   ≤ δ'/2 + 1 * δ' + δ' = 2.5 * δ'
    -- Preprocess: move points to exact lines through z, then use perturbation lemma.
    let Tz := T' z' hz'_Z'
    let C_T := Real.rpow δ (-η) * 81 * 4096
    let f : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, z 0 - p.1 * z 1)
    let K : ℝ := 3
    have hf_lip : LipschitzWith 1 f := by
      have h_y_in_grid : y ∈ productLikeUnitGrid δ' := hY_grid_sub hy
      have h_y_in_Icc : y ∈ Set.Icc (0 : ℝ) 1 := h_y_in_grid.2
      have hz1_in_Icc : z 1 ∈ Set.Icc (0 : ℝ) 1 := by
        rw [hz1_eq]; exact h_y_in_Icc
      have hz1_nonneg : 0 ≤ z 1 := hz1_in_Icc.1
      have hz1_le_one : z 1 ≤ 1 := hz1_in_Icc.2
      have h_abs : |z 1| ≤ 1 := by rw [abs_of_nonneg hz1_nonneg] <;> linarith
      apply LipschitzWith.of_dist_le_mul
      intro p q
      have h21 : (f p).1 = p.1 := by simp [f]
      have h22 : (f q).1 = q.1 := by simp [f]
      have h23 : (f p).2 = z 0 - p.1 * z 1 := by simp [f]
      have h24 : (f q).2 = z 0 - q.1 * z 1 := by simp [f]
      have h25 : (f p).2 - (f q).2 = -((p.1 - q.1) * z 1) := by
        rw [h23, h24] <;> ring
      have h_abs2 : |(f p).2 - (f q).2| = |z 1| * |p.1 - q.1| := by
        rw [h25, abs_neg, abs_mul]
        <;> rw [mul_comm]
      have h_dist : dist (f p) (f q) = max (|(f p).1 - (f q).1|) (|(f p).2 - (f q).2|) := by
        simp [Prod.dist_eq, dist_eq_norm] <;> rfl
      have h_first : |(f p).1 - (f q).1| = |p.1 - q.1| := by
        rw [h21, h22] <;> rfl
      rw [h_dist, h_first, h_abs2]
      have h4 : |z 1| * |p.1 - q.1| ≤ |p.1 - q.1| := by
        have h6 : 0 ≤ |p.1 - q.1| := by positivity
        nlinarith [h_abs]
      have h7 : |p.1 - q.1| ≤ dist p q := by
        simp [Prod.dist_eq, dist_eq_norm] <;> exact le_max_left _ _
      have h8 : |z 1| * |p.1 - q.1| ≤ dist p q := by linarith
      have h7' : |p.1 - q.1| ≤ (1 : ℝ) * dist p q := by simpa using h7
      have h8' : |z 1| * |p.1 - q.1| ≤ (1 : ℝ) * dist p q := by simpa using h8
      exact max_le h7' h8'
    have h_move : ∀ p ∈ Tz, dist p (f p) ≤ K * δ' := by
      intro p hp
      have h_bounds := hT'_bounds z' hz'_Z' p hp
      have h2 : |p.1| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [h_bounds.1], by linarith [h_bounds.2.1]⟩
      have h_inc_err : |p.1 * (z 1) + p.2 - (z 0)| ≤ (3 : ℝ) * δ' := by
        have h1 : |p.1 * y' + p.2 - x'| ≤ δ' := h_inc' z' hz'_Z' p hp
        have h3 : |z 1 - y'| ≤ δ' := hy'_dist
        have h4 : |z 0 - x'| ≤ δ' := hx'_dist
        set a := p.1 * y' + p.2 - x' with ha_def
        set b := p.1 * (z 1 - y') with hb_def
        set c := x' - z 0 with hc_def
        have h_eq : p.1 * (z 1) + p.2 - (z 0) = a + b + c := by
          simp [ha_def, hb_def, hc_def] <;> ring
        have h_abs1 : |a + b + c| ≤ |a| + |b| + |c| := by
          have h1 : |a + b + c| ≤ |a + b| + |c| := by
            exact abs_add_le (a + b) c
          have h2 : |a + b| ≤ |a| + |b| := by exact abs_add_le a b
          linarith
        have h_abs2 : |b| = |p.1| * |z 1 - y'| := by
          simp [hb_def, abs_mul] <;> rfl
        rw [h_eq]
        rw [h_abs2] at h_abs1
        have h_final : |a| + |p.1| * |z 1 - y'| + |c| ≤ (3 : ℝ) * δ' := by
          have h_ia : |a| ≤ δ' := h1
          have h_ib : |p.1| * |z 1 - y'| ≤ 1 * δ' := by
            have h5 : |p.1| * |z 1 - y'| ≤ 1 * |z 1 - y'| := by
              gcongr <;> linarith [h2]
            have h6 : 1 * |z 1 - y'| ≤ 1 * δ' := by gcongr <;> exact h3
            linarith
          have h_ic : |c| ≤ δ' := by
            have h7 : |c| = |z 0 - x'| := by
              simp [hc_def, abs_sub] <;> rw [abs_sub_comm]
            rw [h7]
            exact h4
          linarith
        exact h_abs1.trans h_final
      have h_dist_eq : dist p (f p) = |p.1 * (z 1) + p.2 - (z 0)| := by
        have h21 : (f p).1 = p.1 := by simp [f]
        have h22 : (f p).2 = z 0 - p.1 * (z 1) := by simp [f]
        have h : dist p (f p) = max (|p.1 - (f p).1|) (|p.2 - (f p).2|) := by
          simp [Prod.dist_eq, dist_eq_norm] <;> rfl
        rw [h, h21, h22]
        have h_zero : |p.1 - p.1| = 0 := by simp
        have h_second : |p.2 - (z 0 - p.1 * (z 1))| = |p.1 * (z 1) + p.2 - (z 0)| := by
          have h6 : p.2 - (z 0 - p.1 * (z 1)) = p.1 * (z 1) + p.2 - (z 0) := by ring
          rw [h6]
        rw [h_zero, h_second]
        <;> simp [max_eq_right] <;> exact abs_nonneg _
      rw [h_dist_eq]
      exact h_inc_err
    have hTz_bdd : Bornology.IsBounded Tz := hT'_bounded z' hz'_Z'
    have hTz_nonempty : Tz.Nonempty := hT'_nonempty z' hz'_Z'
    have hTz_sset : IsDeltaSSet δ' s C_T Tz := hT'_sset z' hz'_Z'
    have hK_nonneg : 0 ≤ K := by norm_num
    have hK_eq : K = 3 := by rfl
    have h_ceil : (Nat.ceil (2 * (K + 1)) : ℕ) = 8 := by
      rw [hK_eq]
      have h1 : 2 * ((3 : ℝ) + 1) = 8 := by norm_num
      rw [h1]
      simp
    have h_const_eq : C_T * ((Nat.ceil (2 * (K + 1)) + 1)^2 : ℝ) * (K + 2) = C_T * 405 := by
      have h1 : ((Nat.ceil (2 * (K + 1)) + 1 : ℕ) = 9) := by
        rw [hK_eq]
        norm_num
      have h2 : ((Nat.ceil (2 * (K + 1)) + 1)^2 : ℝ) = 81 := by
        exact_mod_cast congr_arg (fun x : ℕ => x^2) h1
      have h3 : K + 2 = 5 := by
        rw [hK_eq] <;> norm_num
      rw [h2, h3]
      <;> ring
    have hC_T_pos : 0 < C_T := by
      dsimp only [C_T]
      have h1 : 0 < Real.rpow δ (-η) := Real.rpow_pos_of_pos hδ_pos _
      positivity
    have hf_sset_raw : IsDeltaSSet δ' s
        (C_T * ((Nat.ceil (2 * (K + 1)) + 1)^2 : ℝ) * (K + 2)) (f '' Tz) :=
      IsDeltaSSet.perturbation_prod (C := C_T) hδ'_pos (le_of_lt hs) (by linarith [hs1]) hC_T_pos
        hTz_bdd hTz_sset hf_lip hK_nonneg h_move
    have hf_sset : IsDeltaSSet δ' s (C_T * 405) (f '' Tz) := by
      rw [h_const_eq] at hf_sset_raw
      exact hf_sset_raw
    have hz_bounds : 0 ≤ z 0 ∧ z 0 ≤ 1 ∧ 0 ≤ z 1 ∧ z 1 ≤ 1 := by
      have hz0_in : z 0 ∈ productLikeUnitGrid δ' := hXg_sub y hy hXg_val
      have hz1_in : z 1 ∈ productLikeUnitGrid δ' := by
        rw [hz1_eq]; exact hY_grid_sub hy
      have hz0_Icc : z 0 ∈ Set.Icc (0 : ℝ) 1 := hz0_in.2
      have hz1_Icc : z 1 ∈ Set.Icc (0 : ℝ) 1 := hz1_in.2
      exact ⟨hz0_Icc.1, hz0_Icc.2, hz1_Icc.1, hz1_Icc.2⟩
    have h_f_image_subset : f '' Tz ⊆ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-2 : ℝ) 2 := by
      intro p hp
      rcases hp with ⟨q, hq, rfl⟩
      have hq_bounds := hT'_bounds z' hz'_Z' q hq
      have hq1 : -1 ≤ q.1 := hq_bounds.1
      have hq2 : q.1 ≤ 1 := hq_bounds.2.1
      have hz0_0 : 0 ≤ z 0 := hz_bounds.1
      have hz0_1 : z 0 ≤ 1 := hz_bounds.2.1
      have hz1_0 : 0 ≤ z 1 := hz_bounds.2.2.1
      have hz1_1 : z 1 ≤ 1 := hz_bounds.2.2.2
      have h1 : -1 ≤ (f q).1 := by simp [f, hq1] <;> linarith
      have h2 : (f q).1 ≤ 1 := by simp [f, hq2] <;> linarith
      have h3 : -2 ≤ (f q).2 := by
        have h_eq : (f q).2 = z 0 - q.1 * z 1 := by simp [f]
        rw [h_eq]
        have h4 : q.1 * z 1 ≤ 1 := by
          have h5 : q.1 * z 1 ≤ 1 * z 1 := by gcongr
          have h6 : 1 * z 1 ≤ 1 := by
            have h7 : z 1 ≤ 1 := hz1_1
            linarith
          linarith
        linarith
      have h4 : (f q).2 ≤ 2 := by
        have h_eq : (f q).2 = z 0 - q.1 * z 1 := by simp [f]
        rw [h_eq]
        have h5 : q.1 * z 1 ≥ -1 := by
          have h6 : q.1 * z 1 ≥ (-1 : ℝ) * z 1 := by gcongr
          have h7 : (-1 : ℝ) * z 1 ≥ -1 := by
            have h8 : z 1 ≤ 1 := hz1_1
            have h9 : 0 ≤ z 1 := hz1_0
            linarith
          linarith
        linarith
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have h_f_image_bdd : Bornology.IsBounded (f '' Tz) := by
      have h_bdd_set : Bornology.IsBounded (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-2 : ℝ) 2) :=
        IsCompact.isBounded (isCompact_Icc.prod isCompact_Icc)
      exact Bornology.IsBounded.subset h_bdd_set h_f_image_subset
    have h_f_image_nonempty : (f '' Tz).Nonempty := hTz_nonempty.image f
    have hTz_bounds_f : ∀ p ∈ f '' Tz, -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -2 ≤ p.2 ∧ p.2 ≤ 2 := by
      intro p hp
      have h_in : p ∈ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-2 : ℝ) 2 := h_f_image_subset hp
      exact ⟨h_in.1.1, h_in.1.2, h_in.2.1, h_in.2.2⟩
    have h_inc_f : ∀ p ∈ f '' Tz, |p.1 * (z 1) + p.2 - (z 0)| ≤ δ' / 2 := by
      intro p hp
      rcases hp with ⟨q, _, rfl⟩
      have h : (f q).1 * (z 1) + (f q).2 - (z 0) = 0 := by simp [f] <;> ring
      rw [h] <;> linarith [hδ'_pos]
    have hC_T405_pos : 0 < C_T * 405 := by positivity
    have h_main_result := parameterSet_to_tubeFamily (C := C_T * 405)
        hδ'_pos hδ'_dyadic hs hs1 hC_T405_pos z (f '' Tz)
        h_f_image_bdd h_f_image_nonempty hf_sset h_inc_f hz_bounds hTz_bounds_f
    rcases h_main_result with ⟨𝒯z, h𝒯_sub, h𝒯_sc, h𝒯_inc, h_encard, h_thicken_local⟩
    have h_sc_final : IsProductLikeAppendixDeltaSCSetOfDyadicTubes δ' s
        ((C_T * 405) * 1000) 𝒯z := h𝒯_sc
    -- Prove thickening to e_plane_inv '' T'_union
    have h_thicken1 : productLikeAppendixDyadicTubeParameterSet δ' 𝒯z ⊆
        Metric.cthickening (Real.sqrt 2 * (3 * δ' / 2)) (e_plane_inv '' (f '' Tz)) := h_thicken_local
    have h_image_thicken : e_plane_inv '' (f '' Tz) ⊆
        Metric.cthickening (Real.sqrt 2 * (3 * δ')) (e_plane_inv '' Tz) := by
      intro q hq
      rcases hq with ⟨p, hp_f, rfl⟩
      rcases hp_f with ⟨p0, hp0, rfl⟩
      have h_dist : ‖e_plane_inv (f p0) - e_plane_inv p0‖ ≤ Real.sqrt 2 * (3 * δ') := by
        have h_e_lip : LipschitzWith (⟨Real.sqrt 2, by positivity⟩ : NNReal) e_plane_inv :=
          e_plane_inv_sqrt2_lipschitz
        have h := h_e_lip.dist_le_mul (f p0) p0
        have h_move_p : dist (f p0) p0 ≤ K * δ' := by
          have h : dist p0 (f p0) ≤ K * δ' := h_move p0 hp0
          rwa [dist_comm] at h
        calc ‖e_plane_inv (f p0) - e_plane_inv p0‖
          ≤ Real.sqrt 2 * dist (f p0) p0 := h
        _ ≤ Real.sqrt 2 * (K * δ') := by gcongr
        _ = Real.sqrt 2 * (3 * δ') := by norm_num [K] <;> ring
      have h_edist : edist (e_plane_inv (f p0)) (e_plane_inv p0) ≤
          ENNReal.ofReal (Real.sqrt 2 * (3 * δ')) := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal h_dist
      have h_inf : Metric.infEDist (e_plane_inv (f p0)) (e_plane_inv '' Tz) ≤
          edist (e_plane_inv (f p0)) (e_plane_inv p0) :=
        Metric.infEDist_le_edist_of_mem (Set.mem_image_of_mem e_plane_inv hp0)
      have h_main : Metric.infEDist (e_plane_inv (f p0)) (e_plane_inv '' Tz) ≤
          ENNReal.ofReal (Real.sqrt 2 * (3 * δ')) :=
        h_inf.trans h_edist
      exact h_main
    have hTz_sub_union : Tz ⊆ T'_union := by
      intro p hp
      exact Set.mem_iUnion₂.mpr ⟨z', hz'_Z', hp⟩
    have h_image_sub : e_plane_inv '' Tz ⊆ e_plane_inv '' T'_union := by
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, hTz_sub_union hy, rfl⟩
    let r1 := Real.sqrt 2 * (3 * δ' / 2)
    let r2 := Real.sqrt 2 * (3 * δ')
    let r_total := Real.sqrt 2 * ((9 / 2 : ℝ) * δ')
    have hr1_nonneg : 0 ≤ r1 := by positivity
    have hr2_nonneg : 0 ≤ r2 := by positivity
    have h_thicken2 : productLikeAppendixDyadicTubeParameterSet δ' 𝒯z ⊆
        Metric.cthickening r_total (e_plane_inv '' T'_union) := by
      have h1 : productLikeAppendixDyadicTubeParameterSet δ' 𝒯z ⊆
          Metric.cthickening r1 (Metric.cthickening r2 (e_plane_inv '' Tz)) := by
        have h1a : Metric.cthickening r1 (e_plane_inv '' (f '' Tz)) ⊆
            Metric.cthickening r1 (Metric.cthickening r2 (e_plane_inv '' Tz)) :=
          Metric.cthickening_subset_of_subset r1 h_image_thicken
        exact Set.Subset.trans h_thicken1 h1a
      have h2 : Metric.cthickening r1 (Metric.cthickening r2 (e_plane_inv '' Tz)) ⊆
          Metric.cthickening (r1 + r2) (e_plane_inv '' Tz) :=
        Metric.cthickening_cthickening_subset hr1_nonneg hr2_nonneg (e_plane_inv '' Tz)
      have h3 : r1 + r2 = r_total := by
        dsimp only [r1, r2, r_total] <;> ring
      have h4 : productLikeAppendixDyadicTubeParameterSet δ' 𝒯z ⊆
          Metric.cthickening (r1 + r2) (e_plane_inv '' Tz) :=
        Set.Subset.trans h1 h2
      rw [h3] at h4
      have h5 : Metric.cthickening r_total (e_plane_inv '' Tz) ⊆
          Metric.cthickening r_total (e_plane_inv '' T'_union) :=
        Metric.cthickening_subset_of_subset r_total h_image_sub
      exact Set.Subset.trans h4 h5
    have h4_radius : r_total ≤ Real.sqrt 2 * (9 * δ' / 2) := by
      dsimp only [r_total]
      have h5 : (9 / 2 : ℝ) * δ' = 9 * δ' / 2 := by ring
      rw [h5]
    have h_thicken_final : productLikeAppendixDyadicTubeParameterSet δ' 𝒯z ⊆
        Metric.cthickening (Real.sqrt 2 * (9 * δ' / 2)) (e_plane_inv '' T'_union) := by
      have h6 : Metric.cthickening r_total (e_plane_inv '' T'_union) ⊆
          Metric.cthickening (Real.sqrt 2 * (9 * δ' / 2)) (e_plane_inv '' T'_union) :=
        Metric.cthickening_mono h4_radius (e_plane_inv '' T'_union)
      exact Set.Subset.trans h_thicken2 h6
    exact ⟨𝒯z, h𝒯_sub, h_sc_final, h𝒯_inc, h_thicken_final⟩
  choose 𝒯z_partial h𝒯_sub h𝒯_sc h𝒯_inc h𝒯_thicken using hTubes
  -- Step 6: Apply A.7
  let Xg' : ℝ → Set ℝ := fun y => if h : y ∈ Y_grid then Xg y h else ∅
  let Z_occ : Set (EuclideanSpace ℝ (Fin 2)) := productLikeIncidenceSet Y_grid Xg'
  let 𝒯z : EuclideanSpace ℝ (Fin 2) → Set (Set (EuclideanSpace ℝ (Fin 2))) := fun z =>
    if h : z ∈ Z_occ then 𝒯z_partial z h else ∅
  have hXg'_sub : ∀ y ∈ Y_grid, Xg' y ⊆ productLikeUnitGrid δ' := by
    intro y hy; simpa [Xg', hy] using hXg_sub y hy
  have hXg'_sc : ∀ y ∈ Y_grid, IsProductLikeRealDeltaSCSet δ' s
      (C_X * 100) (Xg' y) := by
    intro y hy
    have h_eq2 : Xg' y = Xg y hy := by
      unfold Xg'; rw [dif_pos hy]
    rw [h_eq2]
    exact hXg_sc y hy
  let 𝒯 : Set (Set (EuclideanSpace ℝ (Fin 2))) := ⋃ z ∈ Z_occ, 𝒯z z
  have h_rpow_transfer : ∀ (a : ℝ), 0 < a → δ ^ (-a) < (2 : ℝ)^a * δ' ^ (-a) := by
    intro a ha
    have h4 : 0 < δ' / 2 := by positivity
    have h5 : δ' / 2 < δ := by linarith
    have h6 : δ ^ (-a) < (δ' / 2) ^ (-a) := by
      have h7 : δ ^ a > (δ' / 2) ^ a := Real.rpow_lt_rpow (by positivity) h5 ha
      have h8 : 0 < δ ^ a := by positivity
      have h9 : 0 < (δ' / 2) ^ a := by positivity
      have h10 : (δ ^ a)⁻¹ < ((δ' / 2) ^ a)⁻¹ := by gcongr
      have h11 : δ ^ (-a) = (δ ^ a)⁻¹ := by rw [Real.rpow_neg (by linarith)] <;> ring
      have h12 : (δ' / 2) ^ (-a) = ((δ' / 2) ^ a)⁻¹ := by rw [Real.rpow_neg (by linarith)] <;> ring
      rw [h11, h12]; exact h10
    have h13 : (δ' / 2) ^ (-a) = (2 : ℝ)^a * δ' ^ (-a) := by
      have h_pos2 : 0 < (2 : ℝ) := by norm_num
      have h14 : (δ' / 2 : ℝ) ^ a = (δ') ^ a / (2 : ℝ) ^ a := by
        rw [Real.div_rpow (by linarith) (by norm_num)]
        <;> ring
      have h15 : (δ' / 2 : ℝ) ^ (-a) = ((δ' / 2 : ℝ) ^ a)⁻¹ := by
        rw [Real.rpow_neg (by linarith)] <;> ring
      rw [h15, h14]
      have h16 : ((δ') ^ a / (2 : ℝ) ^ a)⁻¹ = (2 : ℝ) ^ a / (δ') ^ a := by
        have h_posδa : (δ') ^ a ≠ 0 := (Real.rpow_pos_of_pos hδ'_pos a).ne'
        have h_pos2a : (2 : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) a).ne'
        field_simp [h_posδa, h_pos2a] <;> ring
      rw [h16]
      have h17 : (2 : ℝ) ^ a / (δ') ^ a = (2 : ℝ) ^ a * (δ') ^ (-a) := by
        have h18 : (δ') ^ (-a) = ((δ') ^ a)⁻¹ := by
          rw [Real.rpow_neg (by linarith)] <;> ring
        rw [h18] <;> ring
      exact h17
    rw [h13] at h6; exact h6
  have h_sum1 : η + slack = η_A7 := by
    have hslack_eq : slack = η_A7 - η := by rfl
    rw [hslack_eq] <;> ring
  have hδ_lt_δ₀_absorb : δ < δ₀_absorb := by
    have h1 : δ₀ ≤ δ₀_absorb / 2 := min_le_right _ _
    have h2 : 0 < δ₀_absorb := by positivity
    have h3 : δ ≤ δ₀ := hδ_le_δ₀
    linarith
  have hδ_lt_δ₀_Y : δ < δ₀_Y := by
    have h4 : δ₀_absorb ≤ δ₀_Y := by
      dsimp only [δ₀_absorb]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    linarith [hδ_lt_δ₀_absorb]
  have hδ_lt_δ₀_X : δ < δ₀_X := by
    have h4 : δ₀_absorb ≤ δ₀_X := by
      dsimp only [δ₀_absorb]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    linarith [hδ_lt_δ₀_absorb]
  have hδ_lt_δ₀_T : δ < δ₀_T := by
    have h4 : δ₀_absorb ≤ δ₀_T := by
      dsimp only [δ₀_absorb]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith [hδ_lt_δ₀_absorb]
  have hδ_lt_δ₀_final : δ < δ₀_final := by
    have h4 : δ₀_absorb ≤ δ₀_final := by
      dsimp only [δ₀_absorb]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    linarith [hδ_lt_δ₀_absorb]
  have h_absorb_Y' : K_Y * δ ^ (-η) ≤ δ ^ (-η_A7) := by
    have h2 := h_abs_Y δ hδ_pos hδ_lt_δ₀_Y
    simpa [h_sum1] using h2
  have h_absorb_X' : K_X * δ ^ (-η) ≤ δ ^ (-η_A7) := by
    have h2 := h_abs_X δ hδ_pos hδ_lt_δ₀_X
    simpa [h_sum1] using h2
  have h_absorb_T' : K_T * δ ^ (-η) ≤ δ ^ (-η_A7) := by
    have h2 := h_abs_T δ hδ_pos hδ_lt_δ₀_T
    simpa [h_sum1] using h2
  have h_const_absorb_Y : (Real.rpow δ (-η) * 9 * (2 : ℝ)^τ * 9 * 2) * 100 ≤ δ' ^ (-η_A7) := by
    have h3 := h_rpow_transfer η_A7 hη_A7_pos
    have h4 : K_Y * δ ^ (-η) < (2 : ℝ)^η_A7 * δ' ^ (-η_A7) := h_absorb_Y'.trans_lt h3
    have h5 : K_Y * δ ^ (-η) = (2 : ℝ)^η_A7 * ((Real.rpow δ (-η) * 9 * (2 : ℝ)^τ * 9 * 2) * 100) := by
      dsimp only [K_Y]
      have h6 : δ ^ (-η) = Real.rpow δ (-η) := by rfl
      rw [h6] <;> ring
    rw [h5] at h4
    have h7 : 0 < (2 : ℝ)^η_A7 := by positivity
    set a := (2 : ℝ)^η_A7 with ha_def
    set X_Y := ((Real.rpow δ (-η) * 9 * (2 : ℝ)^τ * 9 * 2) * 100) with hX_Y_def
    have h8 : X_Y < δ' ^ (-η_A7) := by
      by_contra h9
      have h9' : δ' ^ (-η_A7) ≤ X_Y := by linarith
      have h10 : a * δ' ^ (-η_A7) ≤ a * X_Y := mul_le_mul_of_nonneg_left h9' (by positivity)
      linarith
    exact h8.le
  have h_const_absorb_X : (Real.rpow δ (-η) * 9 * (4 : ℝ)^s * 9) * 100 ≤ δ' ^ (-η_A7) := by
    have h3 := h_rpow_transfer η_A7 hη_A7_pos
    have h4 : K_X * δ ^ (-η) < (2 : ℝ)^η_A7 * δ' ^ (-η_A7) := h_absorb_X'.trans_lt h3
    have h5 : K_X * δ ^ (-η) = (2 : ℝ)^η_A7 * ((Real.rpow δ (-η) * 9 * (4 : ℝ)^s * 9) * 100) := by
      dsimp only [K_X]
      have h6 : δ ^ (-η) = Real.rpow δ (-η) := by rfl
      rw [h6] <;> ring
    rw [h5] at h4
    have h7 : 0 < (2 : ℝ)^η_A7 := by positivity
    set a := (2 : ℝ)^η_A7 with ha_def
    set X_X := ((Real.rpow δ (-η) * 9 * (4 : ℝ)^s * 9) * 100) with hX_X_def
    have h8 : X_X < δ' ^ (-η_A7) := by
      by_contra h9
      have h9' : δ' ^ (-η_A7) ≤ X_X := by linarith
      have h10 : a * δ' ^ (-η_A7) ≤ a * X_X := mul_le_mul_of_nonneg_left h9' (by positivity)
      linarith
    exact h8.le
  have h_const_absorb_T : (Real.rpow δ (-η) * 81 * 4096 * 405) * 1000 ≤ δ' ^ (-η_A7) := by
    have h3 := h_rpow_transfer η_A7 hη_A7_pos
    have h4 : K_T * δ ^ (-η) < (2 : ℝ)^η_A7 * δ' ^ (-η_A7) := h_absorb_T'.trans_lt h3
    have h5 : K_T * δ ^ (-η) = ((Real.rpow δ (-η) * 81 * 4096 * 405) * 1000) * (2 : ℝ)^η_A7 := by
      have hK : K_T = ((81 : ℝ) * 4096 * 405 * 1000) * (2 : ℝ)^η_A7 := by
        dsimp only [K_T] <;> ring
      rw [hK]
      have h6 : δ ^ (-η) = Real.rpow δ (-η) := by rfl
      rw [h6] <;> ring
    rw [h5] at h4
    have h7 : 0 < (2 : ℝ)^η_A7 := by positivity
    set a := (2 : ℝ)^η_A7 with ha_def
    set X_T := ((Real.rpow δ (-η) * 81 * 4096 * 405) * 1000) with hX_T_def
    have h8 : X_T < δ' ^ (-η_A7) := by
      by_contra h9
      have h9' : δ' ^ (-η_A7) ≤ X_T := by linarith
      have h10 : a * δ' ^ (-η_A7) ≤ a * X_T := mul_le_mul_of_nonneg_left h9' (by positivity)
      linarith
    exact h8.le
  have hY_grid_sc_final : IsProductLikeRealDeltaSCSet δ' τ' (δ' ^ (-η_A7)) Y_grid :=
    IsProductLikeRealDeltaSCSet.weaken_constant hY_grid_sc h_const_absorb_Y
  have hXg'_sc_final : ∀ y ∈ Y_grid, IsProductLikeRealDeltaSCSet δ' s (δ' ^ (-η_A7)) (Xg' y) := by
    intro y hy
    have h_C_eq : C_X * 100 = (Real.rpow δ (-η) * 9 * (4 : ℝ)^s * 9) * 100 := by
      dsimp only [C_X] <;> ring
    have h_tmp : IsProductLikeRealDeltaSCSet δ' s ((Real.rpow δ (-η) * 9 * (4 : ℝ)^s * 9) * 100) (Xg' y) := by
      rw [←h_C_eq]
      exact hXg'_sc y hy
    exact IsProductLikeRealDeltaSCSet.weaken_constant h_tmp h_const_absorb_X
  have h𝒯_sc_final : ∀ z ∈ Z_occ,
      IsProductLikeAppendixDeltaSCSetOfDyadicTubes δ' s (δ' ^ (-η_A7)) (𝒯z z) := by
    intro z hz
    have h6 : 𝒯z z = 𝒯z_partial z hz := by
      simp [𝒯z, hz]
      <;> split_ifs <;> tauto
    rw [h6]
    exact IsProductLikeAppendixDeltaSCSetOfDyadicTubes.weaken_constant (h𝒯_sc z hz) h_const_absorb_T
  have hA7' : ENNReal.ofReal (δ' ^ (-(2 * s + η_A7))) ≤ ENat.toENNReal 𝒯.encard :=
    hA7 hδ'_dyadic hδ'_pos hδ'_le_δ₀_A7 Y_grid Xg' 𝒯z
      hY_grid_sub hY_grid_sc_final
      (fun y hy => ⟨hXg'_sub y hy, hXg'_sc_final y hy⟩)
      (fun z hz => ⟨h𝒯_sc_final z hz, by
        have h7 : 𝒯z z = 𝒯z_partial z hz := by
          simp [𝒯z, hz] <;> split_ifs <;> tauto
        rw [h7]
        exact h𝒯_inc z hz⟩)
  -- Step 7: Transfer conclusion back (uses tubeUnion_covering_lower)
  -- 7a. Apply tubeUnion_covering_lower to parameter sets of all tubes in 𝒯
  let param_union : Set (EuclideanSpace ℝ (Fin 2)) :=
    ⋃ z ∈ Z_occ, productLikeAppendixDyadicTubeParameterSet δ' (𝒯z z)
  have h7a : (Metric.externalCoveringNumber δ'.toNNReal param_union : ENNReal) ≥
      ENat.toENNReal 𝒯.encard / 9 :=
    tubeUnion_covering_lower hδ'_pos (fun z hz => by
      have h_eq : 𝒯z z = 𝒯z_partial z hz := by
        simp [𝒯z, hz] <;> split_ifs <;> tauto
      rw [h_eq]
      exact h𝒯_sub z hz)
  -- 7b. Combine with A.7 lower bound: encard(𝒯) ≥ δ'^{-(2s+η_A7)}
  have h7b : (Metric.externalCoveringNumber δ'.toNNReal param_union : ENNReal) ≥
      ENNReal.ofReal (δ' ^ (-(2 * s + η_A7))) / 9 := by
    calc (Metric.externalCoveringNumber δ'.toNNReal param_union : ENNReal)
      ≥ ENat.toENNReal 𝒯.encard / 9 := h7a
      _ ≥ ENNReal.ofReal (δ' ^ (-(2 * s + η_A7))) / 9 := by
        gcongr
  -- 7c. Relate param_union to T'_union.
  -- The parameter cubes arise from covering T'(z'), so their union is related
  -- to ⋃ T'. We need a lower bound on covering(T'_union) in terms of covering(param_union).
  let C_param_to_T : ℝ := 1000
  let T'_union : Set (ℝ × ℝ) := ⋃ (z' : ℝ × ℝ) (hz' : z' ∈ Z'), T' z' hz'
  -- h_thicken: every point in param_union is within sqrt(2)*9δ'/2 of e_plane_inv '' T'_union.
  -- This follows from the thickening conclusion of parameterSet_to_tubeFamily,
  -- combined with the perturbation argument in hTubes (h𝒯_thicken).
  have h_thicken : param_union ⊆
      Metric.cthickening (Real.sqrt 2 * (9 * δ' / 2)) (e_plane_inv '' T'_union) := by
    apply Set.iUnion₂_subset
    intro z hz
    have h_eq : 𝒯z z = 𝒯z_partial z hz := by
      simp [𝒯z, hz] <;> split_ifs <;> tauto
    rw [h_eq]
    exact h𝒯_thicken z hz
  have h7c : (Metric.externalCoveringNumber δ'.toNNReal T'_union : ENNReal) ≥
      (Metric.externalCoveringNumber δ'.toNNReal param_union : ENNReal) / ENNReal.ofReal C_param_to_T :=
    h7c_covering_bound δ' hδ'_pos param_union T'_union h_thicken
  -- 7d. Transfer from T'_union to original T_union via transformTube.
  -- T'_union = transformTube '' T_union. Since transformTube is 1-Lipschitz:
  --   covering_δ(T'_union) ≤ covering_δ(T_union)
  -- And since δ ≤ δ':
  --   covering_δ'(T'_union) ≤ covering_δ(T'_union)
  -- Hence covering_δ(T_union) ≥ covering_δ'(T'_union).
  let T_union : Set (ℝ × ℝ) := ⋃ (z : ℝ × ℝ) (hz : z ∈ Z), T z hz
  have h_eq_T' : T'_union = transformTube '' T_union := by
    ext p'
    simp only [T'_union, T_union, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨z', hz', hp'⟩
      rcases hp' with ⟨p, hp, rfl⟩
      let z : ℝ × ℝ := (4 * z'.1 - 1, 2 * z'.2 - 1)
      have hz : z ∈ Z := hZ'_to_Z z' hz'
      exact ⟨p, ⟨z, hz, hp⟩, rfl⟩
    · rintro ⟨p, hp_in_union, rfl⟩
      rcases hp_in_union with ⟨z, hz, hp⟩
      rcases Set.mem_iUnion₂.mp hz with ⟨y, hy, hz_in⟩
      have hz1 : z.1 ∈ X y hy := hz_in.1
      have hz2 : z.2 = y := by simpa using hz_in.2
      have h_z2_in_Y : z.2 ∈ Y := by
        cases hz2
        exact hy
      let z' : ℝ × ℝ := (transformX z.1, transformY z.2)
      have h_y' : transformY z.2 ∈ Y' := by
        refine' ⟨z.2, h_z2_in_Y, rfl⟩
      have h_x' : transformX z.1 ∈ X' (transformY z.2) := by
        have h2 : 2 * transformY z.2 - 1 = z.2 := by
          simp [transformY] <;> linarith
        have hX'_eq : X' (transformY z.2) = transformX '' (X z.2 h_z2_in_Y) := by
          unfold X'
          have h_dite : (if h : transformY z.2 ∈ Y' then transformX '' (X (2 * transformY z.2 - 1) (hY'_inv (transformY z.2) h)) else ∅) =
              transformX '' (X z.2 h_z2_in_Y) := by
            simp only [dif_pos h_y']
            <;> congr <;> simp [h2] <;> linarith
          exact h_dite
        rw [hX'_eq]
        have hz1' : z.1 ∈ X z.2 h_z2_in_Y := by
          cases hz2
          exact hz1
        exact ⟨z.1, hz1', rfl⟩
      have hz' : z' ∈ Z' := by
        exact Set.mem_iUnion₂.mpr ⟨transformY z.2, h_y', ⟨h_x', by simp [z']⟩⟩
      have h_z_eq : (4 * z'.1 - 1, 2 * z'.2 - 1) = z := by
        have h : (4 * z'.1 - 1, 2 * z'.2 - 1) = (z.1, z.2) := by
          exact transform_roundtrip z.1 z.2
        simpa using h
      have h_goal : transformTube p ∈ T' z' hz' := by
        dsimp only [T']
        let w := (4 * z'.1 - 1, 2 * z'.2 - 1)
        have hw : w ∈ Z := hZ'_to_Z z' hz'
        have hwe : w = z := h_z_eq
        have h_set_eq : T w hw = T z hz := by
          congr
          <;> exact hwe
        have h3 : p ∈ T w hw := by
          rw [h_set_eq]
          exact hp
        exact ⟨p, h3, rfl⟩
      exact ⟨z', hz', h_goal⟩
  have h7d1 : (Metric.externalCoveringNumber δ.toNNReal T'_union : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal T_union : ENNReal) := by
    rw [h_eq_T']
    have h' := externalCoveringNumber_image_lipschitz (hf := transformTube_lipschitz1) (ε := δ.toNNReal) (A := T_union)
    have h_eq : (1 : NNReal) * δ.toNNReal = δ.toNNReal := by simp
    rw [h_eq] at h'
    exact_mod_cast h'
  have hδ'_nn_le : δ.toNNReal ≤ δ'.toNNReal := by
    apply Real.toNNReal_le_toNNReal
    exact hδ_le_δ'
  have h7d2 : (Metric.externalCoveringNumber δ'.toNNReal T'_union : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal T'_union : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_anti hδ'_nn_le
  have h7d : (Metric.externalCoveringNumber δ.toNNReal T_union : ENNReal) ≥
      (Metric.externalCoveringNumber δ'.toNNReal T'_union : ENNReal) := by
    exact le_trans h7d2 h7d1
  -- 7e. Chain everything and absorb constants.
  -- Need: δ'^{-(2s+η_A7)} / (9 * C_param_to_T) ≥ δ^{-(2s+η)}
  -- Since δ' < 2δ and η = η_A7/4, this holds for sufficiently small δ.
  -- UPSTREAM: constant absorption lemma.
  have h7e_real : Real.rpow δ (-(2 * s + η)) ≤
      (δ' ^ (-(2 * s + η_A7))) / (9 * C_param_to_T) := by
    have h_sum2 : (2 * s + η) + slack = 2 * s + η_A7 := by
      have h : η + slack = η_A7 := h_sum1
      linarith
    have h_absorb_final' : K_final * δ ^ (-(2 * s + η)) ≤ δ ^ (-(2 * s + η_A7)) := by
      have h2 := h_abs_final δ hδ_pos hδ_lt_δ₀_final
      rw [h_sum2] at h2; exact h2
    have h3 := h_rpow_transfer (2 * s + η_A7) (by positivity)
    have h4 : K_final * δ ^ (-(2 * s + η)) < (2 : ℝ)^(2 * s + η_A7) * δ' ^ (-(2 * s + η_A7)) :=
      h_absorb_final'.trans_lt h3
    have h5 : K_final * δ ^ (-(2 * s + η)) =
        ((9 : ℝ) * (C_param_to_T : ℝ)) * (2 : ℝ)^(2 * s + η_A7) * δ ^ (-(2 * s + η)) := by
      dsimp only [K_final, C_param_to_T] <;> ring
    rw [h5] at h4
    have h6 : 0 < (2 : ℝ)^(2 * s + η_A7) := by positivity
    have h_comm : ((9 : ℝ) * (C_param_to_T : ℝ)) * (2 : ℝ)^(2 * s + η_A7) * δ ^ (-(2 * s + η)) =
        (2 : ℝ)^(2 * s + η_A7) * (((9 : ℝ) * (C_param_to_T : ℝ)) * δ ^ (-(2 * s + η))) := by ring
    rw [h_comm] at h4
    let A : ℝ := ((9 : ℝ) * (C_param_to_T : ℝ)) * δ ^ (-(2 * s + η))
    let B : ℝ := δ' ^ (-(2 * s + η_A7))
    have h7 : A < B := by
      have h_pos : 0 < (2 : ℝ)^(2 * s + η_A7) := h6
      have h_eq1 : (2 : ℝ)^(2 * s + η_A7) * (B - A) = (2 : ℝ)^(2 * s + η_A7) * B - (2 : ℝ)^(2 * s + η_A7) * A := by ring
      have h13 : 0 < (2 : ℝ)^(2 * s + η_A7) * (B - A) := by
        rw [h_eq1]; linarith [h4]
      have h14 : 0 < B - A := (mul_pos_iff_of_pos_left h_pos).mp h13
      linarith
    have h8 : 0 < (9 : ℝ) * (C_param_to_T : ℝ) := by positivity
    have h9 : Real.rpow δ (-(2 * s + η)) ≤ δ' ^ (-(2 * s + η_A7)) / ((9 : ℝ) * (C_param_to_T : ℝ)) := by
      have h10 : Real.rpow δ (-(2 * s + η)) =
          (((9 : ℝ) * (C_param_to_T : ℝ)) * Real.rpow δ (-(2 * s + η))) / ((9 : ℝ) * (C_param_to_T : ℝ)) := by
        field_simp [h8.ne'] <;> ring
      rw [h10]
      exact div_le_div_of_nonneg_right h7.le (by positivity)
    exact h9
  have h7e : ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) ≤
      ENNReal.ofReal ((δ' ^ (-(2 * s + η_A7))) / (9 * C_param_to_T)) := by
    exact ENNReal.ofReal_le_ofReal h7e_real
  have h7e' : ENNReal.ofReal ((δ' ^ (-(2 * s + η_A7))) / (9 * C_param_to_T)) =
      (ENNReal.ofReal (δ' ^ (-(2 * s + η_A7))) / 9) / ENNReal.ofReal C_param_to_T := by
    have h_pos9 : (0 : ℝ) < 9 := by norm_num
    have h_posC : 0 < C_param_to_T := by positivity
    have h_eq1 : (δ' ^ (-(2 * s + η_A7))) / (9 * C_param_to_T) =
        ((δ' ^ (-(2 * s + η_A7))) / 9) / C_param_to_T := by
      rw [div_mul_eq_div_div]
      <;> ring
    rw [h_eq1]
    have h_eq2 : ENNReal.ofReal (((δ' ^ (-(2 * s + η_A7))) / 9) / C_param_to_T) =
        ENNReal.ofReal ((δ' ^ (-(2 * s + η_A7))) / 9) / ENNReal.ofReal C_param_to_T := by
      rw [ENNReal.ofReal_div_of_pos h_posC]
      <;> rfl
    rw [h_eq2]
    have h_eq3 : ENNReal.ofReal ((δ' ^ (-(2 * s + η_A7))) / 9) =
        ENNReal.ofReal (δ' ^ (-(2 * s + η_A7))) / 9 := by
      rw [ENNReal.ofReal_div_of_pos h_pos9]
      <;> norm_cast
    rw [h_eq3]
  calc ENNReal.ofReal (Real.rpow δ (-(2 * s + η)))
    ≤ ENNReal.ofReal ((δ' ^ (-(2 * s + η_A7))) / (9 * C_param_to_T)) := h7e
    _ = (ENNReal.ofReal (δ' ^ (-(2 * s + η_A7))) / 9) / ENNReal.ofReal C_param_to_T := h7e'
    _ ≤ (Metric.externalCoveringNumber δ'.toNNReal param_union : ENNReal) / ENNReal.ofReal C_param_to_T := by
      have h : (Metric.externalCoveringNumber δ'.toNNReal param_union : ENNReal) / ENNReal.ofReal C_param_to_T ≥
          (ENNReal.ofReal (δ' ^ (-(2 * s + η_A7))) / 9) / ENNReal.ofReal C_param_to_T := by
        gcongr
        <;> exact h7b
      exact h
    _ ≤ (Metric.externalCoveringNumber δ'.toNNReal T'_union : ENNReal) := h7c
    _ ≤ (Metric.externalCoveringNumber δ.toNNReal T_union : ENNReal) := h7d

end DirecretisedFurstenbergEstimate
