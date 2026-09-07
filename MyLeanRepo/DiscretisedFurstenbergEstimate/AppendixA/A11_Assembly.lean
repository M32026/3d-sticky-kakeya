module

/-
  A11: Product contradiction assembly (OS Appendix A, final step) — FIXED VERSION

  Takes canonical A10_Output and derives False using productProp_bounded.

  Rescaling to fit productProp bounds:
    y' = y/3, x' = x/50, a' = 3a/50, b' = b/50
  Incidence: |a'*y' + b' - x'| = |a*y + b - x|/50 ≤ 4Δ/50 ≤ 4Δ

  S-set properties are TRANSFERRED from A10 through the rescaling maps
  using scale1/scale2 + scale_up1/scale_up2 + anisotropic expansion,
  then constants are absorbed to Δ^{-η_axiom}.

  This replaces the previous vacuous bounded-set trick which required
  η_sset ≥ max(s,τ), conflicting with the product axiom's η_axiom > 0 only.

  Whiteprint node: appendix_a_alternative / a11_assembly
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductContradiction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBounded
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.A11

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.ProductContradiction
open DiscretisedFurstenbergEstimate.CoveringUtils

/-! ### Anisotropic scaling lemma for S-sets -/

/-- Expand x-coordinate by factor 3: (δ,s,C)-set → (δ,s,16C)-set. -/
lemma IsDeltaSSet.expand_x3 {δ s C : ℝ} {A : Set (ℝ × ℝ)}
    (hδ_pos : 0 < δ) (hs_nonneg : 0 ≤ s) (hC_pos : 0 < C)
    (hP : IsDeltaSSet δ s C A) :
    IsDeltaSSet δ s (16 * C) ((fun p : ℝ × ℝ => (3 * p.1, p.2)) '' A) := by
  let f : ℝ × ℝ → ℝ × ℝ := fun p => (3 * p.1, p.2)
  let g : ℝ × ℝ → ℝ × ℝ := fun p => (p.1 / 3, p.2)
  let B : Set (ℝ × ℝ) := f '' A

  have hf_lip : LipschitzWith (3 : NNReal) f := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    have h1 : |3 * p.1 - 3 * q.1| ≤ 3 * |p.1 - q.1| := by
      have h2 : 3 * p.1 - 3 * q.1 = 3 * (p.1 - q.1) := by ring
      rw [h2, abs_mul] <;> norm_num
    have h3 : |p.2 - q.2| ≤ 3 * |p.2 - q.2| := by
      have h4 : 0 ≤ |p.2 - q.2| := abs_nonneg _
      nlinarith
    have hmax1 : |3 * p.1 - 3 * q.1| ≤ 3 * max (|p.1 - q.1|) (|p.2 - q.2|) := by
      calc |3 * p.1 - 3 * q.1|
        ≤ 3 * |p.1 - q.1| := h1
      _ ≤ 3 * max (|p.1 - q.1|) (|p.2 - q.2|) := by
        have h5 : |p.1 - q.1| ≤ max (|p.1 - q.1|) (|p.2 - q.2|) := le_max_left _ _
        exact mul_le_mul_of_nonneg_left h5 (by norm_num)
    have hmax2 : |p.2 - q.2| ≤ 3 * max (|p.1 - q.1|) (|p.2 - q.2|) := by
      calc |p.2 - q.2|
        ≤ 3 * |p.2 - q.2| := h3
      _ ≤ 3 * max (|p.1 - q.1|) (|p.2 - q.2|) := by
        have h5 : |p.2 - q.2| ≤ max (|p.1 - q.1|) (|p.2 - q.2|) := le_max_right _ _
        exact mul_le_mul_of_nonneg_left h5 (by norm_num)
    have h5 : max (|3 * p.1 - 3 * q.1|) (|p.2 - q.2|) ≤
        3 * max (|p.1 - q.1|) (|p.2 - q.2|) := max_le hmax1 hmax2
    have h6 : dist (f p) (f q) = max (|3 * p.1 - 3 * q.1|) (|p.2 - q.2|) := by
      simp [f, Prod.dist_eq, Real.dist_eq] <;> rfl
    have h7 : dist p q = max (|p.1 - q.1|) (|p.2 - q.2|) := by
      simp [Prod.dist_eq, Real.dist_eq] <;> rfl
    rw [h6, h7]
    exact h5

  have hg_lip : LipschitzWith (1 : NNReal) g := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    have h1 : |p.1 / 3 - q.1 / 3| ≤ |p.1 - q.1| := by
      have h2 : p.1 / 3 - q.1 / 3 = (1 / 3 : ℝ) * (p.1 - q.1) := by ring
      rw [h2, abs_mul]
      have h3 : |(1 / 3 : ℝ)| = (1 / 3 : ℝ) := by norm_num
      rw [h3]
      have h4 : 0 ≤ |p.1 - q.1| := abs_nonneg _
      nlinarith
    have hmax1 : |p.1 / 3 - q.1 / 3| ≤ max (|p.1 - q.1|) (|p.2 - q.2|) := by
      calc |p.1 / 3 - q.1 / 3| ≤ |p.1 - q.1| := h1
           _ ≤ max (|p.1 - q.1|) (|p.2 - q.2|) := le_max_left _ _
    have hmax2 : |p.2 - q.2| ≤ max (|p.1 - q.1|) (|p.2 - q.2|) := le_max_right _ _
    have h5 : max (|p.1 / 3 - q.1 / 3|) (|p.2 - q.2|) ≤
        max (|p.1 - q.1|) (|p.2 - q.2|) := max_le hmax1 hmax2
    have h6 : dist (g p) (g q) = max (|p.1 / 3 - q.1 / 3|) (|p.2 - q.2|) := by
      simp [g, Prod.dist_eq, Real.dist_eq] <;> rfl
    have h7 : dist p q = max (|p.1 - q.1|) (|p.2 - q.2|) := by
      simp [Prod.dist_eq, Real.dist_eq] <;> rfl
    rw [h6, h7]
    simpa using h5

  have hgf : ∀ p, g (f p) = p := by
    intro p; ext <;> simp [f, g] <;> ring

  have hgB : g '' B = A := by
    ext z; simp only [B, Set.mem_image]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      rw [hgf x]; exact hx
    · intro hz
      refine ⟨f z, ⟨z, hz, rfl⟩, ?_⟩
      exact hgf z

  have h_cov_AB : Metric.externalCoveringNumber δ.toNNReal A ≤
      Metric.externalCoveringNumber δ.toNNReal B := by
    have h : Metric.externalCoveringNumber ((1 : NNReal) * δ.toNNReal) (g '' B) ≤
        Metric.externalCoveringNumber δ.toNNReal B :=
      externalCoveringNumber_image_lipschitz (hf := hg_lip) (ε := δ.toNNReal) (A := B)
    have h1 : (1 : NNReal) * δ.toNNReal = δ.toNNReal := by simp
    rw [h1] at h
    rw [hgB] at h
    exact h

  have h_main : ∀ (y : ℝ × ℝ) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall y r) : ENNReal) ≤
        ENNReal.ofReal (16 * C) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) := by
    intro y r hr
    let x : ℝ × ℝ := (y.1 / 3, y.2)
    have hfx : f x = y := by ext <;> simp [f, x] <;> ring

    have h1 : B ∩ Metric.closedBall y r ⊆ f '' (A ∩ Metric.closedBall x r) := by
      intro z hz
      have hzB : z ∈ B := hz.1
      have hzball : dist z y ≤ r := hz.2
      rcases hzB with ⟨p, hpA, rfl⟩
      have h2 : dist p x ≤ r := by
        have h3 : dist (f p) (f x) ≤ r := by simpa [hfx] using hzball
        have h4 : dist p x ≤ dist (f p) (f x) := by
          have h5 := hg_lip.dist_le_mul (f p) (f x)
          simpa [hgf] using h5
        exact le_trans h4 h3
      exact ⟨p, ⟨hpA, h2⟩, rfl⟩

    have h_cov1 : Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall y r) ≤
        Metric.externalCoveringNumber δ.toNNReal (f '' (A ∩ Metric.closedBall x r)) :=
      Metric.externalCoveringNumber_mono_set h1

    set δ3 : ℝ := δ / 3 with hδ3_def
    have hδ3_pos : 0 < δ3 := by rw [hδ3_def]; exact div_pos hδ_pos (by norm_num)
    have h3δ_eq : (3 : NNReal) * δ3.toNNReal = δ.toNNReal := by
      have h_pos : 0 ≤ δ3 := by positivity
      have h : (3 : NNReal) * δ3.toNNReal = (3 * δ3).toNNReal := by
        ext <;> simp [h_pos] <;> norm_num <;> ring
      rw [h]
      have h2 : 3 * δ3 = δ := by simp [hδ3_def] <;> ring
      rw [h2] <;> rfl
    have h_cov2 : Metric.externalCoveringNumber δ.toNNReal (f '' (A ∩ Metric.closedBall x r)) ≤
        Metric.externalCoveringNumber δ3.toNNReal (A ∩ Metric.closedBall x r) := by
      have h := externalCoveringNumber_image_lipschitz (hf := hf_lip) (ε := δ3.toNNReal)
        (A := A ∩ Metric.closedBall x r)
      rw [h3δ_eq] at h
      exact h

    have h_scale : δ ≤ 4 * δ3 := by rw [hδ3_def] <;> linarith
    have h_cov3 : Metric.externalCoveringNumber δ3.toNNReal (A ∩ Metric.closedBall x r) ≤
        16 * Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) :=
      covering_scale_2d hδ3_pos hδ_pos h_scale

    have h_sset := hP.2.2.2.2 x r hr

    calc (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall y r) : ENNReal)
        ≤ Metric.externalCoveringNumber δ.toNNReal (f '' (A ∩ Metric.closedBall x r)) := by
          exact_mod_cast h_cov1
      _ ≤ Metric.externalCoveringNumber δ3.toNNReal (A ∩ Metric.closedBall x r) := by
          exact_mod_cast h_cov2
      _ ≤ 16 * Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) := by
          exact_mod_cast h_cov3
      _ ≤ 16 * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
              Metric.externalCoveringNumber δ.toNNReal A) := by
          gcongr <;> exact h_sset
      _ = ENNReal.ofReal (16 * C) * (ENNReal.ofReal r) ^ s *
              Metric.externalCoveringNumber δ.toNNReal A := by
          have h_mul : ENNReal.ofReal (16 * C) = 16 * ENNReal.ofReal C := by
            rw [ENNReal.ofReal_mul (by linarith)] <;> norm_cast
          rw [h_mul] <;> ring
      _ ≤ ENNReal.ofReal (16 * C) * (ENNReal.ofReal r) ^ s *
              Metric.externalCoveringNumber δ.toNNReal B := by
          gcongr <;> exact_mod_cast h_cov_AB

  exact ⟨hP.1.image f, hδ_pos, by positivity, hs_nonneg, h_main⟩

/-! ### Iterated scale-up helpers -/

/-- Scale up from δ/50 to δ in 1D, multiplying constant by 9^3. -/
lemma IsDeltaSSet.scale_up1_50 {δ s C : ℝ} {A : Set ℝ}
    (hδ : 0 < δ) (hP : IsDeltaSSet (δ / 50) s C A) :
    IsDeltaSSet δ s (C * 9 ^ 3) A := by
  have h_pos1 : 0 < δ / 50 := by positivity
  have h_pos2 : 0 < (2 * δ / 25) := by positivity
  have h_pos3 : 0 < (8 * δ / 25) := by positivity
  have h_le1 : δ / 50 ≤ 2 * δ / 25 := by linarith
  have h_le2 : 2 * δ / 25 ≤ 8 * δ / 25 := by linarith
  have h_le3 : 8 * δ / 25 ≤ δ := by linarith
  have h_41 : 2 * δ / 25 ≤ 4 * (δ / 50) := by linarith
  have h_42 : 8 * δ / 25 ≤ 4 * (2 * δ / 25) := by linarith
  have h_43 : δ ≤ 4 * (8 * δ / 25) := by linarith
  have h1 : IsDeltaSSet (2 * δ / 25) s (C * 9) A :=
    hP.scale_up1 h_pos1 h_pos2 h_le1 h_41
  have h2 : IsDeltaSSet (8 * δ / 25) s ((C * 9) * 9) A :=
    h1.scale_up1 h_pos2 h_pos3 h_le2 h_42
  have h3 : IsDeltaSSet δ s (((C * 9) * 9) * 9) A :=
    h2.scale_up1 h_pos3 hδ h_le3 h_43
  have h_final : IsDeltaSSet δ s (C * 9 ^ 3) A := by
    have h_eq : ((C * 9) * 9) * 9 = C * 9 ^ 3 := by ring
    rw [h_eq] at h3
    exact h3
  exact h_final

/-- Scale up from δ/50 to δ in 2D, multiplying constant by 81^3. -/
lemma IsDeltaSSet.scale_up2_50 {δ s C : ℝ} {A : Set (ℝ × ℝ)}
    (hδ : 0 < δ) (hP : IsDeltaSSet (δ / 50) s C A) :
    IsDeltaSSet δ s (C * 81 ^ 3) A := by
  have h_pos1 : 0 < δ / 50 := by positivity
  have h_pos2 : 0 < (2 * δ / 25) := by positivity
  have h_pos3 : 0 < (8 * δ / 25) := by positivity
  have h_le1 : δ / 50 ≤ 2 * δ / 25 := by linarith
  have h_le2 : 2 * δ / 25 ≤ 8 * δ / 25 := by linarith
  have h_le3 : 8 * δ / 25 ≤ δ := by linarith
  have h_41 : 2 * δ / 25 ≤ 4 * (δ / 50) := by linarith
  have h_42 : 8 * δ / 25 ≤ 4 * (2 * δ / 25) := by linarith
  have h_43 : δ ≤ 4 * (8 * δ / 25) := by linarith
  have h1 : IsDeltaSSet (2 * δ / 25) s (C * 81) A :=
    hP.scale_up2 h_pos1 h_pos2 h_le1 h_41
  have h2 : IsDeltaSSet (8 * δ / 25) s ((C * 81) * 81) A :=
    h1.scale_up2 h_pos2 h_pos3 h_le2 h_42
  have h3 : IsDeltaSSet δ s (((C * 81) * 81) * 81) A :=
    h2.scale_up2 h_pos3 hδ h_le3 h_43
  have h_final : IsDeltaSSet δ s (C * 81 ^ 3) A := by
    have h_eq : ((C * 81) * 81) * 81 = C * 81 ^ 3 := by ring
    rw [h_eq] at h3
    exact h3
  exact h_final

/-! ### Decoupled contradiction lemma -/

/-- Decoupled contradiction: S-set exponent η_sset separate from upper-bound η_upper. -/
lemma product_configuration_contradiction_decoupled
    {Δ s τ η_sset η_upper η_axiom : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hτ_pos : 0 < τ)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hη_sset_pos : 0 < η_sset) (hη_upper_pos : 0 < η_upper)
    (hη_axiom_pos : 0 < η_axiom)
    (hη_sset_le : η_sset ≤ η_axiom)
    (hη_upper_lt : η_upper < η_axiom)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (hΔ_le_δ₀ : Δ ≤ δ₀)
    (hA7 : ProductPropBoundedTheorem s τ η_axiom δ₀)
    {Y : Set ℝ}
    {X : ∀ (y : ℝ), y ∈ Y → Set ℝ}
    {T_coarse : ∀ (z : ℝ × ℝ),
       z ∈ (⋃ (y : ℝ) (hy : y ∈ Y), X y hy ×ˢ {y}) → Set (ℝ × ℝ)}
    (hY_bounds : Y ⊆ Set.Icc (-1 : ℝ) 1)
    (hX_bounds : ∀ y hy, X y hy ⊆ Set.Icc (-1 : ℝ) 1)
    (hT_bounds : ∀ z hz, T_coarse z hz ⊆ Set.Icc (-2 : ℝ) 2 ×ˢ Set.Icc (-2 : ℝ) 2)
    (hY_sset : IsDeltaSSet Δ τ (Real.rpow Δ (-η_sset)) Y)
    (hX_sset : ∀ y hy, IsDeltaSSet Δ s (Real.rpow Δ (-η_sset)) (X y hy))
    (hT_sset : ∀ z hz, IsDeltaSSet Δ s (Real.rpow Δ (-η_sset)) (T_coarse z hz))
    (h_inc : ∀ z hz, ∀ (p : ℝ × ℝ), p ∈ T_coarse z hz →
       |p.1 * z.2 + p.2 - z.1| ≤ 4 * Δ)
    (h_upper : (Metric.externalCoveringNumber Δ.toNNReal
          (⋃ (z : ℝ × ℝ)
             (hz : z ∈ (⋃ (y : ℝ) (hy : y ∈ Y), X y hy ×ˢ {y})),
             T_coarse z hz) : ENNReal) <
        ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper)))) :
    False := by
  have h_const_weaken : Real.rpow Δ (-η_sset) ≤ Real.rpow Δ (-η_axiom) := by
    have h1 : -η_axiom ≤ -η_sset := by linarith
    have h2 : Real.rpow Δ (-η_sset) ≤ Real.rpow Δ (-η_axiom) :=
      Real.rpow_le_rpow_of_exponent_ge hΔ_pos (by linarith) h1
    exact h2
  have hY' : IsDeltaSSet Δ τ (Real.rpow Δ (-η_axiom)) Y :=
    IsDeltaSSet.mono_const hY_sset h_const_weaken
  have hX' : ∀ y hy, IsDeltaSSet Δ s (Real.rpow Δ (-η_axiom)) (X y hy) :=
    fun y hy => IsDeltaSSet.mono_const (hX_sset y hy) h_const_weaken
  have hT' : ∀ z hz, IsDeltaSSet Δ s (Real.rpow Δ (-η_axiom)) (T_coarse z hz) :=
    fun z hz => IsDeltaSSet.mono_const (hT_sset z hz) h_const_weaken
  have h_lower : ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_axiom))) ≤
      (Metric.externalCoveringNumber Δ.toNNReal
        (⋃ (z : ℝ × ℝ)
           (hz : z ∈ (⋃ (y : ℝ) (hy : y ∈ Y), X y hy ×ˢ {y})),
           T_coarse z hz) : ENNReal) :=
    hA7 Δ ⟨hΔ_pos, hΔ_le_δ₀⟩ Y X T_coarse hY_bounds hX_bounds hT_bounds hY' hX' hT' h_inc
  have h_exp_le : -(2 * s + η_upper) ≥ -(2 * s + η_axiom) := by linarith
  have h_rpow_le : Real.rpow Δ (-(2 * s + η_upper)) ≤ Real.rpow Δ (-(2 * s + η_axiom)) :=
    Real.rpow_le_rpow_of_exponent_ge hΔ_pos (by linarith) h_exp_le
  have h_upper_le : (Metric.externalCoveringNumber Δ.toNNReal
        (⋃ (z : ℝ × ℝ)
           (hz : z ∈ (⋃ (y : ℝ) (hy : y ∈ Y), X y hy ×ˢ {y})),
           T_coarse z hz) : ENNReal) <
      ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_axiom))) := by
    calc (Metric.externalCoveringNumber Δ.toNNReal _ : ENNReal)
      < ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper))) := h_upper
    _ ≤ ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_axiom))) := by
      exact ENNReal.ofReal_le_ofReal h_rpow_le
  exact lt_irrefl _ (h_lower.trans_lt h_upper_le)

/-! ### Main theorem -/

/-- From A10_Output, derive False using the product-like incidence axiom.

    Uses GENUINE S-set transfer through rescaling maps (no bounded-set trick).
    Requires absorption hypotheses ensuring constants fit in Δ^{-η_axiom}. -/
theorem A11_product_contradiction
    {Δ s t ε : ℝ}
    (a10 : A10_Output Δ s t ε)
    -- Upper bound on T_union covering number (supplied separately, not a field of A10_Output)
    (h_upper : (Metric.externalCoveringNumber Δ.toNNReal
        (⋃ (z : ℝ × ℝ) (hz : z ∈ a10.Z), a10.T_coarse z hz) : ENNReal) <
      ENNReal.ofReal (Real.rpow Δ (-(2 * s + a10.η_upper))))
    (hs : 0 < s) (hs1 : s < 1)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hε_pos : 0 < ε)
    (η_axiom δ₀ : ℝ)
    (hη_axiom_pos : 0 < η_axiom)
    (hη_upper_lt : a10.η_upper < η_axiom)
    (hδ₀_pos : 0 < δ₀)
    (hΔ_le_δ₀ : Δ ≤ δ₀)
    (hA7 : ProductPropBoundedTheorem s a10.τ η_axiom δ₀)
    (h_absorb_Y : (9 * 3 ^ a10.τ) * Real.rpow Δ (-10000 * ε) ≤ Real.rpow Δ (-η_axiom))
    (h_absorb_X : (729 * 50 ^ s) * Real.rpow Δ (-600 * ε) ≤ Real.rpow Δ (-η_axiom))
    (h_absorb_T : (81 ^ 3 * 16 * 50 ^ s) * Real.rpow Δ (-600 * ε) ≤ Real.rpow Δ (-η_axiom)) :
    False := by
  let η_upper := a10.η_upper
  have hη_upper_pos : 0 < η_upper := a10.hη_upper_pos
  let τ := a10.τ
  have hτ_pos : 0 < τ := a10.hτ_pos

  -- Rescaled sets with K=50 incidence scaling
  let Y' : Set ℝ := (fun y : ℝ => y / 3) '' a10.Y
  let X' (y' : ℝ) (hy' : y' ∈ Y') : Set ℝ :=
    (fun x : ℝ => x / 50) '' (a10.X (3 * y') (by
      rcases hy' with ⟨y, hy, h_eq⟩
      have h2 : 3 * y' = y := by linarith
      rw [h2]; exact hy))
  let Z' : Set (ℝ × ℝ) := ⋃ (y' : ℝ) (hy' : y' ∈ Y'), X' y' hy' ×ˢ {y'}

  let origZ (z' : ℝ × ℝ) : ℝ × ℝ := (50 * z'.1, 3 * z'.2)

  have h_origZ_mem : ∀ (z' : ℝ × ℝ), z' ∈ Z' → origZ z' ∈ a10.Z := by
    intro z' hz'
    simp only [Z', Set.mem_iUnion] at hz'
    rcases hz' with ⟨y', hy', hz'⟩
    have hz2 : z'.1 ∈ X' y' hy' ∧ z'.2 = y' := by
      simpa [Set.mem_prod, Set.mem_singleton_iff] using hz'
    have hxv : z'.1 ∈ X' y' hy' := hz2.1
    have hzy : z'.2 = y' := hz2.2
    rcases hxv with ⟨x, hx, h_eq⟩
    have hy : 3 * y' ∈ a10.Y := by
      rcases hy' with ⟨y0, hy0, h_eq0⟩
      have h2 : 3 * y' = y0 := by linarith
      rw [h2]; exact hy0
    have hZ : (x, 3 * y') ∈ a10.Z := by
      rw [a10.hZ_def]
      exact Set.mem_iUnion₂.mpr ⟨3 * y', hy, Set.mem_prod.mpr ⟨hx, by simp⟩⟩
    have h_eq3 : origZ z' = (x, 3 * y') := by
      have h1 : (origZ z').1 = x := by
        simp [origZ, h_eq] <;> linarith
      have h2 : (origZ z').2 = 3 * y' := by
        simp [origZ, hzy] <;> linarith
      exact Prod.ext h1 h2
    rw [h_eq3]
    exact hZ

  let T'_coarse (z' : ℝ × ℝ) (hz' : z' ∈ Z') : Set (ℝ × ℝ) :=
    (fun p : ℝ × ℝ => (3 * p.1 / 50, p.2 / 50)) ''
      (a10.T_coarse (origZ z') (h_origZ_mem z' hz'))

  -- Helper: 3*y' ∈ a10.Y for any y' ∈ Y'
  have hy3 : ∀ (y' : ℝ), y' ∈ Y' → 3 * y' ∈ a10.Y := by
    intro y' hy'
    rcases hy' with ⟨y, hy, h_eq⟩
    have h2 : 3 * y' = y := by linarith
    rw [h2]; exact hy

  -- Bounds
  have hY'_bounds : Y' ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro y' hy'
    rcases hy' with ⟨y, hy, rfl⟩
    have h1 : -3 ≤ y := (a10.hY_bounds hy).1
    have h2 : y ≤ 3 := (a10.hY_bounds hy).2
    constructor <;> linarith

  have hX'_bounds : ∀ y' hy', X' y' hy' ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro y' hy' xv hxv
    rcases hxv with ⟨x, hx, rfl⟩
    have h1 : -50 ≤ x := (a10.hX_bounds (3 * y') (hy3 y' hy') hx).1
    have h2 : x ≤ 50 := (a10.hX_bounds (3 * y') (hy3 y' hy') hx).2
    constructor <;> linarith

  have hT'_bounds : ∀ z' hz', T'_coarse z' hz' ⊆ Set.Icc (-2 : ℝ) 2 ×ˢ Set.Icc (-2 : ℝ) 2 := by
    intro z' hz' p' hp'
    rcases hp' with ⟨p, hp, rfl⟩
    have h1 : -10 ≤ p.1 := ((a10.hT_bounds (origZ z') (h_origZ_mem z' hz') hp).1).1
    have h2 : p.1 ≤ 10 := ((a10.hT_bounds (origZ z') (h_origZ_mem z' hz') hp).1).2
    have h3 : -10 ≤ p.2 := ((a10.hT_bounds (origZ z') (h_origZ_mem z' hz') hp).2).1
    have h4 : p.2 ≤ 10 := ((a10.hT_bounds (origZ z') (h_origZ_mem z' hz') hp).2).2
    constructor <;> constructor <;> linarith

  -- Incidence
  have h_inc' : ∀ z' hz', ∀ (p' : ℝ × ℝ), p' ∈ T'_coarse z' hz' →
      |p'.1 * z'.2 + p'.2 - z'.1| ≤ 4 * Δ := by
    intro z' hz' p' hp'
    rcases hp' with ⟨p, hp, rfl⟩
    let z := origZ z'
    have hz : z ∈ a10.Z := h_origZ_mem z' hz'
    have h1 : |p.1 * z.2 + p.2 - z.1| ≤ 27 * Δ := a10.h_inc z hz p hp
    have h_eq : (3 * p.1 / 50 : ℝ) * z'.2 + (p.2 / 50 : ℝ) - z'.1 =
        (p.1 * z.2 + p.2 - z.1) / 50 := by
      have h_eq4 : (3 * p.1 / 50 : ℝ) * z'.2 + (p.2 / 50 : ℝ) - z'.1 =
          (p.1 * z.2 + p.2 - z.1) / 50 := by
        have hz1 : z.1 = 50 * z'.1 := by simp [origZ, z] <;> ring
        have hz2 : z.2 = 3 * z'.2 := by simp [origZ, z] <;> ring
        rw [hz1, hz2] <;> ring
      exact h_eq4
    rw [h_eq]
    have h3 : |(p.1 * z.2 + p.2 - z.1) / 50| = |p.1 * z.2 + p.2 - z.1| / 50 := by
      rw [abs_div] <;> norm_num
    rw [h3]
    linarith

  -- S-set transfer for Y' (scale by 1/3, then scale up)
  have hY_eq : Y' = (fun x : ℝ => (1 / 3 : ℝ) * x) '' a10.Y := by
    ext z; simp [Y', Set.mem_image] <;> constructor <;> rintro ⟨y, hy, h⟩ <;> refine ⟨y, hy, ?_⟩ <;> linarith
  have hY_raw1 : IsDeltaSSet ((1 / 3 : ℝ) * Δ) a10.τ
      (Real.rpow Δ (-10000 * ε) / (1 / 3 : ℝ) ^ a10.τ)
      ((fun x : ℝ => (1 / 3 : ℝ) * x) '' a10.Y) :=
    a10.hY_sset.scale1 (show (0 : ℝ) < 1 / 3 by norm_num)
  have hY_raw3 : IsDeltaSSet Δ a10.τ
      ((Real.rpow Δ (-10000 * ε) / (1 / 3 : ℝ) ^ a10.τ) * 9)
      ((fun x : ℝ => (1 / 3 : ℝ) * x) '' a10.Y) :=
    hY_raw1.scale_up1 (by positivity) hΔ_pos (by linarith) (by linarith)
  have h_const_eq : (Real.rpow Δ (-10000 * ε) / (1 / 3 : ℝ) ^ a10.τ) * 9 =
      Real.rpow Δ (-10000 * ε) * 3 ^ τ * 9 := by
    have h1 : (1 / 3 : ℝ) ^ a10.τ = 1 / (3 : ℝ) ^ a10.τ := by
      have h11 : (1 / 3 : ℝ) ^ a10.τ = (1 : ℝ) ^ a10.τ / (3 : ℝ) ^ a10.τ := Real.div_rpow (by norm_num) (by norm_num) a10.τ
      have h12 : (1 : ℝ) ^ a10.τ = 1 := by simp
      rw [h11, h12] <;> ring
    rw [h1]
    have h2 : 0 < (3 : ℝ) ^ a10.τ := Real.rpow_pos_of_pos (by norm_num) a10.τ
    field_simp [h2.ne'] <;> ring
  have hY'_sset : IsDeltaSSet Δ τ (Real.rpow Δ (-η_axiom)) Y' := by
    have hY_const : (Real.rpow Δ (-10000 * ε) / (1 / 3 : ℝ) ^ a10.τ) * 9 ≤ Real.rpow Δ (-η_axiom) := by
      rw [h_const_eq]
      have h : Real.rpow Δ (-10000 * ε) * 3 ^ τ * 9 = (9 * 3 ^ τ) * Real.rpow Δ (-10000 * ε) := by ring
      rw [h]
      exact h_absorb_Y
    have h4 : IsDeltaSSet Δ a10.τ (Real.rpow Δ (-η_axiom)) ((fun x : ℝ => (1 / 3 : ℝ) * x) '' a10.Y) :=
      IsDeltaSSet.mono_const hY_raw3 hY_const
    simpa [hY_eq] using h4

  -- S-set transfer for X' (scale by 1/50, then scale up 3×)
  have hX_eq : ∀ y' hy', X' y' hy' = (fun x : ℝ => (1 / 50 : ℝ) * x) '' a10.X (3 * y') (hy3 y' hy') := by
    intro y' hy'
    ext z; simp [X', Set.mem_image] <;> constructor <;> rintro ⟨x, hx, h⟩ <;> refine ⟨x, hx, ?_⟩ <;> linarith
  have h_scale_eq50 : (1 / 50 : ℝ) * Δ = Δ / 50 := by ring
  have h1_50 : (1 / 50 : ℝ) ^ s = 1 / (50 : ℝ) ^ s := by
    have h11 : (1 / 50 : ℝ) ^ s = (1 : ℝ) ^ s / (50 : ℝ) ^ s := Real.div_rpow (by norm_num) (by norm_num) s
    have h12 : (1 : ℝ) ^ s = 1 := by simp
    rw [h11, h12] <;> ring
  have h_const_eq50 : Real.rpow Δ (-600 * ε) / (1 / 50 : ℝ) ^ s =
      Real.rpow Δ (-600 * ε) * 50 ^ s := by
    rw [h1_50]
    have h2 : 0 < (50 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    field_simp [h2.ne'] <;> ring
  have hX_raw2 : ∀ y' hy', IsDeltaSSet (Δ / 50) s
      (Real.rpow Δ (-600 * ε) * 50 ^ s) (X' y' hy') := by
    intro y' hy'
    have h : IsDeltaSSet ((1 / 50 : ℝ) * Δ) s
        (Real.rpow Δ (-600 * ε) / (1 / 50 : ℝ) ^ s)
        ((fun x : ℝ => (1 / 50 : ℝ) * x) '' a10.X (3 * y') (hy3 y' hy')) :=
      (a10.hX_sset (3 * y') (hy3 y' hy')).scale1 (show (0 : ℝ) < 1 / 50 by norm_num)
    have h2 : IsDeltaSSet (Δ / 50) s (Real.rpow Δ (-600 * ε) * 50 ^ s)
        ((fun x : ℝ => (1 / 50 : ℝ) * x) '' a10.X (3 * y') (hy3 y' hy')) := by
      have h3 := h
      rw [h_scale_eq50, h_const_eq50] at h3
      exact h3
    simpa [hX_eq y' hy'] using h2
  have hX_raw3 : ∀ y' hy', IsDeltaSSet Δ s
      (Real.rpow Δ (-600 * ε) * 50 ^ s * 9 ^ 3) (X' y' hy') :=
    fun y' hy' => IsDeltaSSet.scale_up1_50 hΔ_pos (hX_raw2 y' hy')
  have hX_const : ∀ (y' : ℝ) (hy' : y' ∈ Y'), Real.rpow Δ (-600 * ε) * 50 ^ s * 9 ^ 3 ≤
      Real.rpow Δ (-η_axiom) := by
    intro y' hy'
    have h : Real.rpow Δ (-600 * ε) * 50 ^ s * 9 ^ 3 =
        (729 * 50 ^ s) * Real.rpow Δ (-600 * ε) := by ring
    rw [h]
    exact h_absorb_X
  have hX'_sset : ∀ y' hy', IsDeltaSSet Δ s (Real.rpow Δ (-η_axiom)) (X' y' hy') :=
    fun y' hy' => IsDeltaSSet.mono_const (hX_raw3 y' hy') (hX_const y' hy')

  -- S-set transfer for T'_coarse
  let g_scale : ℝ × ℝ → ℝ × ℝ := fun p => (p.1 / 50, p.2 / 50)
  let h_scale : ℝ × ℝ → ℝ × ℝ := fun q => (3 * q.1, q.2)
  have hT_decomp : ∀ z' hz', T'_coarse z' hz' =
      h_scale '' (g_scale '' (a10.T_coarse (origZ z') (h_origZ_mem z' hz'))) := by
    intro z' hz'
    ext p'
    simp only [T'_coarse, Set.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨g_scale p, ⟨p, hp, rfl⟩, ?_⟩
      simp [h_scale, g_scale] <;> ring
    · rintro ⟨q, ⟨p, hp, hq⟩, rfl⟩
      have hq_eq : q = g_scale p := by
        have hq' : (p.1 / 50, p.2 / 50) = q := by simpa [g_scale] using hq
        exact hq'.symm
      rw [hq_eq]
      refine ⟨p, hp, ?_⟩
      simp [h_scale, g_scale] <;> ring
  have hg_eq : g_scale = (fun p : ℝ × ℝ => ((1 / 50 : ℝ) * p.1, (1 / 50 : ℝ) * p.2)) := by
    funext p; ext <;> simp [g_scale] <;> ring
  have hT_raw2 : ∀ z' hz', IsDeltaSSet (Δ / 50) s
      (Real.rpow Δ (-600 * ε) * 50 ^ s)
      (g_scale '' (a10.T_coarse (origZ z') (h_origZ_mem z' hz'))) := by
    intro z' hz'
    have h : IsDeltaSSet ((1 / 50 : ℝ) * Δ) s
        (Real.rpow Δ (-600 * ε) / (1 / 50 : ℝ) ^ s)
        ((fun p : ℝ × ℝ => ((1 / 50 : ℝ) * p.1, (1 / 50 : ℝ) * p.2)) ''
          (a10.T_coarse (origZ z') (h_origZ_mem z' hz'))) :=
      (a10.hT_sset (origZ z') (h_origZ_mem z' hz')).scale2 (show (0 : ℝ) < 1 / 50 by norm_num)
    have h2 : IsDeltaSSet (Δ / 50) s (Real.rpow Δ (-600 * ε) * 50 ^ s)
        (g_scale '' (a10.T_coarse (origZ z') (h_origZ_mem z' hz'))) := by
      have h3 := h
      rw [h_scale_eq50, h_const_eq50] at h3
      rw [←hg_eq] at h3
      exact h3
    exact h2
  have hT_raw3 : ∀ z' hz', IsDeltaSSet Δ s
      (Real.rpow Δ (-600 * ε) * 50 ^ s * 81 ^ 3)
      (g_scale '' (a10.T_coarse (origZ z') (h_origZ_mem z' hz'))) :=
    fun z' hz' => IsDeltaSSet.scale_up2_50 hΔ_pos (hT_raw2 z' hz')
  have hT_raw4 : ∀ z' hz', IsDeltaSSet Δ s
      ((Real.rpow Δ (-600 * ε) * 50 ^ s * 81 ^ 3) * 16)
      (T'_coarse z' hz') := by
    intro z' hz'
    rw [hT_decomp z' hz']
    have hC_pos : 0 < (Real.rpow Δ (-600 * ε) * 50 ^ s * 81 ^ 3) := by
      have h1 : 0 < Real.rpow Δ (-600 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h2 : 0 < (50 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
      positivity
    have h4 := IsDeltaSSet.expand_x3 hΔ_pos (by linarith) hC_pos (hT_raw3 z' hz')
    have h5 : 16 * (Real.rpow Δ (-600 * ε) * 50 ^ s * 81 ^ 3) =
        (Real.rpow Δ (-600 * ε) * 50 ^ s * 81 ^ 3) * 16 := by ring
    rw [h5] at h4
    exact h4
  have hT_const : ∀ (z' : ℝ × ℝ) (hz' : z' ∈ Z'), (Real.rpow Δ (-600 * ε) * 50 ^ s * 81 ^ 3) * 16 ≤
      Real.rpow Δ (-η_axiom) := by
    intro z' hz'
    have h : (Real.rpow Δ (-600 * ε) * 50 ^ s * 81 ^ 3) * 16 =
        (81 ^ 3 * 16 * 50 ^ s) * Real.rpow Δ (-600 * ε) := by ring
    rw [h]
    exact h_absorb_T
  have hT'_sset : ∀ z' hz', IsDeltaSSet Δ s (Real.rpow Δ (-η_axiom)) (T'_coarse z' hz') :=
    fun z' hz' => IsDeltaSSet.mono_const (hT_raw4 z' hz') (hT_const z' hz')

  -- Upper bound transfer via Lipschitz
  let T'_union : Set (ℝ × ℝ) := ⋃ (z' : ℝ × ℝ) (hz' : z' ∈ Z'), T'_coarse z' hz'
  let T_union : Set (ℝ × ℝ) := ⋃ (z : ℝ × ℝ) (hz : z ∈ a10.Z), a10.T_coarse z hz

  let f_scale : ℝ × ℝ → ℝ × ℝ := fun p => (3 * p.1 / 50, p.2 / 50)

  have hT'_union_sub : T'_union ⊆ f_scale '' T_union := by
    intro p' hp'
    rcases Set.mem_iUnion₂.mp hp' with ⟨z', hz', hp'⟩
    rcases hp' with ⟨p, hp, rfl⟩
    have hz : origZ z' ∈ a10.Z := h_origZ_mem z' hz'
    have hp_in_union : p ∈ T_union := by
      exact Set.mem_iUnion₂.mpr ⟨origZ z', hz, hp⟩
    exact ⟨p, hp_in_union, rfl⟩

  have h_f_lip : LipschitzWith (1 : NNReal) f_scale := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [f_scale, Prod.dist_eq, Real.dist_eq]
    have h1 : |3 * x.1 / 50 - 3 * y.1 / 50| ≤ |x.1 - y.1| := by
      have h : |3 * x.1 / 50 - 3 * y.1 / 50| = (3 / 50 : ℝ) * |x.1 - y.1| := by
        have h2 : 3 * x.1 / 50 - 3 * y.1 / 50 = (3 / 50 : ℝ) * (x.1 - y.1) := by ring
        rw [h2, abs_mul] <;> norm_num
      rw [h]
      have h3 : (3 / 50 : ℝ) ≤ 1 := by norm_num
      have h4 : 0 ≤ |x.1 - y.1| := abs_nonneg _
      nlinarith
    have h2 : |x.2 / 50 - y.2 / 50| ≤ |x.2 - y.2| := by
      have h : |x.2 / 50 - y.2 / 50| = (1 / 50 : ℝ) * |x.2 - y.2| := by
        have h2 : x.2 / 50 - y.2 / 50 = (1 / 50 : ℝ) * (x.2 - y.2) := by ring
        rw [h2, abs_mul] <;> norm_num
      rw [h]
      have h3 : (1 / 50 : ℝ) ≤ 1 := by norm_num
      have h4 : 0 ≤ |x.2 - y.2| := abs_nonneg _
      nlinarith
    have h3 : max (|3 * x.1 / 50 - 3 * y.1 / 50|) (|x.2 / 50 - y.2 / 50|) ≤
        max (|x.1 - y.1|) (|x.2 - y.2|) := by
      apply max_le
      · exact le_trans h1 (le_max_left _ _)
      · exact le_trans h2 (le_max_right _ _)
    simpa using h3

  have h_upper_transfer : (Metric.externalCoveringNumber Δ.toNNReal T'_union : ENNReal) ≤
      (Metric.externalCoveringNumber Δ.toNNReal T_union : ENNReal) := by
    have h1 : (Metric.externalCoveringNumber Δ.toNNReal T'_union : ENNReal) ≤
        (Metric.externalCoveringNumber Δ.toNNReal (f_scale '' T_union) : ENNReal) :=
      by exact_mod_cast Metric.externalCoveringNumber_mono_set hT'_union_sub
    have h2 : (Metric.externalCoveringNumber Δ.toNNReal (f_scale '' T_union) : ENNReal) ≤
        (Metric.externalCoveringNumber Δ.toNNReal T_union : ENNReal) := by
      have h3 := externalCoveringNumber_image_lipschitz (hf := h_f_lip) (ε := Δ.toNNReal) (A := T_union)
      simpa using h3
    exact le_trans h1 h2

  -- h_upper already at relaxed exponent η_upper (supplied as separate argument)
  have h_upper_original : (Metric.externalCoveringNumber Δ.toNNReal T_union : ENNReal) <
      ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper))) := h_upper

  have h_upper' : (Metric.externalCoveringNumber Δ.toNNReal T'_union : ENNReal) <
      ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper))) := by
    have h1 : (Metric.externalCoveringNumber Δ.toNNReal T'_union : ENNReal) ≤
        (Metric.externalCoveringNumber Δ.toNNReal T_union : ENNReal) := h_upper_transfer
    exact lt_of_le_of_lt h1 h_upper_original

  exact product_configuration_contradiction_decoupled
    hs hs1 hτ_pos hΔ_pos hΔ_lt_one
    hη_axiom_pos hη_upper_pos hη_axiom_pos
    (by linarith) hη_upper_lt
    δ₀ hδ₀_pos hΔ_le_δ₀ hA7
    hY'_bounds hX'_bounds hT'_bounds
    hY'_sset hX'_sset hT'_sset
    h_inc' h_upper'

end DirecretisedFurstenbergEstimate.A11
