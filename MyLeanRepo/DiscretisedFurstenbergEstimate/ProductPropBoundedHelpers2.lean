module

/-
  Bounded productProp from A.7 axiom — Helpers part 2.

  Contains: interval covering, scale change lemmas, Lipschitz
  transformations, pigeonhole principles, and tube union covering bounds.
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Translation
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RealAnalysis
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBoundedHelpers1b
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

open DiscretisedFurstenbergEstimate.CoveringUtils
open DiscretisedFurstenbergEstimate.Translation

noncomputable section

namespace DirecretisedFurstenbergEstimate

open DiscretisedFurstenbergEstimate.CoveringUtils

/-! ### Interval covering helper for scale-up -/

/-- Given x in [c-δ₂, c+δ₂] and δ₂ ≤ 4δ₁, there exists i ∈ {0,1,2,3} such that
|x - (c - δ₂ + (2i+1)δ₁)| ≤ δ₁. -/
lemma interval_cover_helper {δ₁ δ₂ c x : ℝ} (hδ₁ : 0 < δ₁) (h_scale : δ₂ ≤ 4 * δ₁)
    (h_left : c - δ₂ ≤ x) (h_right : x ≤ c + δ₂) :
    ∃ (i : ℕ), i ≤ 3 ∧ |x - (c - δ₂ + (2 * (i : ℝ) + 1) * δ₁)| ≤ δ₁ := by
  by_cases h6 : x ≤ c - δ₂ + 2 * δ₁
  · have h11 : -(δ₁) ≤ x - (c - δ₂ + δ₁) := by linarith
    have h12 : x - (c - δ₂ + δ₁) ≤ δ₁ := by linarith
    have h13 : |x - (c - δ₂ + δ₁)| ≤ δ₁ := abs_le.mpr ⟨h11, h12⟩
    have h_eq : (c - δ₂ + (2 * ((0 : ℕ) : ℝ) + 1) * δ₁) = c - δ₂ + δ₁ := by
      have h : (2 * ((0 : ℕ) : ℝ) + 1) = (1 : ℝ) := by norm_cast
      rw [h] <;> ring
    have h_goal : |x - (c - δ₂ + (2 * ((0 : ℕ) : ℝ) + 1) * δ₁)| ≤ δ₁ := by
      rw [h_eq]; exact h13
    exact ⟨0, by norm_num, h_goal⟩
  · have h6' : x > c - δ₂ + 2 * δ₁ := by linarith
    by_cases h7 : x ≤ c - δ₂ + 4 * δ₁
    · have h11 : -(δ₁) ≤ x - (c - δ₂ + 3 * δ₁) := by linarith
      have h12 : x - (c - δ₂ + 3 * δ₁) ≤ δ₁ := by linarith
      have h13 : |x - (c - δ₂ + 3 * δ₁)| ≤ δ₁ := abs_le.mpr ⟨h11, h12⟩
      have h_eq : (c - δ₂ + (2 * ((1 : ℕ) : ℝ) + 1) * δ₁) = c - δ₂ + 3 * δ₁ := by
        have h : (2 * ((1 : ℕ) : ℝ) + 1) = (3 : ℝ) := by norm_cast
        rw [h] <;> ring
      have h_goal : |x - (c - δ₂ + (2 * ((1 : ℕ) : ℝ) + 1) * δ₁)| ≤ δ₁ := by
        rw [h_eq]; exact h13
      exact ⟨1, by norm_num, h_goal⟩
    · have h7' : x > c - δ₂ + 4 * δ₁ := by linarith
      by_cases h8 : x ≤ c - δ₂ + 6 * δ₁
      · have h11 : -(δ₁) ≤ x - (c - δ₂ + 5 * δ₁) := by linarith
        have h12 : x - (c - δ₂ + 5 * δ₁) ≤ δ₁ := by linarith
        have h13 : |x - (c - δ₂ + 5 * δ₁)| ≤ δ₁ := abs_le.mpr ⟨h11, h12⟩
        have h_eq : (c - δ₂ + (2 * ((2 : ℕ) : ℝ) + 1) * δ₁) = c - δ₂ + 5 * δ₁ := by
          have h : (2 * ((2 : ℕ) : ℝ) + 1) = (5 : ℝ) := by norm_cast
          rw [h] <;> ring
        have h_goal : |x - (c - δ₂ + (2 * ((2 : ℕ) : ℝ) + 1) * δ₁)| ≤ δ₁ := by
          rw [h_eq]; exact h13
        exact ⟨2, by norm_num, h_goal⟩
      · have h8' : x > c - δ₂ + 6 * δ₁ := by linarith
        have h9 : c + δ₂ ≤ c - δ₂ + 8 * δ₁ := by linarith [h_scale]
        have h11 : -(δ₁) ≤ x - (c - δ₂ + 7 * δ₁) := by linarith
        have h12 : x - (c - δ₂ + 7 * δ₁) ≤ δ₁ := by linarith
        have h13 : |x - (c - δ₂ + 7 * δ₁)| ≤ δ₁ := abs_le.mpr ⟨h11, h12⟩
        have h_eq : (c - δ₂ + (2 * ((3 : ℕ) : ℝ) + 1) * δ₁) = c - δ₂ + 7 * δ₁ := by
          have h : (2 * ((3 : ℕ) : ℝ) + 1) = (7 : ℝ) := by norm_cast
          rw [h] <;> ring
        have h_goal : |x - (c - δ₂ + (2 * ((3 : ℕ) : ℝ) + 1) * δ₁)| ≤ δ₁ := by
          rw [h_eq]; exact h13
        exact ⟨3, by norm_num, h_goal⟩

/-- covering_{δ₁}(A) ≤ 4 * covering_{δ₂}(A) in 1D when δ₂ ≤ 4δ₁. -/
lemma covering_scale_1d {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (h_scale : δ₂ ≤ 4 * δ₁)
    {A : Set ℝ} :
    Metric.externalCoveringNumber δ₁.toNNReal A ≤ 4 * Metric.externalCoveringNumber δ₂.toNNReal A := by
  by_cases h_top : Metric.externalCoveringNumber δ₂.toNNReal A = ⊤
  · rw [h_top]; simp
  · have h_fin : Metric.externalCoveringNumber δ₂.toNNReal A < ⊤ :=
      lt_top_iff_ne_top.mpr h_top
    rcases exists_external_cover_eq h_fin with ⟨Cset, hC, h_eq⟩
    have hCfin : Cset.Finite := by
      have h : Cset.encard < ⊤ := h_eq.symm ▸ h_fin
      exact Set.encard_lt_top_iff.mp h
    let Cfin : Finset ℝ := hCfin.toFinset
    have hCfin_coe : (Cfin : Set ℝ) = Cset := by ext z; simp [Cfin, Set.Finite.mem_toFinset]
    let ball_cover (c : ℝ) : Finset ℝ :=
      Finset.image (fun i : ℕ => c - δ₂ + (2 * (i : ℝ) + 1) * δ₁) (Finset.range 4)
    have h_ball_cover : ∀ (c : ℝ),
        Metric.closedBall c δ₂ ⊆ ⋃ d ∈ (ball_cover c : Set ℝ), Metric.closedBall d δ₁ := by
      intro c
      intro x hx
      have hdist : dist x c ≤ δ₂ := (Metric.mem_closedBall).mp hx
      have h_ab : |x - c| ≤ δ₂ := by simpa [dist_eq_norm] using hdist
      have h_left : c - δ₂ ≤ x := by linarith [abs_le.mp h_ab]
      have h_right : x ≤ c + δ₂ := by linarith [abs_le.mp h_ab]
      rcases interval_cover_helper hδ₁ h_scale h_left h_right with ⟨i, hi, hball_abs⟩
      let d : ℝ := c - δ₂ + (2 * (i : ℝ) + 1) * δ₁
      have hi4 : i ∈ Finset.range 4 := by
        simp only [Finset.mem_range] <;> omega
      have hd_in : d ∈ (ball_cover c : Set ℝ) := by
        apply Finset.mem_coe.mpr
        apply Finset.mem_image.mpr
        exact ⟨i, hi4, rfl⟩
      have hball : x ∈ Metric.closedBall d δ₁ := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hball_abs
      exact Set.mem_iUnion₂.mpr ⟨d, hd_in, hball⟩
    let S : Finset ℝ := Cfin.biUnion ball_cover
    have hScover : Metric.IsCover δ₁.toNNReal A (S : Set ℝ) := by
      intro x hx
      have h6 : ∃ (c : ℝ), c ∈ Cset ∧ edist x c ≤ ↑δ₂.toNNReal := hC hx
      rcases h6 with ⟨c, hcC, hedist⟩
      have hcfin : c ∈ Cfin := by
        have h : c ∈ (Cfin : Set ℝ) := by rw [hCfin_coe]; exact hcC
        exact_mod_cast h
      have hδ₂_nn : 0 ≤ δ₂ := by linarith
      have h7 : dist x c ≤ δ₂ := by
        rw [edist_dist] at hedist
        have h71 : ENNReal.ofReal (dist x c) ≤ ENNReal.ofReal δ₂ := by
          simpa [ENNReal.ofReal, Real.toNNReal_of_nonneg hδ₂_nn] using hedist
        exact (ENNReal.ofReal_le_ofReal_iff hδ₂_nn).mp h71
      have h8 : x ∈ (⋃ d ∈ (ball_cover c : Set ℝ), Metric.closedBall d δ₁) :=
        (h_ball_cover c) (show x ∈ Metric.closedBall c δ₂ from h7)
      rcases Set.mem_iUnion₂.mp h8 with ⟨d, hd, hball⟩
      have hdin : d ∈ S := Finset.mem_biUnion.mpr ⟨c, hcfin, hd⟩
      have hδ₁_nn : 0 ≤ δ₁ := by linarith
      have h9 : edist x d ≤ ↑δ₁.toNNReal := by
        rw [edist_dist]
        have h10 : dist x d ≤ δ₁ := by simpa [Metric.mem_closedBall] using hball
        have h11 : ENNReal.ofReal (dist x d) ≤ ENNReal.ofReal δ₁ := ENNReal.ofReal_le_ofReal h10
        simpa [ENNReal.ofReal, Real.toNNReal_of_nonneg hδ₁_nn] using h11
      exact ⟨d, hdin, h9⟩
    have h1 : Metric.externalCoveringNumber δ₁.toNNReal A ≤ (S : Set ℝ).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hScover
    have h_card : ∀ c ∈ Cfin, (ball_cover c).card ≤ 4 := by
      intro c _
      have h : (ball_cover c).card ≤ (Finset.range 4).card := Finset.card_image_le
      simpa using h
    have h2 : S.card ≤ 4 * Cfin.card := by
      calc S.card
        ≤ ∑ c ∈ Cfin, (ball_cover c).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ Cfin, 4 := Finset.sum_le_sum h_card
      _ = 4 * Cfin.card := by simp [Finset.sum_const] <;> ring
    have h3 : (S : Set ℝ).encard = ↑S.card := by simp
    have h4 : Cset.encard = Metric.externalCoveringNumber δ₂.toNNReal A := h_eq
    have h5 : (Cfin : Set ℝ).encard = Cset.encard := by rw [hCfin_coe]
    calc Metric.externalCoveringNumber δ₁.toNNReal A
      ≤ (S : Set ℝ).encard := h1
    _ = ↑S.card := h3
    _ ≤ ↑(4 * Cfin.card) := by exact_mod_cast h2
    _ = 4 * ↑Cfin.card := by simp
    _ = 4 * (Cfin : Set ℝ).encard := by simp
    _ = 4 * Cset.encard := by rw [h5]
    _ = 4 * Metric.externalCoveringNumber δ₂.toNNReal A := by rw [h4]

/-- covering_{δ₁}(A) ≤ 16 * covering_{δ₂}(A) in 2D when δ₂ ≤ 4δ₁. -/
lemma covering_scale_2d {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (h_scale : δ₂ ≤ 4 * δ₁)
    {A : Set (ℝ × ℝ)} :
    Metric.externalCoveringNumber δ₁.toNNReal A ≤ 16 * Metric.externalCoveringNumber δ₂.toNNReal A := by
  by_cases h_top : Metric.externalCoveringNumber δ₂.toNNReal A = ⊤
  · rw [h_top]; simp
  · have h_fin : Metric.externalCoveringNumber δ₂.toNNReal A < ⊤ :=
      lt_top_iff_ne_top.mpr h_top
    rcases exists_external_cover_eq h_fin with ⟨Cset, hC, h_eq⟩
    have hCfin : Cset.Finite := by
      have h : Cset.encard < ⊤ := h_eq.symm ▸ h_fin
      exact Set.encard_lt_top_iff.mp h
    let Cfin : Finset (ℝ × ℝ) := hCfin.toFinset
    have hCfin_coe : (Cfin : Set (ℝ × ℝ)) = Cset := by ext z; simp [Cfin, Set.Finite.mem_toFinset]
    let offsets : Finset (ℝ × ℝ) :=
      Finset.image (fun ij : ℕ × ℕ => ((2 * ij.1 + 1 : ℝ) * δ₁, (2 * ij.2 + 1 : ℝ) * δ₁))
        (Finset.Icc 0 3 ×ˢ Finset.Icc 0 3)
    let ball_cover (c : ℝ × ℝ) : Finset (ℝ × ℝ) :=
      offsets.image (fun off => (c.1 - δ₂ + off.1, c.2 - δ₂ + off.2))
    have h_ball_cover : ∀ (c : ℝ × ℝ),
        Metric.closedBall c δ₂ ⊆ ⋃ p ∈ (ball_cover c : Set (ℝ × ℝ)), Metric.closedBall p δ₁ := by
      intro c
      intro x hx
      have hdist : dist x c ≤ δ₂ := (Metric.mem_closedBall).mp hx
      have h_x1 : |x.1 - c.1| ≤ δ₂ := by
        have h1 : |x.1 - c.1| ≤ dist x c := by
          rw [Prod.dist_eq]; exact le_max_left (|x.1 - c.1|) (|x.2 - c.2|)
        linarith
      have h_x2 : |x.2 - c.2| ≤ δ₂ := by
        have h2 : |x.2 - c.2| ≤ dist x c := by
          rw [Prod.dist_eq]; exact le_max_right (|x.1 - c.1|) (|x.2 - c.2|)
        linarith
      have h_left1 : c.1 - δ₂ ≤ x.1 := by linarith [abs_le.mp h_x1]
      have h_right1 : x.1 ≤ c.1 + δ₂ := by linarith [abs_le.mp h_x1]
      have h_left2 : c.2 - δ₂ ≤ x.2 := by linarith [abs_le.mp h_x2]
      have h_right2 : x.2 ≤ c.2 + δ₂ := by linarith [abs_le.mp h_x2]
      rcases interval_cover_helper hδ₁ h_scale h_left1 h_right1 with ⟨i, hi, hxi⟩
      rcases interval_cover_helper hδ₁ h_scale h_left2 h_right2 with ⟨j, hj, hxj⟩
      let p : ℝ × ℝ := (c.1 - δ₂ + (2 * (i : ℝ) + 1) * δ₁, c.2 - δ₂ + (2 * (j : ℝ) + 1) * δ₁)
      have hi4 : i ∈ Finset.Icc (0 : ℕ) 3 := by
        simp only [Finset.mem_Icc] <;> omega
      have hj4 : j ∈ Finset.Icc (0 : ℕ) 3 := by
        simp only [Finset.mem_Icc] <;> omega
      have hp_in : p ∈ (ball_cover c : Set (ℝ × ℝ)) := by
        apply Finset.mem_coe.mpr
        apply Finset.mem_image.mpr
        let off : ℝ × ℝ := ((2 * (i : ℝ) + 1) * δ₁, (2 * (j : ℝ) + 1) * δ₁)
        have h_off_in : off ∈ offsets := by
          apply Finset.mem_image.mpr
          refine ⟨(i, j), ?_, rfl⟩
          simp only [offsets, Finset.mem_product] <;> exact ⟨hi4, hj4⟩
        exact ⟨off, h_off_in, by simp [p, off] <;> ring⟩
      have hball : x ∈ Metric.closedBall p δ₁ := by
        simp [p, Metric.mem_closedBall, Prod.dist_eq, max_le_iff] <;> exact ⟨hxi, hxj⟩
      exact Set.mem_iUnion₂.mpr ⟨p, hp_in, hball⟩
    let S : Finset (ℝ × ℝ) := Cfin.biUnion ball_cover
    have hScover : Metric.IsCover δ₁.toNNReal A (S : Set (ℝ × ℝ)) := by
      intro x hx
      have h6 : ∃ (c : ℝ × ℝ), c ∈ Cset ∧ edist x c ≤ ↑δ₂.toNNReal := hC hx
      rcases h6 with ⟨c, hcC, hedist⟩
      have hcfin : c ∈ Cfin := by
        have h : c ∈ (Cfin : Set (ℝ × ℝ)) := by rw [hCfin_coe]; exact hcC
        exact_mod_cast h
      have hδ₂_nn : 0 ≤ δ₂ := by linarith
      have h7 : dist x c ≤ δ₂ := by
        rw [edist_dist] at hedist
        have h71 : ENNReal.ofReal (dist x c) ≤ ENNReal.ofReal δ₂ := by
          simpa [ENNReal.ofReal, Real.toNNReal_of_nonneg hδ₂_nn] using hedist
        exact (ENNReal.ofReal_le_ofReal_iff hδ₂_nn).mp h71
      have h8 : x ∈ (⋃ d ∈ (ball_cover c : Set (ℝ × ℝ)), Metric.closedBall d δ₁) :=
        (h_ball_cover c) (show x ∈ Metric.closedBall c δ₂ from h7)
      rcases Set.mem_iUnion₂.mp h8 with ⟨d, hd, hball⟩
      have hdin : d ∈ S := Finset.mem_biUnion.mpr ⟨c, hcfin, hd⟩
      have hδ₁_nn : 0 ≤ δ₁ := by linarith
      have h9 : edist x d ≤ ↑δ₁.toNNReal := by
        rw [edist_dist]
        have h10 : dist x d ≤ δ₁ := by simpa [Metric.mem_closedBall] using hball
        have h11 : ENNReal.ofReal (dist x d) ≤ ENNReal.ofReal δ₁ := ENNReal.ofReal_le_ofReal h10
        simpa [ENNReal.ofReal, Real.toNNReal_of_nonneg hδ₁_nn] using h11
      exact ⟨d, hdin, h9⟩
    have h1 : Metric.externalCoveringNumber δ₁.toNNReal A ≤ (S : Set (ℝ × ℝ)).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hScover
    have h_card : ∀ c ∈ Cfin, (ball_cover c).card ≤ 16 := by
      intro c _
      have h : (ball_cover c).card ≤ offsets.card := Finset.card_image_le
      have h2 : offsets.card ≤ 16 := by
        have h3 : offsets.card ≤ (Finset.Icc 0 3 ×ˢ Finset.Icc 0 3).card := Finset.card_image_le
        simpa using h3
      exact h.trans h2
    have h2 : S.card ≤ 16 * Cfin.card := by
      calc S.card
        ≤ ∑ c ∈ Cfin, (ball_cover c).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ Cfin, 16 := Finset.sum_le_sum h_card
      _ = 16 * Cfin.card := by simp [Finset.sum_const] <;> ring
    have h3 : (S : Set (ℝ × ℝ)).encard = ↑S.card := by simp
    have h4 : Cset.encard = Metric.externalCoveringNumber δ₂.toNNReal A := h_eq
    have h5 : (Cfin : Set (ℝ × ℝ)).encard = Cset.encard := by rw [hCfin_coe]
    calc Metric.externalCoveringNumber δ₁.toNNReal A
      ≤ (S : Set (ℝ × ℝ)).encard := h1
    _ = ↑S.card := h3
    _ ≤ ↑(16 * Cfin.card) := by exact_mod_cast h2
    _ = 16 * ↑Cfin.card := by simp
    _ = 16 * (Cfin : Set (ℝ × ℝ)).encard := by simp
    _ = 16 * Cset.encard := by rw [h5]
    _ = 16 * Metric.externalCoveringNumber δ₂.toNNReal A := by rw [h4]

/-- Interval cover helper for 10×10 grid: given x ∈ [c-10δ, c+10δ], there exists
i ∈ {0,...,9} such that |x - (c - 10δ + (2i+1)δ)| ≤ δ. -/
lemma interval_cover_10 {δ c x : ℝ} (hδ : 0 < δ)
    (h_left : c - 10 * δ ≤ x) (h_right : x ≤ c + 10 * δ) :
    ∃ (i : ℕ), i ≤ 9 ∧ |x - (c - 10 * δ + (2 * (i : ℝ) + 1) * δ)| ≤ δ := by
  let t : ℝ := (x - (c - 10 * δ)) / (2 * δ)
  have ht0 : 0 ≤ t := by
    have h : x - (c - 10 * δ) ≥ 0 := by linarith
    exact div_nonneg h (by positivity)
  have ht10 : t ≤ 10 := by
    have h : x - (c - 10 * δ) ≤ 20 * δ := by linarith
    have h2 : (x - (c - 10 * δ)) / (2 * δ) ≤ (20 * δ) / (2 * δ) := by gcongr
    have h3 : (20 * δ) / (2 * δ) = 10 := by
      field_simp [hδ.ne'] <;> ring
    rw [h3] at h2
    exact h2
  let i : ℕ := if t < 10 then Nat.floor t else 9
  have hi9 : i ≤ 9 := by
    by_cases h : t < 10
    · have h_i_eq : i = Nat.floor t := by simp [i, h]
      rw [h_i_eq]
      have hfl : (Nat.floor t : ℝ) ≤ t := Nat.floor_le ht0
      have hlt : (Nat.floor t : ℝ) < 10 := by linarith
      have hlt' : Nat.floor t < 10 := Nat.cast_lt.mp hlt
      exact Nat.lt_succ_iff.mp hlt'
    · have h_i_eq : i = 9 := by simp [i, h]
      rw [h_i_eq] <;> norm_num
  have h_i_le_t : (i : ℝ) ≤ t := by
    by_cases h : t < 10
    · have h_i_eq : i = Nat.floor t := by simp [i, h]
      rw [h_i_eq]
      exact Nat.floor_le ht0
    · have h' : t = 10 := by linarith
      have h_i_eq : i = 9 := by simp [i, h]
      rw [h_i_eq, h'] <;> norm_num
  have h_t_le_i1 : t ≤ (i : ℝ) + 1 := by
    by_cases h : t < 10
    · have h_i_eq : i = Nat.floor t := by simp [i, h]
      rw [h_i_eq]
      have h_lt : t < (Nat.floor t : ℝ) + 1 := Nat.lt_floor_add_one t
      linarith
    · have h' : t = 10 := by linarith
      have h_i_eq : i = 9 := by simp [i, h]
      rw [h_i_eq, h'] <;> norm_num
  have h_goal : |x - (c - 10 * δ + (2 * (i : ℝ) + 1) * δ)| ≤ δ := by
    have h_t_def : 2 * t * δ = x - (c - 10 * δ) := by
      simp [t] <;> field_simp [hδ.ne'] <;> ring
    have h_eq1 : x - (c - 10 * δ + (2 * (i : ℝ) + 1) * δ) = (2 * t - 2 * (i : ℝ) - 1) * δ := by
      have h : (2 * t - 2 * (i : ℝ) - 1) * δ = 2 * t * δ - 2 * (i : ℝ) * δ - δ := by ring
      rw [h, h_t_def] <;> ring
    rw [h_eq1]
    have h2 : -1 ≤ 2 * t - 2 * (i : ℝ) - 1 := by linarith [h_i_le_t]
    have h3 : 2 * t - 2 * (i : ℝ) - 1 ≤ 1 := by linarith [h_t_le_i1]
    have h4 : |2 * t - 2 * (i : ℝ) - 1| ≤ 1 := by
      exact abs_le.mpr ⟨h2, h3⟩
    calc |(2 * t - 2 * (i : ℝ) - 1) * δ|
      = |2 * t - 2 * (i : ℝ) - 1| * |δ| := by rw [abs_mul]
    _ ≤ 1 * |δ| := by gcongr
    _ = δ := by simp [abs_of_pos hδ]
  exact ⟨i, hi9, h_goal⟩

/-- Covering number scales by factor 100 from radius 10δ to radius δ in 2D. -/
lemma covering_10_2d {δ : ℝ} (hδ : 0 < δ) {A : Set (ℝ × ℝ)} :
    Metric.externalCoveringNumber δ.toNNReal A ≤ 100 * Metric.externalCoveringNumber (10 * δ).toNNReal A := by
  set δ₂ := 10 * δ with hδ₂_def
  have hδ₂_pos : 0 < δ₂ := by positivity
  by_cases h_top : Metric.externalCoveringNumber δ₂.toNNReal A = ⊤
  · rw [h_top]; simp
  · have h_fin : Metric.externalCoveringNumber δ₂.toNNReal A < ⊤ := lt_top_iff_ne_top.mpr h_top
    rcases exists_external_cover_eq h_fin with ⟨Cset, hC, h_eq⟩
    have hCfin : Cset.Finite := by
      have h : Cset.encard < ⊤ := h_eq.symm ▸ h_fin
      exact Set.encard_lt_top_iff.mp h
    let Cfin : Finset (ℝ × ℝ) := hCfin.toFinset
    have hCfin_coe : (Cfin : Set (ℝ × ℝ)) = Cset := by ext z; simp [Cfin, Set.Finite.mem_toFinset]
    let offsets : Finset (ℝ × ℝ) :=
      Finset.image (fun ij : ℕ × ℕ => ((2 * ij.1 + 1 : ℝ) * δ, (2 * ij.2 + 1 : ℝ) * δ))
        (Finset.Icc 0 9 ×ˢ Finset.Icc 0 9)
    let ball_cover (c : ℝ × ℝ) : Finset (ℝ × ℝ) :=
      offsets.image (fun off => (c.1 - δ₂ + off.1, c.2 - δ₂ + off.2))
    have h_ball_cover : ∀ (c : ℝ × ℝ),
        Metric.closedBall c δ₂ ⊆ ⋃ p ∈ (ball_cover c : Set (ℝ × ℝ)), Metric.closedBall p δ := by
      intro c x hx
      have hdist : dist x c ≤ δ₂ := (Metric.mem_closedBall).mp hx
      have h_x1 : |x.1 - c.1| ≤ δ₂ := by
        have h1 : |x.1 - c.1| ≤ dist x c := by rw [Prod.dist_eq]; exact le_max_left _ _
        linarith
      have h_x2 : |x.2 - c.2| ≤ δ₂ := by
        have h2 : |x.2 - c.2| ≤ dist x c := by rw [Prod.dist_eq]; exact le_max_right _ _
        linarith
      have h_left1 : c.1 - δ₂ ≤ x.1 := by linarith [abs_le.mp h_x1]
      have h_right1 : x.1 ≤ c.1 + δ₂ := by linarith [abs_le.mp h_x1]
      have h_left2 : c.2 - δ₂ ≤ x.2 := by linarith [abs_le.mp h_x2]
      have h_right2 : x.2 ≤ c.2 + δ₂ := by linarith [abs_le.mp h_x2]
      rcases interval_cover_10 hδ h_left1 h_right1 with ⟨i, hi, hxi⟩
      rcases interval_cover_10 hδ h_left2 h_right2 with ⟨j, hj, hxj⟩
      let p : ℝ × ℝ := (c.1 - δ₂ + (2 * (i : ℝ) + 1) * δ, c.2 - δ₂ + (2 * (j : ℝ) + 1) * δ)
      have hi10 : i ∈ Finset.Icc (0 : ℕ) 9 := by simp only [Finset.mem_Icc] <;> omega
      have hj10 : j ∈ Finset.Icc (0 : ℕ) 9 := by simp only [Finset.mem_Icc] <;> omega
      have hp_in : p ∈ (ball_cover c : Set (ℝ × ℝ)) := by
        apply Finset.mem_coe.mpr
        apply Finset.mem_image.mpr
        let off : ℝ × ℝ := ((2 * (i : ℝ) + 1) * δ, (2 * (j : ℝ) + 1) * δ)
        have h_off_in : off ∈ offsets := by
          apply Finset.mem_image.mpr
          refine ⟨(i, j), ?_, rfl⟩
          simp only [offsets, Finset.mem_product] <;> exact ⟨hi10, hj10⟩
        exact ⟨off, h_off_in, by simp [p, off] <;> ring⟩
      have hball : x ∈ Metric.closedBall p δ := by
        simp [p, Metric.mem_closedBall, Prod.dist_eq, max_le_iff] <;> exact ⟨hxi, hxj⟩
      exact Set.mem_iUnion₂.mpr ⟨p, hp_in, hball⟩
    let S : Finset (ℝ × ℝ) := Cfin.biUnion ball_cover
    have hScover : Metric.IsCover δ.toNNReal A (S : Set (ℝ × ℝ)) := by
      intro x hx
      have h6 : ∃ (c : ℝ × ℝ), c ∈ Cset ∧ edist x c ≤ ↑δ₂.toNNReal := hC hx
      rcases h6 with ⟨c, hcC, hedist⟩
      have hcfin : c ∈ Cfin := by
        have h : c ∈ (Cfin : Set (ℝ × ℝ)) := by rw [hCfin_coe]; exact hcC
        exact_mod_cast h
      have hδ₂_nn : 0 ≤ δ₂ := by linarith
      have h7 : dist x c ≤ δ₂ := by
        rw [edist_dist] at hedist
        have h71 : ENNReal.ofReal (dist x c) ≤ ENNReal.ofReal δ₂ := by
          simpa [ENNReal.ofReal, Real.toNNReal_of_nonneg hδ₂_nn] using hedist
        exact (ENNReal.ofReal_le_ofReal_iff hδ₂_nn).mp h71
      have h8 : x ∈ (⋃ d ∈ (ball_cover c : Set (ℝ × ℝ)), Metric.closedBall d δ) :=
        (h_ball_cover c) (show x ∈ Metric.closedBall c δ₂ from h7)
      rcases Set.mem_iUnion₂.mp h8 with ⟨d, hd, hball⟩
      have hdin : d ∈ S := Finset.mem_biUnion.mpr ⟨c, hcfin, hd⟩
      have hδ_nn : 0 ≤ δ := by linarith
      have h9 : edist x d ≤ ↑δ.toNNReal := by
        rw [edist_dist]
        have h10 : dist x d ≤ δ := by simpa [Metric.mem_closedBall] using hball
        have h11 : ENNReal.ofReal (dist x d) ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal h10
        simpa [ENNReal.ofReal, Real.toNNReal_of_nonneg hδ_nn] using h11
      exact ⟨d, hdin, h9⟩
    have h1 : Metric.externalCoveringNumber δ.toNNReal A ≤ (S : Set (ℝ × ℝ)).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hScover
    have h_card : ∀ c ∈ Cfin, (ball_cover c).card ≤ 100 := by
      intro c _
      have h : (ball_cover c).card ≤ offsets.card := Finset.card_image_le
      have h2 : offsets.card ≤ 100 := by
        have h3 : offsets.card ≤ (Finset.Icc 0 9 ×ˢ Finset.Icc 0 9).card := Finset.card_image_le
        simpa using h3
      exact h.trans h2
    have h2 : S.card ≤ 100 * Cfin.card := by
      calc S.card
        ≤ ∑ c ∈ Cfin, (ball_cover c).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ Cfin, 100 := Finset.sum_le_sum h_card
      _ = 100 * Cfin.card := by simp [Finset.sum_const] <;> ring
    have h3 : (S : Set (ℝ × ℝ)).encard = ↑S.card := by simp
    have h4 : Cset.encard = Metric.externalCoveringNumber δ₂.toNNReal A := h_eq
    have h5 : (Cfin : Set (ℝ × ℝ)).encard = Cset.encard := by rw [hCfin_coe]
    calc Metric.externalCoveringNumber δ.toNNReal A
      ≤ (S : Set (ℝ × ℝ)).encard := h1
    _ = ↑S.card := h3
    _ ≤ ↑(100 * Cfin.card) := by exact_mod_cast h2
    _ = 100 * ↑Cfin.card := by simp
    _ = 100 * (Cfin : Set (ℝ × ℝ)).encard := by simp
    _ = 100 * Cset.encard := by rw [h5]
    _ = 100 * Metric.externalCoveringNumber δ₂.toNNReal A := by rw [h4]

/-- Scale-up in 1D: (δ₁,s,C)-set → (δ₂,s,9C)-set when δ₁ ≤ δ₂ ≤ 4δ₁. -/
lemma IsDeltaSSet.scale_up1 {δ₁ δ₂ s C : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (h1 : δ₁ ≤ δ₂) (h2 : δ₂ ≤ 4 * δ₁) {A : Set ℝ}
    (hP : IsDeltaSSet δ₁ s C A) :
    IsDeltaSSet δ₂ s (C * 9) A := by
  have hC_pos : 0 < C := hP.2.2.1
  have hC9_pos : 0 < C * 9 := by positivity
  have h1' : δ₁.toNNReal ≤ δ₂.toNNReal := by
    have hδ₁_nn : 0 ≤ δ₁ := by linarith
    have hδ₂_nn : 0 ≤ δ₂ := by linarith
    exact (Real.toNNReal_le_toNNReal_iff hδ₂_nn).mpr h1
  have h61 : Metric.externalCoveringNumber δ₁.toNNReal A ≤ 4 * Metric.externalCoveringNumber δ₂.toNNReal A :=
    covering_scale_1d hδ₁ hδ₂ h2
  have h_main : ∀ (x : ℝ) (r : ℝ), δ₂ ≤ r →
      (Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal (C * 9) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal) := by
    intro x r hr
    have h3 : δ₁ ≤ r := by linarith
    have h41 : Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x r) ≤
        Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) :=
      Metric.externalCoveringNumber_anti h1'
    have h4 : (Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) := by
      exact_mod_cast h41
    have h5 : (Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) :=
      hP.2.2.2.2 x r h3
    have h6 : (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) ≤
        4 * (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal) := by
      exact_mod_cast h61
    have h7 : ENNReal.ofReal C * 4 ≤ ENNReal.ofReal (C * 9) := by
      have h : C * 4 ≤ C * 9 := by linarith [hC_pos]
      have h' : ENNReal.ofReal (C * 4) ≤ ENNReal.ofReal (C * 9) := ENNReal.ofReal_le_ofReal h
      have h'' : ENNReal.ofReal C * 4 = ENNReal.ofReal (C * 4) := by
        rw [ENNReal.ofReal_mul (by linarith)] <;> norm_num
      rw [h'']; exact h'
    calc (Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) := h4
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) := h5
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (4 * (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal)) := by
      gcongr
    _ = (ENNReal.ofReal C * 4) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal) := by ring
    _ ≤ ENNReal.ofReal (C * 9) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal) := by
      gcongr
  exact ⟨hP.1, hδ₂, hC9_pos, hP.2.2.2.1, h_main⟩

/-- Scale-up in 2D: (δ₁,s,C)-set → (δ₂,s,81C)-set when δ₁ ≤ δ₂ ≤ 4δ₁. -/
lemma IsDeltaSSet.scale_up2 {δ₁ δ₂ s C : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (h1 : δ₁ ≤ δ₂) (h2 : δ₂ ≤ 4 * δ₁) {A : Set (ℝ × ℝ)}
    (hP : IsDeltaSSet δ₁ s C A) :
    IsDeltaSSet δ₂ s (C * 81) A := by
  have hC_pos : 0 < C := hP.2.2.1
  have hC81_pos : 0 < C * 81 := by positivity
  have h1' : δ₁.toNNReal ≤ δ₂.toNNReal := by
    have hδ₁_nn : 0 ≤ δ₁ := by linarith
    have hδ₂_nn : 0 ≤ δ₂ := by linarith
    exact (Real.toNNReal_le_toNNReal_iff hδ₂_nn).mpr h1
  have h61 : Metric.externalCoveringNumber δ₁.toNNReal A ≤ 16 * Metric.externalCoveringNumber δ₂.toNNReal A :=
    covering_scale_2d hδ₁ hδ₂ h2
  have h_main : ∀ (x : ℝ × ℝ) (r : ℝ), δ₂ ≤ r →
      (Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal (C * 81) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal) := by
    intro x r hr
    have h3 : δ₁ ≤ r := by linarith
    have h41 : Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x r) ≤
        Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) :=
      Metric.externalCoveringNumber_anti h1'
    have h4 : (Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) := by
      exact_mod_cast h41
    have h5 : (Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) :=
      hP.2.2.2.2 x r h3
    have h6 : (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) ≤
        16 * (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal) := by
      exact_mod_cast h61
    have h7 : ENNReal.ofReal C * 16 ≤ ENNReal.ofReal (C * 81) := by
      have h : C * 16 ≤ C * 81 := by linarith [hC_pos]
      have h' : ENNReal.ofReal (C * 16) ≤ ENNReal.ofReal (C * 81) := ENNReal.ofReal_le_ofReal h
      have h'' : ENNReal.ofReal C * 16 = ENNReal.ofReal (C * 16) := by
        rw [ENNReal.ofReal_mul (by linarith)] <;> norm_num
      rw [h'']; exact h'
    calc (Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) := h4
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) := h5
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (16 * (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal)) := by
      gcongr
    _ = (ENNReal.ofReal C * 16) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal) := by ring
    _ ≤ ENNReal.ofReal (C * 81) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal) := by
      gcongr
  exact ⟨hP.1, hδ₂, hC81_pos, hP.2.2.2.1, h_main⟩

/-- Given 0 < δ ≤ 1, there exists a dyadic scale δ' with δ ≤ δ' < 2δ. -/
lemma exists_dyadic_scale_near (δ : ℝ) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) :
    ∃ (n : ℕ), δ ≤ (2 : ℝ)^(-(n : ℤ)) ∧ (2 : ℝ)^(-(n : ℤ)) < 2 * δ := by
  let x : ℝ := -Real.log δ / Real.log 2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx_nonneg : 0 ≤ x := by
    have h1 : Real.log δ ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    have h2 : 0 ≤ -Real.log δ := by linarith
    have h3 : 0 ≤ -Real.log δ / Real.log 2 := by positivity
    exact h3
  let n_int : ℤ := ⌊x⌋
  have hn_int_nonneg : 0 ≤ n_int := Int.floor_nonneg.mpr hx_nonneg
  let n : ℕ := n_int.toNat
  have hn_eq : (n : ℤ) = n_int := by
    simp [n, Int.toNat_of_nonneg hn_int_nonneg]
  have hn_real : (n : ℝ) = (n_int : ℝ) := by exact_mod_cast hn_eq
  have h1 : (n : ℝ) ≤ x := by
    rw [hn_real]; exact Int.floor_le x
  have h2 : x < (n : ℝ) + 1 := by
    rw [hn_real]; exact Int.lt_floor_add_one x
  have hx_eq : x = -Real.log δ / Real.log 2 := by rfl
  have h4 : -(n : ℝ) * Real.log 2 ≥ Real.log δ := by
    have h41 : (n : ℝ) ≤ -Real.log δ / Real.log 2 := by rw [←hx_eq]; exact h1
    have h42 : (n : ℝ) * Real.log 2 ≤ -Real.log δ := by
      calc (n : ℝ) * Real.log 2
        ≤ (-Real.log δ / Real.log 2) * Real.log 2 := by gcongr
      _ = -Real.log δ := by field_simp [hlog2_pos.ne'] <;> ring
    linarith
  have h5 : -(n : ℝ) * Real.log 2 < Real.log 2 + Real.log δ := by
    have h51 : -Real.log δ / Real.log 2 < (n : ℝ) + 1 := by rw [←hx_eq]; exact h2
    have h52 : -Real.log δ < (n : ℝ) * Real.log 2 + Real.log 2 := by
      calc -Real.log δ
        = (-Real.log δ / Real.log 2) * Real.log 2 := by field_simp [hlog2_pos.ne'] <;> ring
      _ < ((n : ℝ) + 1) * Real.log 2 := by gcongr
      _ = (n : ℝ) * Real.log 2 + Real.log 2 := by ring
    linarith
  have h6 : (2 : ℝ) ^ (-(n : ℤ)) ≥ δ := by
    have h7 : Real.log ((2 : ℝ) ^ (-(n : ℤ))) = (-(n : ℝ)) * Real.log 2 := by
      simp [Real.log_zpow] <;> ring
    have h8 : Real.log ((2 : ℝ) ^ (-(n : ℤ))) ≥ Real.log δ := by
      rw [h7]; exact h4
    exact Real.log_le_log_iff (by positivity) (by positivity) |>.mp h8
  have h9 : (2 : ℝ) ^ (-(n : ℤ)) < 2 * δ := by
    have h10 : Real.log ((2 : ℝ) ^ (-(n : ℤ))) = (-(n : ℝ)) * Real.log 2 := by
      simp [Real.log_zpow] <;> ring
    have h11 : Real.log ((2 : ℝ) ^ (-(n : ℤ))) < Real.log (2 * δ) := by
      rw [h10, Real.log_mul (by norm_num) (by linarith)]
      exact h5
    exact Real.log_lt_log_iff (by positivity) (by positivity) |>.mp h11
  exact ⟨n, h6, h9⟩

/-! ### Additional helpers for main proof (to be proved) -/

/-! ### S-set monotonicity and exponent capping -/

lemma IsDeltaSSet.mono_const {X : Type*} [PseudoMetricSpace X] {δ s C C' : ℝ} {A : Set X}
    (h : IsDeltaSSet δ s C A) (hC : C ≤ C') :
    IsDeltaSSet δ s C' A := by
  have hC'_pos : 0 < C' := by linarith [h.2.2.1]
  refine ⟨h.1, h.2.1, hC'_pos, h.2.2.2.1, ?_⟩
  intro x r hr
  have h4 := h.2.2.2.2 x r hr
  have h5 : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal hC
  calc
    (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) : ENNReal)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := h4
    _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by gcongr

lemma IsDeltaSSet.cap_exponent1d {δ s s' C : ℝ} {A : Set ℝ}
    (h : IsDeltaSSet δ s C A) (hs' : 0 ≤ s') (h_le : s' ≤ s)
    (hA_bdd : Bornology.IsBounded A) (hC_one : 1 ≤ C) :
    IsDeltaSSet δ s' C A := by
  have hA_nonempty : A.Nonempty := h.1
  have hδ_pos : 0 < δ := h.2.1
  have hC_pos : 0 < C := h.2.2.1
  have hs_nonneg : 0 ≤ s := h.2.2.2.1
  refine ⟨hA_nonempty, hδ_pos, hC_pos, hs', ?_⟩
  intro x r hr
  by_cases h_r_le_one : r ≤ 1
  · -- Case r ≤ 1: use original bound and r^s ≤ r^s'
    have h_r_pos : 0 < r := by linarith
    have h_rpow_real : r ^ s ≤ r ^ s' :=
      Real.rpow_le_rpow_of_exponent_ge h_r_pos h_r_le_one h_le
    have h_rpow_enn : (ENNReal.ofReal r) ^ s ≤ (ENNReal.ofReal r) ^ s' := by
      rw [ENNReal.ofReal_rpow_of_pos h_r_pos, ENNReal.ofReal_rpow_of_pos h_r_pos]
      exact ENNReal.ofReal_le_ofReal h_rpow_real
    have h_orig := h.2.2.2.2 x r hr
    have h_mul : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
      gcongr
    exact h_orig.trans h_mul
  · -- Case r > 1: A ∩ B(x,r) ⊆ A, and C * r^s' ≥ 1
    have h_r_gt_one : 1 < r := by linarith
    have h_sub : A ∩ Metric.closedBall x r ⊆ A := by simp
    have h1 : (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
      have h1' : Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x r) ≤
          Metric.externalCoveringNumber δ.toNNReal A :=
        Metric.externalCoveringNumber_mono_set h_sub
      exact_mod_cast h1'
    have hC1 : (1 : ENNReal) ≤ ENNReal.ofReal C := by
      have h : (1 : ℝ) ≤ C := hC_one
      have h' : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
      rw [h']
      exact ENNReal.ofReal_le_ofReal h
    have hr1 : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ s' := by
      have h3 : (1 : ENNReal) ≤ ENNReal.ofReal r := by
        have h4 : (1 : ℝ) ≤ r := by linarith
        have h5 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
        rw [h5]
        exact ENNReal.ofReal_le_ofReal h4
      have h4 : (ENNReal.ofReal r) ^ (0 : ℝ) ≤ (ENNReal.ofReal r) ^ s' :=
        ENNReal.rpow_le_rpow_of_exponent_le h3 hs'
      simpa using h4
    have h2 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' := by
      calc (1 : ENNReal)
        = (1 : ENNReal) * (1 : ENNReal) := by simp
        _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' := mul_le_mul' hC1 hr1
    have h3 : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' *
          (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
      have h4 : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) =
          (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by simp
      rw [h4]
      have h5 : (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
          (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s') * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      simpa [mul_assoc] using h5
    exact h1.trans h3

/-! ### transformTube inverse and Lipschitz bounds -/

/-- Inverse of transformTube: (a', b') ↦ (2a', 4b' + 2a' - 1). -/
def transformTubeInv (p : ℝ × ℝ) : ℝ × ℝ :=
  (2 * p.1, 4 * p.2 + 2 * p.1 - 1)

lemma transformTube_left_inv2 : ∀ p, transformTubeInv (transformTube p) = p := by
  intro p; ext <;> simp [transformTube, transformTubeInv] <;> ring

lemma transformTube_right_inv2 : ∀ p, transformTube (transformTubeInv p) = p := by
  intro p; ext <;> simp [transformTube, transformTubeInv] <;> ring

lemma transformTube_lipschitz1 :
    LipschitzWith (1 : NNReal) (transformTube : (ℝ × ℝ) → (ℝ × ℝ)) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  let d := dist p q
  have hd_def : d = max (|p.1 - q.1|) (|p.2 - q.2|) := by
    simp [d, Prod.dist_eq, dist_eq_norm] <;> rfl
  have h11 : |p.1 - q.1| ≤ d := by rw [hd_def]; exact le_max_left _ _
  have h12 : |p.2 - q.2| ≤ d := by rw [hd_def]; exact le_max_right _ _
  have h1 : |(transformTube p).1 - (transformTube q).1| ≤ d := by
    have h_eq : (transformTube p).1 - (transformTube q).1 = (p.1 - q.1) / 2 := by
      simp [transformTube] <;> ring
    rw [h_eq]
    have h_abs_nonneg : 0 ≤ |p.1 - q.1| := abs_nonneg _
    have h : |(p.1 - q.1) / 2| ≤ |p.1 - q.1| := by
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      <;> linarith [h_abs_nonneg]
    exact h.trans h11
  have h2 : |(transformTube p).2 - (transformTube q).2| ≤ d := by
    have h_eq : (transformTube p).2 - (transformTube q).2 =
        ((p.2 - q.2) - (p.1 - q.1)) / 4 := by
      simp [transformTube] <;> ring
    rw [h_eq]
    have h : |((p.2 - q.2) - (p.1 - q.1)) / 4| ≤ d := by
      have h5 : |((p.2 - q.2) - (p.1 - q.1))| ≤ |p.2 - q.2| + |p.1 - q.1| := by
        exact abs_sub _ _
      have h6 : |((p.2 - q.2) - (p.1 - q.1)) / 4| =
          |((p.2 - q.2) - (p.1 - q.1))| / 4 := by
        rw [abs_div] <;> norm_num
      rw [h6]
      have h7 : 0 ≤ d := dist_nonneg
      linarith [h11, h12, h7]
    exact h
  have h3 : dist (transformTube p) (transformTube q) =
      max (|(transformTube p).1 - (transformTube q).1|)
          (|(transformTube p).2 - (transformTube q).2|) := by
    simp [Prod.dist_eq, dist_eq_norm] <;> rfl
  rw [h3]
  have h4 : max (|(transformTube p).1 - (transformTube q).1|)
      (|(transformTube p).2 - (transformTube q).2|) ≤ (1 : ℝ) * d := by
    simpa [one_mul] using max_le h1 h2
  exact h4

lemma transformTubeInv_lipschitz8 :
    LipschitzWith (8 : NNReal) (transformTubeInv : (ℝ × ℝ) → (ℝ × ℝ)) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  let d := dist p q
  have hd_def : d = max (|p.1 - q.1|) (|p.2 - q.2|) := by
    simp [d, Prod.dist_eq, dist_eq_norm] <;> rfl
  have h11 : |p.1 - q.1| ≤ d := by rw [hd_def]; exact le_max_left _ _
  have h12 : |p.2 - q.2| ≤ d := by rw [hd_def]; exact le_max_right _ _
  have h1 : |(transformTubeInv p).1 - (transformTubeInv q).1| ≤ 8 * d := by
    have h_eq : (transformTubeInv p).1 - (transformTubeInv q).1 = 2 * (p.1 - q.1) := by
      simp [transformTubeInv] <;> ring
    rw [h_eq]
    have h : |2 * (p.1 - q.1)| = 2 * |p.1 - q.1| := by
      rw [abs_mul] <;> norm_num
    rw [h]
    have h7 : 0 ≤ d := dist_nonneg
    linarith [h11, h7]
  have h2 : |(transformTubeInv p).2 - (transformTubeInv q).2| ≤ 8 * d := by
    have h_eq : (transformTubeInv p).2 - (transformTubeInv q).2 =
        4 * (p.2 - q.2) + 2 * (p.1 - q.1) := by
      simp [transformTubeInv] <;> ring
    rw [h_eq]
    have h : |4 * (p.2 - q.2) + 2 * (p.1 - q.1)| ≤
        4 * |p.2 - q.2| + 2 * |p.1 - q.1| := by
      calc |4 * (p.2 - q.2) + 2 * (p.1 - q.1)|
        ≤ |4 * (p.2 - q.2)| + |2 * (p.1 - q.1)| := by exact abs_add_le (4 * (p.2 - q.2)) (2 * (p.1 - q.1))
      _ = 4 * |p.2 - q.2| + 2 * |p.1 - q.1| := by
        simp [abs_mul] <;> ring
    have h7 : 0 ≤ d := dist_nonneg
    linarith [h11, h12, h7]
  have h3 : dist (transformTubeInv p) (transformTubeInv q) =
      max (|(transformTubeInv p).1 - (transformTubeInv q).1|)
          (|(transformTubeInv p).2 - (transformTubeInv q).2|) := by
    simp [Prod.dist_eq, dist_eq_norm] <;> rfl
  rw [h3]
  have h4 : max (|(transformTubeInv p).1 - (transformTubeInv q).1|)
      (|(transformTubeInv p).2 - (transformTubeInv q).2|) ≤ (8 : ℝ) * d := by
    simpa using max_le h1 h2
  exact h4

lemma lipschitz_image_covering' {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {K : NNReal} {f : X → Y} (hf : LipschitzWith K f)
    {ε : NNReal} {A : Set X} :
    Metric.externalCoveringNumber (K * ε) (f '' A) ≤
      Metric.externalCoveringNumber ε A :=
  externalCoveringNumber_image_lipschitz hf

/-- Coercion from ENat to ENNReal preserves multiplication by a natural number. -/
lemma enat_mul_to_ennreal (n : ℕ) (x : ENat) :
    ((n : ENat) * x : ENNReal) = (n : ENNReal) * (x : ENNReal) := by
  simpa using ENat.toENNReal_mul (n : ENat) x

lemma transformTube_Sset_preservation {δ s C : ℝ} (hδ : 0 < δ)
    {A : Set (ℝ × ℝ)} (hP : IsDeltaSSet δ s C A) (hs_le_one : s ≤ 1) :
    IsDeltaSSet δ s (C * 4096) (transformTube '' A) := by
  let f := transformTube
  let g := transformTubeInv
  have hf_lip : LipschitzWith (1 : NNReal) f := transformTube_lipschitz1
  have hg_lip : LipschitzWith (8 : NNReal) g := transformTubeInv_lipschitz8
  have hfg : ∀ p, f (g p) = p := transformTube_right_inv2
  have hgf : ∀ p, g (f p) = p := transformTube_left_inv2
  let B := f '' A
  have hB_nonempty : B.Nonempty := hP.1.image f
  have hC_pos : 0 < C := hP.2.2.1
  have hC4096_pos : 0 < C * 4096 := by positivity
  have hs_nonneg : 0 ≤ s := hP.2.2.2.1
  have hs_le_one' : s ≤ 1 := hs_le_one
  -- Helper: covering(A) ≤ 256 * covering(B)
  have h2δ_pos : 0 < (2 * δ) := by positivity
  have h8δ_pos : 0 < (8 * δ) := by positivity
  have h_scale1 : Metric.externalCoveringNumber δ.toNNReal A ≤
      (16 : ENat) * Metric.externalCoveringNumber (Real.toNNReal (2 * δ)) A :=
    covering_scale_2d hδ h2δ_pos (by linarith)
  have h_scale2 : Metric.externalCoveringNumber (Real.toNNReal (2 * δ)) A ≤
      (16 : ENat) * Metric.externalCoveringNumber (Real.toNNReal (8 * δ)) A :=
    covering_scale_2d h2δ_pos h8δ_pos (by linarith)
  have h_covA_le : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
      (256 : ENNReal) * (Metric.externalCoveringNumber (Real.toNNReal (8 * δ)) A : ENNReal) := by
    have h1' : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
        (16 : ENNReal) * (Metric.externalCoveringNumber (Real.toNNReal (2 * δ)) A : ENNReal) := by
      have h_tmp := ENat.toENNReal_le.mpr h_scale1
      simpa [enat_mul_to_ennreal] using h_tmp
    have h2' : (Metric.externalCoveringNumber (Real.toNNReal (2 * δ)) A : ENNReal) ≤
        (16 : ENNReal) * (Metric.externalCoveringNumber (Real.toNNReal (8 * δ)) A : ENNReal) := by
      have h_tmp := ENat.toENNReal_le.mpr h_scale2
      simpa [enat_mul_to_ennreal] using h_tmp
    calc (Metric.externalCoveringNumber δ.toNNReal A : ENNReal)
      ≤ (16 : ENNReal) * (Metric.externalCoveringNumber (Real.toNNReal (2 * δ)) A : ENNReal) := h1'
    _ ≤ (16 : ENNReal) * ((16 : ENNReal) * (Metric.externalCoveringNumber (Real.toNNReal (8 * δ)) A : ENNReal)) := by
      exact mul_le_mul_of_nonneg_left h2' (by norm_num)
    _ = (256 : ENNReal) * (Metric.externalCoveringNumber (Real.toNNReal (8 * δ)) A : ENNReal) := by ring
  have hA_eq : A = g '' B := by
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hz
      exact ⟨f z, ⟨z, hz, rfl⟩, by simp [hgf]⟩
    · rintro ⟨y', ⟨a, ha, rfl⟩, rfl⟩
      simpa [hgf] using ha
  have hg_cov : Metric.externalCoveringNumber (Real.toNNReal (8 * δ)) A ≤
      Metric.externalCoveringNumber δ.toNNReal B := by
    rw [hA_eq]
    have h : Metric.externalCoveringNumber ((8 : NNReal) * δ.toNNReal) (g '' B) ≤
        Metric.externalCoveringNumber δ.toNNReal B :=
      externalCoveringNumber_image_lipschitz hg_lip
    have h_eq : (8 : NNReal) * δ.toNNReal = (Real.toNNReal (8 * δ)) := by
      apply NNReal.coe_injective
      have h1 : ((8 : NNReal) * δ.toNNReal : ℝ) = 8 * δ := by
        simp [NNReal.coe_mul, hδ.le] <;> norm_cast
      have h2 : ((Real.toNNReal (8 * δ) : ℝ)) = 8 * δ := by
        have hpos : 0 ≤ 8 * δ := by positivity
        have h3 : (Real.toNNReal (8 * δ) : ℝ) = max (8 * δ) 0 := by
          simp [Real.toNNReal]
        rw [h3, max_eq_left hpos]
      exact h1.trans h2.symm
    simpa [h_eq] using h
  have h_covA_final : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
      (256 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) := by
    have hg_cov' : (Metric.externalCoveringNumber (Real.toNNReal (8 * δ)) A : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) := by
      exact ENat.toENNReal_le.mpr hg_cov
    calc (Metric.externalCoveringNumber δ.toNNReal A : ENNReal)
      ≤ (256 : ENNReal) * (Metric.externalCoveringNumber (Real.toNNReal (8 * δ)) A : ENNReal) := h_covA_le
    _ ≤ (256 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) := by
      exact mul_le_mul_of_nonneg_left hg_cov' (by norm_num)
  -- Helper: for y0 ∈ B, covering(B ∩ B(y0,r')) ≤ C * 2048 * (r')^s * covering(B)
  have h_bound2048 : ∀ (y0 : ℝ × ℝ), y0 ∈ B → ∀ (r' : ℝ), δ ≤ r' →
      (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall y0 r') : ENNReal) ≤
        ENNReal.ofReal (C * 2048) * (ENNReal.ofReal r') ^ s *
          (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) := by
    intro y0 hy0 r' hr'
    let x0 : ℝ × ℝ := g y0
    have hx0A : x0 ∈ A := by
      rcases hy0 with ⟨a, ha, rfl⟩
      have h : g (f a) = a := hgf a
      have hx : x0 = a := by simpa [x0] using h
      rw [hx]; exact ha
    have h_image_inter : B ∩ Metric.closedBall y0 r' ⊆ f '' (A ∩ Metric.closedBall x0 (8 * r')) := by
      intro z hz
      rcases hz.1 with ⟨a, ha, rfl⟩
      have h_dist : dist (f a) y0 ≤ r' := hz.2
      have h_dist2 : dist a x0 ≤ 8 * r' := by
        have h4 : dist (g (f a)) (g y0) ≤ (8 : ℝ) * dist (f a) y0 := hg_lip.dist_le_mul (f a) y0
        have h5 : g (f a) = a := hgf a
        rw [h5] at h4
        exact h4.trans (mul_le_mul_of_nonneg_left h_dist (by norm_num))
      exact ⟨a, ⟨ha, h_dist2⟩, rfl⟩
    have h1 : (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall y0 r') : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x0 (8 * r')) : ENNReal) := by
      have h_cov1 : Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall y0 r') ≤
          Metric.externalCoveringNumber δ.toNNReal (f '' (A ∩ Metric.closedBall x0 (8 * r'))) :=
        Metric.externalCoveringNumber_mono_set h_image_inter
      have h_cov2 : Metric.externalCoveringNumber ((1 : NNReal) * δ.toNNReal)
          (f '' (A ∩ Metric.closedBall x0 (8 * r'))) ≤
          Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x0 (8 * r')) :=
        externalCoveringNumber_image_lipschitz hf_lip
      have h_eq : (1 : NNReal) * δ.toNNReal = δ.toNNReal := by simp
      rw [h_eq] at h_cov2
      exact le_trans (ENat.toENNReal_le.mpr h_cov1) (ENat.toENNReal_le.mpr h_cov2)
    have h8r'_ge_δ : δ ≤ 8 * r' := by linarith
    have h2 : (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x0 (8 * r')) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (8 * r')) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) :=
      hP.2.2.2.2 x0 (8 * r') h8r'_ge_δ
    have h_pow : (ENNReal.ofReal (8 * r')) ^ s ≤ ENNReal.ofReal 8 * (ENNReal.ofReal r') ^ s := by
      have h_rpos : 0 ≤ r' := by linarith
      have h1 : (ENNReal.ofReal (8 * r')) ^ s = ENNReal.ofReal ((8 * r') ^ s) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) hs_nonneg]
      rw [h1]
      have h2 : (8 * r') ^ s = (8 : ℝ) ^ s * (r') ^ s := Real.mul_rpow (by norm_num) h_rpos
      rw [h2]
      have h3 : ENNReal.ofReal ((8 : ℝ) ^ s * (r') ^ s) =
          ENNReal.ofReal ((8 : ℝ) ^ s) * ENNReal.ofReal ((r') ^ s) := by
        rw [ENNReal.ofReal_mul (by positivity)]
      rw [h3]
      have h4 : ENNReal.ofReal ((r') ^ s) = (ENNReal.ofReal r') ^ s := by
        rw [ENNReal.ofReal_rpow_of_nonneg h_rpos hs_nonneg]
      rw [h4]
      have h5 : (8 : ℝ) ^ s ≤ 8 := by
        have h6 : (8 : ℝ) ^ s ≤ (8 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs_le_one'
        simpa using h6
      have h7 : ENNReal.ofReal ((8 : ℝ) ^ s) ≤ ENNReal.ofReal (8 : ℝ) := by
        have hnonneg : 0 ≤ (8 : ℝ) := by norm_num
        exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mpr h5
      gcongr
    calc (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall y0 r') : ENNReal)
      ≤ (Metric.externalCoveringNumber δ.toNNReal (A ∩ Metric.closedBall x0 (8 * r')) : ENNReal) := h1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (8 * r')) ^ s * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := h2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal 8 * (ENNReal.ofReal r') ^ s) * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
      gcongr
    _ ≤ ENNReal.ofReal (C * 2048) * (ENNReal.ofReal r') ^ s * (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) := by
      set covA := (Metric.externalCoveringNumber δ.toNNReal A : ENNReal)
      set covB := (Metric.externalCoveringNumber δ.toNNReal B : ENNReal)
      have h_lhs_eq : ENNReal.ofReal C * (ENNReal.ofReal 8 * (ENNReal.ofReal r') ^ s) * covA
          = ENNReal.ofReal (C * 8) * (ENNReal.ofReal r') ^ s * covA := by
        have h1 : ENNReal.ofReal C * ENNReal.ofReal 8 = ENNReal.ofReal (C * 8) := by
          rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
        have h2 : ENNReal.ofReal C * (ENNReal.ofReal 8 * (ENNReal.ofReal r') ^ s) * covA
            = (ENNReal.ofReal C * ENNReal.ofReal 8) * (ENNReal.ofReal r') ^ s * covA := by ring
        rw [h2, h1]
      rw [h_lhs_eq]
      have h11 : ENNReal.ofReal (C * 8) * (ENNReal.ofReal r') ^ s * covA
          ≤ ENNReal.ofReal (C * 8) * (ENNReal.ofReal r') ^ s * ((256 : ENNReal) * covB) := by
        gcongr
        <;> exact h_covA_final
      have h12 : ENNReal.ofReal (C * 8) * (ENNReal.ofReal r') ^ s * ((256 : ENNReal) * covB) =
          ENNReal.ofReal (C * 2048) * (ENNReal.ofReal r') ^ s * covB := by
        have h13 : ENNReal.ofReal (C * 8) * (256 : ENNReal) = ENNReal.ofReal (C * 2048) := by
          have h14 : (256 : ENNReal) = ENNReal.ofReal (256 : ℝ) := by norm_cast
          rw [h14]
          have h_pos_C8 : 0 ≤ C * 8 := by positivity
          have h15 : ENNReal.ofReal (C * 8) * ENNReal.ofReal (256 : ℝ) = ENNReal.ofReal ((C * 8) * (256 : ℝ)) :=
            (ENNReal.ofReal_mul (show 0 ≤ C * 8 by positivity)).symm
          rw [h15]
          have h16 : (C * 8) * (256 : ℝ) = C * 2048 := by ring
          rw [h16]
        have h17 : ENNReal.ofReal (C * 8) * (ENNReal.ofReal r') ^ s * ((256 : ENNReal) * covB) =
            (ENNReal.ofReal (C * 8) * (256 : ENNReal)) * (ENNReal.ofReal r') ^ s * covB := by ring
        rw [h17, h13] <;> ring
      exact h12 ▸ h11
  have h_main_ineq : ∀ (y : ℝ × ℝ) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall y r) : ENNReal) ≤
        ENNReal.ofReal (C * 4096) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) := by
    intro y r hr
    by_cases hyB : y ∈ B
    · have h := h_bound2048 y hyB r hr
      exact le_trans h (by
        have h2048 : ENNReal.ofReal (C * 2048) ≤ ENNReal.ofReal (C * 4096) := by
          have hnonneg : 0 ≤ C * 4096 := by positivity
          exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mpr (by linarith [hC_pos])
        gcongr)
    · by_cases h_empty : (B ∩ Metric.closedBall y r).Nonempty
      · rcases h_empty with ⟨y0, hy0⟩
        have hy0B : y0 ∈ B := hy0.1
        have hdist : dist y y0 ≤ r := by
          have h : dist y0 y ≤ r := hy0.2
          rw [dist_comm] at h
          exact h
        have h_sub : B ∩ Metric.closedBall y r ⊆ B ∩ Metric.closedBall y0 (2 * r) := by
          intro p hp
          have h1 : p ∈ B := hp.1
          have h2 : dist p y ≤ r := hp.2
          have h3 : dist p y0 ≤ dist p y + dist y y0 := dist_triangle p y y0
          have h4 : dist p y0 ≤ 2 * r := by linarith
          exact ⟨h1, h4⟩
        have h_cov_le : (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall y r) : ENNReal) ≤
            (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall y0 (2 * r)) : ENNReal) := by
          exact_mod_cast Metric.externalCoveringNumber_mono_set h_sub
        have h2r_ge_δ : δ ≤ 2 * r := by linarith
        have h := h_bound2048 y0 hy0B (2 * r) h2r_ge_δ
        have h_pow2 : (ENNReal.ofReal (2 * r)) ^ s ≤ ENNReal.ofReal 2 * (ENNReal.ofReal r) ^ s := by
          have h_rpos : 0 ≤ r := by linarith
          have h1 : (ENNReal.ofReal (2 * r)) ^ s = ENNReal.ofReal ((2 * r) ^ s) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) hs_nonneg]
          rw [h1]
          have h2 : (2 * r) ^ s = (2 : ℝ) ^ s * r ^ s := Real.mul_rpow (by norm_num) h_rpos
          rw [h2]
          have h3 : ENNReal.ofReal ((2 : ℝ) ^ s * r ^ s) =
              ENNReal.ofReal ((2 : ℝ) ^ s) * ENNReal.ofReal (r ^ s) := by
            rw [ENNReal.ofReal_mul (by positivity)]
          rw [h3]
          have h4 : ENNReal.ofReal (r ^ s) = (ENNReal.ofReal r) ^ s := by
            rw [ENNReal.ofReal_rpow_of_nonneg h_rpos hs_nonneg]
          rw [h4]
          have h5 : (2 : ℝ) ^ s ≤ 2 := by
            have h6 : (2 : ℝ) ^ s ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs_le_one'
            simpa using h6
          have h7 : ENNReal.ofReal ((2 : ℝ) ^ s) ≤ ENNReal.ofReal (2 : ℝ) := ENNReal.ofReal_le_ofReal h5
          gcongr
        calc (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall y r) : ENNReal)
          ≤ (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall y0 (2 * r)) : ENNReal) := h_cov_le
        _ ≤ ENNReal.ofReal (C * 2048) * (ENNReal.ofReal (2 * r)) ^ s * (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) := h
        _ ≤ ENNReal.ofReal (C * 2048) * (ENNReal.ofReal 2 * (ENNReal.ofReal r) ^ s) * (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) := by gcongr
        _ = ENNReal.ofReal (C * 4096) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) := by
          have h9 : ENNReal.ofReal (C * 2048) * (ENNReal.ofReal 2 * (ENNReal.ofReal r) ^ s) * (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) =
              (ENNReal.ofReal (C * 2048) * ENNReal.ofReal 2) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) := by ring
          rw [h9]
          have h10 : ENNReal.ofReal (C * 2048) * ENNReal.ofReal 2 = ENNReal.ofReal (C * 4096) := by
            rw [← ENNReal.ofReal_mul (by positivity)] <;> ring_nf
          rw [h10] <;> ring
      · have h_eq_empty : B ∩ Metric.closedBall y r = ∅ := by
          simpa [Set.not_nonempty_iff_eq_empty] using h_empty
        rw [h_eq_empty]
        simp
  exact ⟨hB_nonempty, hδ, hC4096_pos, hs_nonneg, h_main_ineq⟩
/-! ### Helper: Injectivity of canonical cube map -/

lemma canonicalCube_injective (δ : ℝ) :
    Set.InjOn (productLikeAppendixDyadicTubeCanonicalParameterCube δ)
      (appendixDyadicTubes δ) := by
  intro T1 hT1 T2 hT2 h_eq
  have h1 : appendixDualOfParameterSet
      (productLikeAppendixDyadicTubeCanonicalParameterCube δ T1) = T1 := by
    simp [productLikeAppendixDyadicTubeCanonicalParameterCube, hT1]
    <;> exact (Classical.choose_spec hT1).2
  have h2 : appendixDualOfParameterSet
      (productLikeAppendixDyadicTubeCanonicalParameterCube δ T2) = T2 := by
    simp [productLikeAppendixDyadicTubeCanonicalParameterCube, hT2]
    <;> exact (Classical.choose_spec hT2).2
  have h3 : appendixDualOfParameterSet
      (productLikeAppendixDyadicTubeCanonicalParameterCube δ T1) =
      appendixDualOfParameterSet
      (productLikeAppendixDyadicTubeCanonicalParameterCube δ T2) := by
    rw [h_eq]
  exact Eq.trans h1.symm (Eq.trans h3 h2)

/-! ### Helper: Pigeonhole principles -/

lemma finset_pigeonhole {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    {s : Finset α} {f : α → β} (hk : 0 < Fintype.card β) :
    ∃ (b : β), s.card ≤ Fintype.card β * (s.filter (fun a => f a = b)).card := by
  by_cases h : s.card = 0
  · have hne : Nonempty β := Fintype.card_pos_iff.mp hk
    exact ⟨Classical.arbitrary β, by simp [h]⟩
  · have hpos : 0 < s.card := Nat.pos_of_ne_zero h
    by_contra h'
    push Not at h'
    have h1 : ∀ b : β, Fintype.card β * (s.filter (fun a => f a = b)).card < s.card := h'
    have h2 : ∀ b : β, (s.filter (fun a => f a = b)).card ≤ (s.card - 1) / Fintype.card β := by
      intro b
      have h3 : Fintype.card β * (s.filter (fun a => f a = b)).card + 1 ≤ s.card :=
        Nat.lt_iff_add_one_le.mp (h1 b)
      have h4 : Fintype.card β * (s.filter (fun a => f a = b)).card ≤ s.card - 1 := by omega
      have h5 : (s.filter (fun a => f a = b)).card * Fintype.card β ≤ s.card - 1 := by
        rw [mul_comm] <;> exact h4
      exact (Nat.le_div_iff_mul_le hk).mpr h5
    have h4 : ∑ b : β, (s.filter (fun a => f a = b)).card ≤
        Fintype.card β * ((s.card - 1) / Fintype.card β) := by
      calc
        ∑ b : β, (s.filter (fun a => f a = b)).card
          ≤ ∑ b : β, ((s.card - 1) / Fintype.card β) :=
            Finset.sum_le_sum (fun b _ => h2 b)
        _ = Fintype.card β * ((s.card - 1) / Fintype.card β) := by
          simp [Finset.sum_const] <;> ring
    have h5 : Fintype.card β * ((s.card - 1) / Fintype.card β) ≤ s.card - 1 :=
      Nat.mul_div_le _ _
    have h_disj : ∀ (b1 : β), b1 ∈ (Finset.univ : Finset β) →
        ∀ (b2 : β), b2 ∈ (Finset.univ : Finset β) → b1 ≠ b2 →
          Disjoint (s.filter (fun a => f a = b1)) (s.filter (fun a => f a = b2)) := by
      intro b1 _ b2 _ hne
      simp [Finset.disjoint_left] <;> intro x hx1 hx2 <;> simp_all
    have h_card : (Finset.biUnion (Finset.univ : Finset β) (fun b => s.filter (fun a => f a = b))).card =
        ∑ b : β, (s.filter (fun a => f a = b)).card := Finset.card_biUnion h_disj
    have h7 : s = Finset.biUnion (Finset.univ : Finset β) (fun b => s.filter (fun a => f a = b)) := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
      constructor
      · intro hx
        exact ⟨f x, hx, rfl⟩
      · rintro ⟨b, hx, _⟩
        exact hx
    have h6 : ∑ b : β, (s.filter (fun a => f a = b)).card = s.card := by
      calc
        ∑ b : β, (s.filter (fun a => f a = b)).card
          = (Finset.biUnion (Finset.univ : Finset β) (fun b => s.filter (fun a => f a = b))).card := h_card.symm
        _ = s.card := by exact congr_arg Finset.card h7.symm
    rw [h6] at h4
    omega

lemma set_pigeonhole_9 {α : Type*} {S : Set α} {f : α → Fin 3 × Fin 3} :
    ∃ (r : Fin 3 × Fin 3), S.encard ≤ 9 * {a ∈ S | f a = r}.encard := by
  classical
  by_cases hS : S.Finite
  · let s := hS.toFinset
    have h_main : ∃ (r : Fin 3 × Fin 3),
        s.card ≤ 9 * (s.filter (fun a => f a = r)).card :=
      finset_pigeonhole (β := Fin 3 × Fin 3) (by decide)
    rcases h_main with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    have h_eq1 : S.encard = ↑s.card := by exact Set.Finite.encard_eq_coe_toFinset_card hS
    have h_eq2 : {a ∈ S | f a = r}.encard = ↑(s.filter (fun a => f a = r)).card := by
      have h_set : {a ∈ S | f a = r} = (s.filter (fun a => f a = r) : Set α) := by
        ext x
        simp [s, Set.Finite.mem_toFinset] <;> tauto
      rw [h_set]
      exact Set.encard_coe_eq_coe_finsetCard ({a ∈ s | f a = r})
    rw [h_eq1, h_eq2]
    exact_mod_cast hr
  · have hS' : Set.Infinite S := by exact Set.not_finite.mp hS
    have h_exists : ∃ (r : Fin 3 × Fin 3), Set.Infinite {a ∈ S | f a = r} := by
      by_contra h
      push Not at h
      have h_fin : ∀ r : Fin 3 × Fin 3, ({a ∈ S | f a = r} : Set α).Finite :=
        fun r => by exact Set.finite_coe_iff.mp (h r)
      have h_union : S = ⋃ r : Fin 3 × Fin 3, {a ∈ S | f a = r} := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        constructor
        · intro hx
          exact ⟨f x, hx, rfl⟩
        · rintro ⟨r, hx, _⟩
          exact hx
      have h_univ : (⋃ r : Fin 3 × Fin 3, {a ∈ S | f a = r}) =
          ⋃ r ∈ (Set.univ : Set (Fin 3 × Fin 3)), {a ∈ S | f a = r} := by
        ext y; simp
      have h_finite : (⋃ r : Fin 3 × Fin 3, {a ∈ S | f a = r}).Finite := by
        rw [h_univ]
        exact Set.Finite.biUnion (Set.toFinite (Set.univ : Set (Fin 3 × Fin 3)))
          fun r _ => h_fin r
      rw [h_union] at hS'
      exact hS' h_finite
    rcases h_exists with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    have h_top : {a ∈ S | f a = r}.encard = ⊤ := by
      exact Set.encard_eq_top_iff.mpr hr
    have hS_top : S.encard = ⊤ := by exact Set.encard_eq_top_iff.mpr hS
    have h9 : (9 : ENat) * {a ∈ S | f a = r}.encard = ⊤ := by
      rw [h_top] <;> simp
    exact le_top.trans_eq h9.symm

/-! ### Helper: Cube centers and separation -/

def cubeCenter (δ : ℝ) (k : Fin 2 → ℤ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i : Fin 2 => δ * ((k i : ℝ) + 1 / 2))

lemma cubeCenter_mem_cube (δ : ℝ) (hδ : 0 < δ) (k : Fin 2 → ℤ) :
    cubeCenter δ k ∈ dyadicCube δ k := by
  intro i
  simp [cubeCenter, dyadicCube, Set.mem_Ico] <;> constructor <;> linarith

lemma int_emod3_separation (a b : ℤ) (hmod : a % 3 = b % 3) (hne : a ≠ b) :
    |a - b| ≥ 3 := by
  have hdiv : (3 : ℤ) ∣ (a - b) := by omega
  rcases hdiv with ⟨k, hk⟩
  have hk_ne_zero : k ≠ 0 := by
    intro h
    rw [h, mul_zero] at hk
    omega
  have h_abs_k : |k| ≥ 1 := Int.one_le_abs hk_ne_zero
  have h_abs : |a - b| = 3 * |k| := by
    rw [hk] <;> rw [abs_mul] <;> simp
  rw [h_abs] <;> omega

lemma cubeCenter_separation (δ : ℝ) (hδ : 0 < δ)
    (k1 k2 : Fin 2 → ℤ) (hne : k1 ≠ k2)
    (hmod0 : (k1 0) % 3 = (k2 0) % 3)
    (hmod1 : (k1 1) % 3 = (k2 1) % 3) :
    dist (cubeCenter δ k1) (cubeCenter δ k2) > 2 * δ := by
  have h_coord : ∃ i : Fin 2, k1 i ≠ k2 i := by
    by_contra h
    push Not at h
    have h_eq : k1 = k2 := by funext i; exact h i
    exact hne h_eq
  rcases h_coord with ⟨i, hne_i⟩
  have hmod_i : (k1 i) % 3 = (k2 i) % 3 := by fin_cases i <;> tauto
  have h_diff3 : |(k1 i : ℝ) - (k2 i : ℝ)| ≥ 3 :=
    by exact_mod_cast int_emod3_separation (k1 i) (k2 i) hmod_i hne_i
  have h_coord_diff : |(cubeCenter δ k1 i) - (cubeCenter δ k2 i)| ≥ 3 * δ := by
    have h9 : (cubeCenter δ k1 i) - (cubeCenter δ k2 i) = δ * ((k1 i : ℝ) - (k2 i : ℝ)) := by
      simp [cubeCenter] <;> ring
    rw [h9]
    have h10 : |δ * ((k1 i : ℝ) - (k2 i : ℝ))| = δ * |(k1 i : ℝ) - (k2 i : ℝ)| := by
      rw [abs_mul, abs_of_pos hδ]
    rw [h10]
    have h11 : δ * |(k1 i : ℝ) - (k2 i : ℝ)| ≥ δ * 3 := by gcongr
    linarith
  let x := cubeCenter δ k1 - cubeCenter δ k2
  have h_dist_eq : dist (cubeCenter δ k1) (cubeCenter δ k2) = ‖x‖ := by rfl
  have h_norm_sq : ‖x‖ ^ 2 = ∑ j : Fin 2, |x j| ^ 2 := EuclideanSpace.norm_sq_eq x
  have h_goal : dist (cubeCenter δ k1) (cubeCenter δ k2) ^ 2 ≥
      |(cubeCenter δ k1 i) - (cubeCenter δ k2 i)| ^ 2 := by
    rw [h_dist_eq, h_norm_sq]
    have h2 : |x i| ^ 2 ≤ ∑ j : Fin 2, |x j| ^ 2 := by
      apply Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i)
    exact h2
  have h_final : dist (cubeCenter δ k1) (cubeCenter δ k2) ≥ 3 * δ := by
    have h_sq1 : dist (cubeCenter δ k1) (cubeCenter δ k2) ^ 2 ≥ (3 * δ) ^ 2 := by
      calc
        dist (cubeCenter δ k1) (cubeCenter δ k2) ^ 2
          ≥ |(cubeCenter δ k1 i) - (cubeCenter δ k2 i)| ^ 2 := h_goal
        _ ≥ (3 * δ) ^ 2 := by
          have h13 : |(cubeCenter δ k1 i) - (cubeCenter δ k2 i)| ≥ 3 * δ := h_coord_diff
          gcongr
    have h14 : 0 ≤ dist (cubeCenter δ k1) (cubeCenter δ k2) := dist_nonneg
    nlinarith
  linarith

/-- Reverse covering bound: covering number of parameter set union
is at least encard(tube union) / 9. Proof via packing: select a mod-3
residue class of cube indices (≥ N/9 tubes), whose centers are 3δ-separated
(hence 2δ-separated), and apply packingNumber ≤ externalCoveringNumber. -/
lemma tubeUnion_covering_lower {δ : ℝ} (hδ : 0 < δ)
    {ι : Type*} {S : Set ι}
    {𝒯 : ι → Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (h : ∀ i ∈ S, 𝒯 i ⊆ appendixDyadicTubes δ) :
    (Metric.externalCoveringNumber δ.toNNReal
       (⋃ i ∈ S, productLikeAppendixDyadicTubeParameterSet δ (𝒯 i)) : ENNReal) ≥
      ENat.toENNReal (⋃ i ∈ S, 𝒯 i).encard / 9 := by
  let 𝒯_union : Set (Set (EuclideanSpace ℝ (Fin 2))) := ⋃ i ∈ S, 𝒯 i
  have h_appendix : ∀ T ∈ 𝒯_union, T ∈ appendixDyadicTubes δ := by
    intro T hT
    rcases Set.mem_iUnion₂.mp hT with ⟨i, hi, hTi⟩
    exact h i hi hTi
  let k : (T : Set (EuclideanSpace ℝ (Fin 2))) → T ∈ 𝒯_union → (Fin 2 → ℤ) :=
    fun T hT => Classical.choose (canonicalCube_is_dyadic δ T (h_appendix T hT))
  have hk_eq : ∀ (T) (hT : T ∈ 𝒯_union),
      productLikeAppendixDyadicTubeCanonicalParameterCube δ T = dyadicCube δ (k T hT) := by
    intro T hT
    exact Classical.choose_spec (canonicalCube_is_dyadic δ T (h_appendix T hT))
  have h_k_inj : ∀ (T1 T2) (hT1 : T1 ∈ 𝒯_union) (hT2 : T2 ∈ 𝒯_union),
      k T1 hT1 = k T2 hT2 → T1 = T2 := by
    intro T1 T2 hT1 hT2 h_eq
    have h_cube_eq : productLikeAppendixDyadicTubeCanonicalParameterCube δ T1 =
        productLikeAppendixDyadicTubeCanonicalParameterCube δ T2 := by
      rw [hk_eq T1 hT1, hk_eq T2 hT2, h_eq]
    exact canonicalCube_injective δ (h_appendix T1 hT1) (h_appendix T2 hT2) h_cube_eq
  let residue (k : Fin 2 → ℤ) : Fin 3 × Fin 3 :=
    (⟨(k 0 % 3).toNat, by omega⟩, ⟨(k 1 % 3).toNat, by omega⟩)
  classical
  let g : {T // T ∈ 𝒯_union} → Fin 3 × Fin 3 :=
    fun xT => residue (k xT.val xT.property)
  let S_set : Set {T // T ∈ 𝒯_union} := Set.univ
  have h_encard_eq : S_set.encard = 𝒯_union.encard := by
    simp [S_set] <;> exact Set.encard_subtype_eq 𝒯_union
  have h_pigeon := set_pigeonhole_9 (S := S_set) (f := g)
  rcases h_pigeon with ⟨r, hr⟩
  let 𝒯_r_sub : Set {T // T ∈ 𝒯_union} := {xT ∈ S_set | g xT = r}
  have h_encard_r : 𝒯_union.encard ≤ 9 * 𝒯_r_sub.encard := by
    simpa [h_encard_eq] using hr
  let center_map : {T // T ∈ 𝒯_union} → EuclideanSpace ℝ (Fin 2) :=
    fun xT => cubeCenter δ (k xT.val xT.property)
  let P : Set (EuclideanSpace ℝ (Fin 2)) := center_map '' 𝒯_r_sub
  have h_param_union_eq : productLikeAppendixDyadicTubeParameterSet δ 𝒯_union =
      (⋃ i ∈ S, productLikeAppendixDyadicTubeParameterSet δ (𝒯 i)) := by
    simp [productLikeAppendixDyadicTubeParameterSet, 𝒯_union, Set.sUnion_image]
    <;> ext y <;> simp [Set.mem_iUnion₂] <;> tauto
  have hP_subset : P ⊆ (⋃ i ∈ S, productLikeAppendixDyadicTubeParameterSet δ (𝒯 i)) := by
    intro p hp
    rcases hp with ⟨xT, hxT, rfl⟩
    let T := xT.val
    let hT := xT.property
    have h_center_in_cube : cubeCenter δ (k T hT) ∈
        productLikeAppendixDyadicTubeCanonicalParameterCube δ T := by
      rw [hk_eq T hT]
      exact cubeCenter_mem_cube δ hδ (k T hT)
    have h_cube_in_param : productLikeAppendixDyadicTubeCanonicalParameterCube δ T ⊆
        productLikeAppendixDyadicTubeParameterSet δ 𝒯_union := by
      apply Set.subset_sUnion_of_mem
      exact Set.mem_image_of_mem _ hT
    have h_in_param : cubeCenter δ (k T hT) ∈ productLikeAppendixDyadicTubeParameterSet δ 𝒯_union :=
      h_cube_in_param h_center_in_cube
    rw [h_param_union_eq] at h_in_param
    exact h_in_param
  have h_inj : Set.InjOn center_map 𝒯_r_sub := by
    intro xT1 hxT1 xT2 hxT2 h_eq
    have h_k_eq : k xT1.val xT1.property = k xT2.val xT2.property := by
      have h_eq2 : cubeCenter δ (k xT1.val xT1.property) = cubeCenter δ (k xT2.val xT2.property) := h_eq
      have h_eq3 : (fun i : Fin 2 => δ * ((k xT1.val xT1.property i : ℝ) + 1 / 2)) =
          (fun i : Fin 2 => δ * ((k xT2.val xT2.property i : ℝ) + 1 / 2)) := by
        simpa [cubeCenter] using h_eq2
      have h_eq4 : k xT1.val xT1.property = k xT2.val xT2.property := by
        funext i
        have h5 := congr_fun h_eq3 i
        apply_fun (fun y : ℝ => y / δ) at h5
        <;> simpa [hδ.ne'] using h5
      exact h_eq4
    have h_T_eq : xT1.val = xT2.val := h_k_inj xT1.val xT2.val xT1.property xT2.property h_k_eq
    exact Subtype.ext h_T_eq
  have hP_encard : P.encard = 𝒯_r_sub.encard := by
    have h : (center_map '' 𝒯_r_sub).encard = 𝒯_r_sub.encard := Set.InjOn.encard_image h_inj
    have hP : P = center_map '' 𝒯_r_sub := by rfl
    rw [hP]
    exact h
  have h_sep : Metric.IsSeparated (2 * δ.toNNReal) P := by
    intro p1 hp1 p2 hp2 hne
    rcases hp1 with ⟨xT1, hxT1, rfl⟩
    rcases hp2 with ⟨xT2, hxT2, rfl⟩
    have h_xT_ne : xT1 ≠ xT2 := by
      intro h
      rw [h] at hne
      exact hne rfl
    have h_k_ne : k xT1.val xT1.property ≠ k xT2.val xT2.property := by
      intro h
      have h_T_eq : xT1.val = xT2.val :=
        h_k_inj xT1.val xT2.val xT1.property xT2.property h
      exact h_xT_ne (Subtype.ext h_T_eq)
    have h_g_eq : g xT1 = g xT2 := by rw [hxT1.2, hxT2.2]
    have hmod0 : (k xT1.val xT1.property 0) % 3 = (k xT2.val xT2.property 0) % 3 := by
      have h : (g xT1).1 = (g xT2).1 := by rw [h_g_eq]
      have h' : ((k xT1.val xT1.property 0) % 3).toNat =
          ((k xT2.val xT2.property 0) % 3).toNat := by
        simpa [g, residue, Fin.ext_iff] using h
      have h_nonneg1 : 0 ≤ (k xT1.val xT1.property 0) % 3 := Int.emod_nonneg _ (by norm_num)
      have h_nonneg2 : 0 ≤ (k xT2.val xT2.property 0) % 3 := Int.emod_nonneg _ (by norm_num)
      have h4 : ((k xT1.val xT1.property 0) % 3 : ℤ) = ↑(((k xT1.val xT1.property 0) % 3).toNat) := by
        rw [Int.toNat_of_nonneg h_nonneg1]
      have h5 : ((k xT2.val xT2.property 0) % 3 : ℤ) = ↑(((k xT2.val xT2.property 0) % 3).toNat) := by
        rw [Int.toNat_of_nonneg h_nonneg2]
      rw [h4, h5, h']
    have hmod1 : (k xT1.val xT1.property 1) % 3 = (k xT2.val xT2.property 1) % 3 := by
      have h : (g xT1).2 = (g xT2).2 := by rw [h_g_eq]
      have h' : ((k xT1.val xT1.property 1) % 3).toNat =
          ((k xT2.val xT2.property 1) % 3).toNat := by
        simpa [g, residue, Fin.ext_iff] using h
      have h_nonneg1 : 0 ≤ (k xT1.val xT1.property 1) % 3 := Int.emod_nonneg _ (by norm_num)
      have h_nonneg2 : 0 ≤ (k xT2.val xT2.property 1) % 3 := Int.emod_nonneg _ (by norm_num)
      have h4 : ((k xT1.val xT1.property 1) % 3 : ℤ) = ↑(((k xT1.val xT1.property 1) % 3).toNat) := by
        rw [Int.toNat_of_nonneg h_nonneg1]
      have h5 : ((k xT2.val xT2.property 1) % 3 : ℤ) = ↑(((k xT2.val xT2.property 1) % 3).toNat) := by
        rw [Int.toNat_of_nonneg h_nonneg2]
      rw [h4, h5, h']
    have h_dist : dist (center_map xT1) (center_map xT2) > 2 * δ :=
      cubeCenter_separation δ hδ
        (k xT1.val xT1.property) (k xT2.val xT2.property) h_k_ne hmod0 hmod1
    have h_edist : (2 * δ.toNNReal : ENNReal) <
        edist (center_map xT1) (center_map xT2) := by
      have h9 : edist (center_map xT1) (center_map xT2) =
          ENNReal.ofReal (dist (center_map xT1) (center_map xT2)) := by exact edist_dist (center_map xT1) (center_map xT2)
      rw [h9]
      have h11 : (2 * δ.toNNReal : ENNReal) = ENNReal.ofReal (2 * δ) := by
        simp [NNReal.coe_mul] <;> norm_cast
      rw [h11]
      have h12 : ENNReal.ofReal (2 * δ) < ENNReal.ofReal (dist (center_map xT1) (center_map xT2)) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
        exact h_dist
      exact h12
    exact h_edist
  have h_pack : P.encard ≤ Metric.packingNumber (2 * δ.toNNReal)
      (⋃ i ∈ S, productLikeAppendixDyadicTubeParameterSet δ (𝒯 i)) :=
    Metric.IsSeparated.encard_le_packingNumber hP_subset h_sep
  have h_main : Metric.packingNumber (2 * δ.toNNReal)
      (⋃ i ∈ S, productLikeAppendixDyadicTubeParameterSet δ (𝒯 i)) ≤
      Metric.externalCoveringNumber δ.toNNReal
        (⋃ i ∈ S, productLikeAppendixDyadicTubeParameterSet δ (𝒯 i)) :=
    Metric.packingNumber_two_mul_le_externalCoveringNumber δ.toNNReal _
  have h_final : P.encard ≤ Metric.externalCoveringNumber δ.toNNReal
      (⋃ i ∈ S, productLikeAppendixDyadicTubeParameterSet δ (𝒯 i)) :=
    le_trans h_pack h_main
  rw [hP_encard] at h_final
  have h9 : 𝒯_union.encard ≤ 9 * 𝒯_r_sub.encard := h_encard_r
  have h10 : ENat.toENNReal 𝒯_union.encard ≤
      (9 : ENNReal) * ENat.toENNReal 𝒯_r_sub.encard := by exact_mod_cast h9
  have h11 : ENat.toENNReal 𝒯_r_sub.encard ≤
      (Metric.externalCoveringNumber δ.toNNReal
        (⋃ i ∈ S, productLikeAppendixDyadicTubeParameterSet δ (𝒯 i)) : ENNReal) := by
    exact_mod_cast h_final
  have h12 : ENat.toENNReal 𝒯_union.encard / 9 ≤
      (Metric.externalCoveringNumber δ.toNNReal
        (⋃ i ∈ S, productLikeAppendixDyadicTubeParameterSet δ (𝒯 i)) : ENNReal) := by
    calc
      ENat.toENNReal 𝒯_union.encard / 9
        ≤ ((9 : ENNReal) * ENat.toENNReal 𝒯_r_sub.encard) / 9 := by gcongr
      _ = ENat.toENNReal 𝒯_r_sub.encard := by
        have h_comm : (9 : ENNReal) * ENat.toENNReal 𝒯_r_sub.encard =
            ENat.toENNReal 𝒯_r_sub.encard * (9 : ENNReal) := by ring
        rw [h_comm]
        exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
      _ ≤ _ := h11
  simpa [𝒯_union] using h12

/-! ### Helper: IsDeltaSCSet weakening -/

/-- If P is a (δ,s,C)-SC-set and C ≤ C', then P is a (δ,s,C')-SC-set. -/
lemma IsDeltaSCSet.weaken_constant {d : ℕ} {δ s C C' : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    (h : IsDeltaSCSet δ s C P) (hC : C ≤ C') :
    IsDeltaSCSet δ s C' P := by
  rcases h with ⟨hBdd, hNE, hd, hdyadic, hδ_pos, hs, hs_le, hC_pos, hmain⟩
  have hC'_pos : 0 < C' := by linarith
  refine ⟨hBdd, hNE, hd, hdyadic, hδ_pos, hs, hs_le, hC'_pos, ?_⟩
  intro r Q hr hQ hδr hr1
  have h1 := hmain hr hQ hδr hr1
  have h2 : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal hC
  calc
    ENat.toENNReal (dyadicCoveringNumber (d := d) δ (P ∩ Q))
      ≤ ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber (d := d) δ P) *
          ENNReal.ofReal (r ^ s) := h1
    _ ≤ ENNReal.ofReal C' * ENat.toENNReal (dyadicCoveringNumber (d := d) δ P) *
          ENNReal.ofReal (r ^ s) := by gcongr

/-- Weaken constant in IsProductLikeRealDeltaSCSet. -/
lemma IsProductLikeRealDeltaSCSet.weaken_constant {δ s C C' : ℝ} {A : Set ℝ}
    (h : IsProductLikeRealDeltaSCSet δ s C A) (hC : C ≤ C') :
    IsProductLikeRealDeltaSCSet δ s C' A :=
  IsDeltaSCSet.weaken_constant h hC

/-- Weaken constant in IsProductLikeAppendixDeltaSCSetOfDyadicTubes. -/
lemma IsProductLikeAppendixDeltaSCSetOfDyadicTubes.weaken_constant
    {δ s C C' : ℝ} {𝒯 : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (h : IsProductLikeAppendixDeltaSCSetOfDyadicTubes δ s C 𝒯) (hC : C ≤ C') :
    IsProductLikeAppendixDeltaSCSetOfDyadicTubes δ s C' 𝒯 := by
  rcases h with ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, IsDeltaSCSet.weaken_constant h4 hC⟩
