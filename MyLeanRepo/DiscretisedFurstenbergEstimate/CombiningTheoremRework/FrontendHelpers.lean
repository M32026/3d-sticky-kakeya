module

/-
  Frontend boundedness + cardinality helpers

  Provides:
  1. affineLine_family_bounded: set of AffineLines with |m|≤1, |b|≤3 is bounded
  2. dyadic_tube_family_card_bound: T0.card ≤ 12 * 16^n

  Whiteprint node: frontend_boundedness_card_helpers
  Status: COMPLETE
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.Gap1Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontendHelpers

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open DyadicCardToNcover

/-- A family of AffineLines, each representable as mkSlopeIntercept m b with
    |m|≤1 and |b|≤3, is bounded in the AffineLine metric. -/
lemma affineLine_family_bounded {F : Set AffineLine}
    (h : ∀ ℓ ∈ F, ∃ (m b : ℝ), |m| ≤ 1 ∧ |b| ≤ 3 ∧ AffineLine.mkSlopeIntercept m b = ℓ) :
    Bornology.IsBounded F := by
  have h_sp_norm : ∀ (ℓ : AffineLine), ‖ℓ.1.direction.starProjection‖ ≤ 1 := by
    intro ℓ
    exact Submodule.starProjection_norm_le (K := ℓ.1.direction)
  have h_off_norm : ∀ (ℓ : AffineLine), ℓ ∈ F → ‖ℓ.offset‖ ≤ 3 := by
    intro ℓ hℓ
    rcases h ℓ hℓ with ⟨m, b, hm, hb, rfl⟩
    have h1 : (AffineLine.mkSlopeIntercept m b).offset = b • offsetVec m :=
      mkSlopeIntercept_offset_formula m b
    rw [h1]
    have h2 : ‖(b • offsetVec m)‖ = |b| * ‖offsetVec m‖ := by
      rw [norm_smul] <;> rfl
    rw [h2]
    have h3 : ‖offsetVec m‖ ≤ 1 := by
      rw [offsetVec_norm m]
      have h4 : 0 < Real.sqrt (1 + m^2) := by positivity
      have h5 : 1 ≤ Real.sqrt (1 + m^2) := by
        have h6 : 1 ≤ 1 + m^2 := by nlinarith
        have h7 : Real.sqrt 1 ≤ Real.sqrt (1 + m^2) := Real.sqrt_le_sqrt h6
        simpa using h7
      have h6 : 1 / Real.sqrt (1 + m^2) ≤ 1 := by
        have h7 : 1 ≤ Real.sqrt (1 + m^2) := h5
        have h8 : 1 / Real.sqrt (1 + m^2) ≤ 1 := by
          have h_pos : 0 < Real.sqrt (1 + m^2) := by positivity
          calc 1 / Real.sqrt (1 + m^2) ≤ 1 / (1 : ℝ) := by gcongr
               _ = 1 := by norm_num
        exact h8
      exact h6
    calc |b| * ‖offsetVec m‖ ≤ |b| * 1 := by gcongr
         _ = |b| := by ring
         _ ≤ 3 := hb
  by_cases hF : F.Nonempty
  · rcases hF with ⟨ℓ₀, hℓ₀⟩
    have h_main : F ⊆ Metric.closedBall ℓ₀ 8 := by
      intro ℓ hℓ
      have h_dist : dist ℓ ℓ₀ ≤ 8 := by
        have h1 : dist ℓ ℓ₀ = ‖ℓ.1.direction.starProjection - ℓ₀.1.direction.starProjection‖ + ‖ℓ.offset - ℓ₀.offset‖ := by rfl
        rw [h1]
        have h2 : ‖ℓ.1.direction.starProjection - ℓ₀.1.direction.starProjection‖ ≤ 2 := by
          calc ‖ℓ.1.direction.starProjection - ℓ₀.1.direction.starProjection‖
            ≤ ‖ℓ.1.direction.starProjection‖ + ‖ℓ₀.1.direction.starProjection‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by gcongr <;> exact h_sp_norm _
          _ = 2 := by norm_num
        have h3 : ‖ℓ.offset - ℓ₀.offset‖ ≤ 6 := by
          calc ‖ℓ.offset - ℓ₀.offset‖
            ≤ ‖ℓ.offset‖ + ‖ℓ₀.offset‖ := norm_sub_le _ _
          _ ≤ 3 + 3 := by gcongr <;> exact h_off_norm _ ‹_›
          _ = 6 := by norm_num
        linarith
      exact h_dist
    have h_bdd : Bornology.IsBounded F := by
      rw [Metric.isBounded_iff_subset_closedBall ℓ₀]
      exact ⟨8, h_main⟩
    exact h_bdd
  · have h_empty : F = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using hF
    rw [h_empty]
    exact Bornology.isBounded_empty

/-- Cardinality bound for a finset of dyadic tubes at scale n, each with
    slope index in [-2^n, 2^n) and intersecting [0,1)^2 with |slope|≤1.
    Bound: card ≤ 12 * 16^n. -/
lemma dyadic_tube_family_card_bound {n : ℕ} (hn : n ≥ 2)
    {T0 : Finset (DyadicTube n)}
    (h_a : ∀ T ∈ T0, -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ))
    (h_slope : ∀ T ∈ T0, |T.slope| ≤ 1)
    (h_inc : ∀ T ∈ T0, ∃ (x : EuclideanPlane),
      0 ≤ x 0 ∧ x 0 < 1 ∧ 0 ≤ x 1 ∧ x 1 < 1 ∧ x ∈ T.toSet) :
    T0.card ≤ 12 * 16^n := by
  set δ : ℝ := dyadicDelta n with hδ_set
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_def : δ = 1 / (2 ^ n : ℝ) := by exact Eq.symm (Real.ext_cauchy rfl)
  have hδ_inv : 1 / δ = (2 ^ n : ℝ) := by
    rw [hδ_def]; field_simp <;> ring
  have h_b_bound : ∀ T ∈ T0, |(T.b : ℝ)| ≤ 2 * (2 ^ n : ℝ) + 1 := by
    intro T hT
    rcases h_inc T hT with ⟨x, hx0_lo, hx0_hi, hx1_lo, hx1_hi, hxT⟩
    have hT_def : |x 1 - T.slope * x 0 - T.intercept| ≤ δ := by
      simpa [DyadicTube.toSet, Set.mem_setOf_eq] using hxT
    have h_x1_abs : |x 1| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have h_x0_abs : |x 0| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have h_sl : |T.slope| ≤ 1 := h_slope T hT
    have h_term : |x 1 - T.slope * x 0| ≤ 2 := by
      have h4 : |x 1 - T.slope * x 0| ≤ |x 1| + |T.slope * x 0| := by
        exact real_abs_sub (x.ofLp 1) (T.slope * x.ofLp 0)
      have h5 : |T.slope * x 0| ≤ 1 := by
        calc |T.slope * x 0| = |T.slope| * |x 0| := by rw [abs_mul]
             _ ≤ 1 * 1 := by gcongr
             _ = 1 := by norm_num
      linarith
    have h_intercept : |T.intercept| ≤ 2 + δ := by
      have h4 : T.intercept = (x 1 - T.slope * x 0) - (x 1 - T.slope * x 0 - T.intercept) := by ring
      rw [h4]
      have h5 : |(x 1 - T.slope * x 0) - (x 1 - T.slope * x 0 - T.intercept)| ≤
          |x 1 - T.slope * x 0| + |x 1 - T.slope * x 0 - T.intercept| := by exact real_abs_sub (x.ofLp 1 - T.slope * x.ofLp 0) (x.ofLp 1 - T.slope * x.ofLp 0 - T.intercept)
      have h6 := h5.trans (add_le_add h_term hT_def)
      simpa using h6
    have h9 : T.intercept = (T.b : ℝ) * δ := by
      simp [DyadicTube.intercept, hδ_set] <;> ring
    rw [h9] at h_intercept
    have h10 : |(T.b : ℝ) * δ| = |(T.b : ℝ)| * δ := by
      rw [abs_mul, abs_of_pos hδ_pos]
    rw [h10] at h_intercept
    have h11 : |(T.b : ℝ)| * δ ≤ 2 + δ := h_intercept
    have h12 : |(T.b : ℝ)| ≤ (2 + δ) / δ := by
      calc |(T.b : ℝ)|
        = (|(T.b : ℝ)| * δ) / δ := by field_simp [hδ_pos.ne'] <;> ring
      _ ≤ (2 + δ) / δ := by gcongr
    have h13 : (2 + δ) / δ = 2 * (2 ^ n : ℝ) + 1 := by
      have h14 : (2 + δ) / δ = 2 / δ + 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      have h15 : 2 / δ = 2 * (2 ^ n : ℝ) := by
        have h16 : 2 / δ = 2 * (1 / δ) := by ring
        rw [h16, hδ_inv] <;> ring
      rw [h14, h15] <;> ring
    rw [h13] at h12
    exact h12
  let a_set : Finset ℤ := Finset.Ico (-(2 ^ n : ℤ)) (2 ^ n : ℤ)
  let b_set : Finset ℤ := Finset.Icc (-(2 * (2 ^ n : ℤ) + 1)) (2 * (2 ^ n : ℤ) + 1)
  have h1 : ∀ T ∈ T0, T.a ∈ a_set := by
    intro T hT
    have h := h_a T hT
    simp only [a_set, Finset.mem_Ico]
    exact ⟨h.1, h.2⟩
  have h2 : ∀ T ∈ T0, T.b ∈ b_set := by
    intro T hT
    have h := h_b_bound T hT
    simp only [b_set, Finset.mem_Icc]
    have h_abs : -(2 * (2 ^ n : ℝ) + 1) ≤ (T.b : ℝ) ∧ (T.b : ℝ) ≤ 2 * (2 ^ n : ℝ) + 1 := by
      exact abs_le.mp h
    have h_i1 : (-(2 * (2 ^ n) + 1 : ℤ)) ≤ T.b := by exact_mod_cast h_abs.1
    have h_i2 : T.b ≤ (2 * (2 ^ n) + 1 : ℤ) := by exact_mod_cast h_abs.2
    exact ⟨h_i1, h_i2⟩
  let f : DyadicTube n → ℤ × ℤ := fun T => (T.a, T.b)
  have h_inj : Set.InjOn f (T0 : Set (DyadicTube n)) := by
    intro T1 hT1 T2 hT2 h
    have h_a1 : T1.a = T2.a := by simp [f] at h <;> tauto
    have h_b1 : T1.b = T2.b := by simp [f] at h <;> tauto
    cases T1; cases T2; simp_all
  have h3 : (T0.image f).card = T0.card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h4 : T0.image f ⊆ a_set ×ˢ b_set := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨T, hT, rfl⟩
    exact Finset.mem_product.mpr ⟨h1 T hT, h2 T hT⟩
  have h5 : T0.card ≤ (a_set ×ˢ b_set).card := by
    calc T0.card = (T0.image f).card := h3.symm
         _ ≤ (a_set ×ˢ b_set).card := Finset.card_le_card h4
  have h6 : (a_set ×ˢ b_set).card = a_set.card * b_set.card := Finset.card_product _ _
  rw [h6] at h5
  have h7 : a_set.card ≤ 2 ^ (n + 1) := by
    have h71 : a_set = Finset.Ico (-(2 ^ n : ℤ)) (2 ^ n : ℤ) := by rfl
    rw [h71]
    let f : ℤ → ℕ := fun x => (x + (2 ^ n : ℤ)).toNat
    have h_inj : Set.InjOn f (Finset.Ico (-(2 ^ n : ℤ)) (2 ^ n : ℤ) : Set ℤ) := by
      intro x hx y hy h_eq
      have hx' : -(2 ^ n : ℤ) ≤ x := (Finset.mem_Ico.mp hx).1
      have hy' : -(2 ^ n : ℤ) ≤ y := (Finset.mem_Ico.mp hy).1
      have h1 : 0 ≤ x + (2 ^ n : ℤ) := by linarith
      have h2 : 0 ≤ y + (2 ^ n : ℤ) := by linarith
      have h3 : ((x + (2 ^ n : ℤ)).toNat : ℤ) = x + (2 ^ n : ℤ) := by
        rw [Int.toNat_of_nonneg h1]
      have h4 : ((y + (2 ^ n : ℤ)).toNat : ℤ) = y + (2 ^ n : ℤ) := by
        rw [Int.toNat_of_nonneg h2]
      have h5 : ((x + (2 ^ n : ℤ)).toNat : ℤ) = ((y + (2 ^ n : ℤ)).toNat : ℤ) := by exact_mod_cast h_eq
      rw [h3, h4] at h5
      linarith
    have h_img : (Finset.Ico (-(2 ^ n : ℤ)) (2 ^ n : ℤ)).image f ⊆ Finset.range (2 ^ (n + 1)) := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
      have hx' : -(2 ^ n : ℤ) ≤ x ∧ x < (2 ^ n : ℤ) := Finset.mem_Ico.mp hx
      have h1 : 0 ≤ x + (2 ^ n : ℤ) := by linarith
      have h2 : x + (2 ^ n : ℤ) < (2 ^ (n + 1) : ℤ) := by
        simp [pow_succ] <;> linarith
      have h3 : (x + (2 ^ n : ℤ)).toNat < 2 ^ (n + 1) := by
        have h4 : ((x + (2 ^ n : ℤ)).toNat : ℤ) = x + (2 ^ n : ℤ) := Int.toNat_of_nonneg h1
        exact_mod_cast (by linarith)
      simpa [f, Finset.mem_range] using h3
    have h9 : (Finset.Ico (-(2 ^ n : ℤ)) (2 ^ n : ℤ)).card = ((Finset.Ico (-(2 ^ n : ℤ)) (2 ^ n : ℤ)).image f).card := by
      rw [Finset.card_image_of_injOn h_inj]
    rw [h9]
    have h10 : ((Finset.Ico (-(2 ^ n : ℤ)) (2 ^ n : ℤ)).image f).card ≤ (Finset.range (2 ^ (n + 1))).card := Finset.card_le_card h_img
    simpa using h10
  have h8 : b_set.card ≤ 5 * 2 ^ n := by
    have h81 : b_set = Finset.Icc (-(2 * (2 ^ n : ℤ) + 1)) (2 * (2 ^ n : ℤ) + 1) := by rfl
    rw [h81]
    let shift : ℤ := 2 * (2 ^ n : ℤ) + 1
    let f : ℤ → ℕ := fun x => (x + shift).toNat
    have h_inj : Set.InjOn f (Finset.Icc (-(shift)) (shift) : Set ℤ) := by
      intro x hx y hy h_eq
      have hx' : -(shift) ≤ x := (Finset.mem_Icc.mp hx).1
      have hy' : -(shift) ≤ y := (Finset.mem_Icc.mp hy).1
      have h1 : 0 ≤ x + shift := by linarith
      have h2 : 0 ≤ y + shift := by linarith
      have h3 : ((x + shift).toNat : ℤ) = x + shift := by rw [Int.toNat_of_nonneg h1]
      have h4 : ((y + shift).toNat : ℤ) = y + shift := by rw [Int.toNat_of_nonneg h2]
      have h5 : ((x + shift).toNat : ℤ) = ((y + shift).toNat : ℤ) := by exact_mod_cast h_eq
      rw [h3, h4] at h5
      linarith
    have h_img : (Finset.Icc (-(shift)) (shift)).image f ⊆ Finset.range (4 * (2 ^ n) + 3) := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
      have hx' : -(shift) ≤ x ∧ x ≤ shift := Finset.mem_Icc.mp hx
      have h1 : 0 ≤ x + shift := by linarith
      have h2 : x + shift < (4 * (2 ^ n) + 3 : ℤ) := by
        simp [shift] <;> linarith
      have h3 : (x + shift).toNat < 4 * (2 ^ n) + 3 := by
        have h4 : ((x + shift).toNat : ℤ) = x + shift := Int.toNat_of_nonneg h1
        exact_mod_cast (by linarith)
      simpa [f, Finset.mem_range] using h3
    have h9 : (Finset.Icc (-(shift)) (shift)).card = ((Finset.Icc (-(shift)) (shift)).image f).card := by
      rw [Finset.card_image_of_injOn h_inj]
    rw [h9]
    have h10 : ((Finset.Icc (-(shift)) (shift)).image f).card ≤ (Finset.range (4 * (2 ^ n) + 3)).card := Finset.card_le_card h_img
    have h11 : (Finset.range (4 * (2 ^ n) + 3)).card = 4 * (2 ^ n) + 3 := by simp
    rw [h11] at h10
    have h12 : (4 * (2 ^ n) + 3 : ℕ) ≤ 5 * 2 ^ n := by
      have h13 : 4 * 2 ^ n + 3 ≤ 5 * 2 ^ n := by
        have h14 : 3 ≤ 2 ^ n := by
          have h15 : n ≥ 2 := hn
          have h16 : 2 ^ n ≥ 4 := by
            have h17 : n ≥ 2 := hn
            have h18 : 2 ^ n ≥ 2 ^ 2 := by
              gcongr
              <;> norm_num
            norm_num at h18 ⊢ <;> exact h18
          linarith
        linarith
      exact_mod_cast h13
    exact le_trans h10 h12
  have h9 : T0.card ≤ (2 ^ (n + 1)) * (5 * 2 ^ n) := by
    calc T0.card ≤ a_set.card * b_set.card := h5
         _ ≤ (2 ^ (n + 1)) * (5 * 2 ^ n) := by gcongr
  have h10 : (2 ^ (n + 1)) * (5 * 2 ^ n) = 10 * 4 ^ n := by
    have h101 : 2 ^ (n + 1) * 2 ^ n = 2 ^ (2 * n + 1) := by
      have h_exp : (n + 1) + n = 2 * n + 1 := by omega
      rw [← pow_add, h_exp]
    have h : (2 ^ (n + 1)) * (5 * 2 ^ n) = 5 * (2 ^ (n + 1) * 2 ^ n) := by ring
    rw [h, h101]
    have h103 : 2 ^ (2 * n + 1) = 2 * 4 ^ n := by
      have h104 : 2 ^ (2 * n + 1) = 2 * 2 ^ (2 * n) := by
        rw [pow_add, pow_one] <;> ring
      rw [h104]
      have h105 : 2 ^ (2 * n) = 4 ^ n := by
        have h106 : 2 ^ (2 * n) = (2 ^ 2) ^ n := by
          rw [pow_mul] <;> ring
        rw [h106] <;> norm_num
      rw [h105] <;> ring
    rw [h103] <;> ring
  rw [h10] at h9
  have h11 : 10 * 4 ^ n ≤ 12 * 16 ^ n := by
    have h12 : 4 ^ n ≤ 16 ^ n := by
      gcongr <;> norm_num
    nlinarith
  exact le_trans h9 h11

end DirecretisedFurstenbergEstimate.FrontendHelpers

end
