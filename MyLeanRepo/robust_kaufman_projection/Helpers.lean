module

public import MyLeanRepo.robust_kaufman_projection.Base

@[expose] public section

/-!
# Helper lemmas for the robust Kaufman projection theorem

This module provides three supporting results:
1. `affineProjection_lipschitz`: the affine projection is 2-Lipschitz for |σ| ≤ 1.
2. `ncover_eq_card_of_two_delta_separated`: for a finite strictly `2*δ`-separated set
   in `ℝ`, the `δ`-external covering number equals the cardinality.
3. `InUnitSquare.bounded`: any subset of the unit square is bounded.
-/

noncomputable section

open scoped ENNReal NNReal

open Metric Set

/-- The affine projection `p ↦ p 0 - σ * p 1` is `2`-Lipschitz when `|σ| ≤ 1`. -/
lemma affineProjection_lipschitz {σ : ℝ} (hσ : σ ∈ Set.Icc (-1 : ℝ) 1) :
    LipschitzWith 2 (fun p : EuclideanPlane => p 0 - σ * p 1) := by
  have h1 : |σ| ≤ 1 := by
    rcases hσ with ⟨hσ1, hσ2⟩
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h_main : ∀ (p q : EuclideanPlane),
      dist ((p 0 - σ * p 1)) ((q 0 - σ * q 1)) ≤ 2 * dist p q := by
    intro p q
    set a := p 0 - q 0 with ha
    set b := p 1 - q 1 with hb
    have h_alg : (p 0 - σ * p 1) - (q 0 - σ * q 1) = a - σ * b := by ring
    have h_dist1 : dist ((p 0 - σ * p 1)) ((q 0 - σ * q 1)) = |a - σ * b| := by
      rw [Real.dist_eq, h_alg]
    rw [h_dist1]
    have h2 : |a - σ * b| ≤ |a| + |σ| * |b| := by
      calc
        |a - σ * b| ≤ |a| + |σ * b| := abs_sub _ _
        _ = |a| + |σ| * |b| := by rw [abs_mul]
    have h3 : |σ| * |b| ≤ |b| := by
      have h31 : |σ| ≤ 1 := h1
      have h32 : 0 ≤ |b| := abs_nonneg b
      calc
        |σ| * |b| ≤ 1 * |b| := by gcongr
        _ = |b| := by ring
    have h4 : |a - σ * b| ≤ |a| + |b| := by linarith
    have h5 : (|a| + |b|) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
      have h51 : (|a| + |b|) ^ 2 = a ^ 2 + b ^ 2 + 2 * |a| * |b| := by
        have h : (|a| + |b|) ^ 2 = |a| ^ 2 + |b| ^ 2 + 2 * |a| * |b| := by ring
        rw [h]
        have h2 : |a| ^ 2 = a ^ 2 := by simp [sq_abs]
        have h3 : |b| ^ 2 = b ^ 2 := by simp [sq_abs]
        rw [h2, h3] <;> ring
      rw [h51]
      have h52 : 2 * |a| * |b| ≤ a ^ 2 + b ^ 2 := by
        have h : (|a| - |b|) ^ 2 ≥ 0 := by positivity
        have h2 : |a| ^ 2 + |b| ^ 2 ≥ 2 * |a| * |b| := by nlinarith
        simpa [sq_abs] using h2
      linarith
    have h6 : dist p q ^ 2 = a ^ 2 + b ^ 2 := by
      have h7 : dist p q = ‖p - q‖ := dist_eq_norm p q
      rw [h7]
      have h8 : ‖p - q‖ ^ 2 = ∑ i : Fin 2, ‖(p - q) i‖ ^ 2 :=
        EuclideanSpace.norm_sq_eq (p - q)
      rw [h8]
      simp [ha, hb, Fin.sum_univ_two]
      <;> ring
    have h9 : 0 ≤ |a| + |b| := by positivity
    have h10 : 0 ≤ Real.sqrt 2 * dist p q := by positivity
    have h11 : (|a| + |b|) ^ 2 ≤ (Real.sqrt 2 * dist p q) ^ 2 := by
      have h13 : (Real.sqrt 2 * dist p q) ^ 2 = 2 * (dist p q) ^ 2 := by
        calc
          (Real.sqrt 2 * dist p q) ^ 2
            = (Real.sqrt 2) ^ 2 * (dist p q) ^ 2 := by ring
          _ = 2 * (dist p q) ^ 2 := by
            rw [Real.sq_sqrt (by norm_num)] <;> ring
      rw [h13, h6]
      exact h5
    have h14 : |a| + |b| ≤ Real.sqrt 2 * dist p q := by
      by_contra h
      have h20 : Real.sqrt 2 * dist p q < |a| + |b| := by linarith
      have h21 : 0 ≤ Real.sqrt 2 * dist p q := by positivity
      have h22 : (Real.sqrt 2 * dist p q) ^ 2 < (|a| + |b|) ^ 2 := by nlinarith
      linarith [h11]
    have h15 : Real.sqrt 2 ≤ 2 := by
      have h16 : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      have h17 : Real.sqrt 4 = 2 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      linarith
    calc
      |a - σ * b| ≤ |a| + |b| := h4
      _ ≤ Real.sqrt 2 * dist p q := h14
      _ ≤ 2 * dist p q := by
        have h18 : Real.sqrt 2 * dist p q ≤ 2 * dist p q := by
          gcongr
          <;> linarith
        exact h18
  simpa [LipschitzWith, edist_dist, ENNReal.ofReal_mul] using
    fun x y => ENNReal.ofReal_le_ofReal (h_main x y)

/-- For a finite set `S` in `ℝ` whose distinct points are strictly more than `2*δ` apart,
the `δ`-external covering number equals the cardinality. -/
lemma ncover_eq_card_of_two_delta_separated
    {S : Finset ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 * δ < |x - y|) :
    Ncover δ (S : Set ℝ) = (S.card : ENNReal) := by
  let ε : NNReal := δ.toNNReal
  have hε : (ε : ℝ) = δ := by
    have h : 0 ≤ δ := by linarith
    have : (δ.toNNReal : ℝ) = max δ 0 := by simp
    rw [this, max_eq_left h]
  have h_sep' : IsSeparated (2 * ε : ENNReal) (S : Set ℝ) := by
    intro x hx y hy hxy
    have h9 : 2 * δ < |x - y| := h_sep x hx y hy hxy
    have h10 : (2 * ε : ENNReal) = ENNReal.ofReal (2 * δ) := by
      have h101 : (2 * ε : ENNReal) = ENNReal.ofReal (↑(2 * ε) : ℝ) := by
        exact Eq.symm ENNReal.ofReal_coe_nnreal
      rw [h101]
      have h103 : (↑(2 * ε) : ℝ) = 2 * δ := by
        simp [hε] <;> ring
      rw [h103]
    rw [h10]
    have h_edist : edist x y = ENNReal.ofReal |x - y| := by
      rw [edist_dist, Real.dist_eq]
    rw [h_edist]
    let a : NNReal := (2 * δ).toNNReal
    let b : NNReal := |x - y|.toNNReal
    have ha : (a : ℝ) = 2 * δ := by
      simp [a, show 0 ≤ 2 * δ by linarith]
    have hb : (b : ℝ) = |x - y| := by
      simp [b, show 0 ≤ |x - y| by positivity]
    have h_ab : a < b := by
      exact NNReal.coe_lt_coe.mp (by rw [ha, hb]; exact h9)
    have h16 : (a : ENNReal) < (b : ENNReal) := by exact_mod_cast h_ab
    have h17 : ENNReal.ofReal (2 * δ) = (a : ENNReal) := by
      simp [a, ENNReal.ofReal, show 0 ≤ 2 * δ by linarith] <;> rfl
    have h18 : ENNReal.ofReal |x - y| = (b : ENNReal) := by
      simp [b, ENNReal.ofReal, show 0 ≤ |x - y| by positivity] <;> rfl
    rw [h17, h18]
    exact h16
  have h1 : (S : Set ℝ).encard ≤ packingNumber (2 * ε) (S : Set ℝ) :=
    IsSeparated.encard_le_packingNumber (by rfl) h_sep'
  have h2 : packingNumber (2 * ε) (S : Set ℝ) ≤ externalCoveringNumber ε (S : Set ℝ) :=
    packingNumber_two_mul_le_externalCoveringNumber ε (S : Set ℝ)
  have h3 : (S : Set ℝ).encard ≤ externalCoveringNumber ε (S : Set ℝ) := le_trans h1 h2
  have h4 : externalCoveringNumber ε (S : Set ℝ) ≤ (S : Set ℝ).encard :=
    externalCoveringNumber_le_encard_self (S : Set ℝ)
  have h5 : externalCoveringNumber ε (S : Set ℝ) = (S : Set ℝ).encard := le_antisymm h4 h3
  have h6 : (S : Set ℝ).encard = ↑S.card := by
    simp
  rw [Ncover, h5, h6]
  <;> norm_cast

/-- Lower bound: for a finite strictly `2*δ`-separated set, the covering number is at least
the cardinality. -/
lemma ncover_lower_of_two_delta_separated
    {S : Finset ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 * δ < |x - y|) :
    (S.card : ENNReal) ≤ Ncover δ (S : Set ℝ) :=
  (ncover_eq_card_of_two_delta_separated hδ h_sep).symm.le

/-- Upper bound: the covering number of any finite set is at most its cardinality. -/
lemma ncover_upper_of_finset (S : Finset ℝ) {δ : ℝ} :
    Ncover δ (S : Set ℝ) ≤ (S.card : ENNReal) := by
  have h : externalCoveringNumber δ.toNNReal (S : Set ℝ) ≤ (S : Set ℝ).encard :=
    externalCoveringNumber_le_encard_self (S : Set ℝ)
  have h6 : (S : Set ℝ).encard = ↑S.card := by simp
  rw [Ncover, h6] at *
  <;> exact_mod_cast h

/-- Any subset of the unit square in the Euclidean plane is bounded. -/
lemma InUnitSquare.bounded {P : Set EuclideanPlane} (h : InUnitSquare P) :
    Bornology.IsBounded P := by
  have h1 : ∀ p : EuclideanPlane, (p 0 ∈ Set.Icc (0 : ℝ) 1 ∧ p 1 ∈ Set.Icc (0 : ℝ) 1) → ‖p‖ ≤ Real.sqrt 2 := by
    intro p hp
    have h2 : 0 ≤ p 0 := hp.1.1
    have h3 : p 0 ≤ 1 := hp.1.2
    have h4 : 0 ≤ p 1 := hp.2.1
    have h5 : p 1 ≤ 1 := hp.2.2
    have h6 : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
      have h7 := EuclideanSpace.norm_sq_eq p
      simpa [Fin.sum_univ_two] using h7
    have h8 : ‖p‖ ^ 2 ≤ 2 := by nlinarith
    have h9 : 0 ≤ ‖p‖ := by positivity
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  let Q : Set EuclideanPlane := {p | p 0 ∈ Set.Icc (0 : ℝ) 1 ∧ p 1 ∈ Set.Icc (0 : ℝ) 1}
  have hQ : Q ⊆ Metric.closedBall (0 : EuclideanPlane) (Real.sqrt 2) := by
    intro p hp
    have h10 : ‖p‖ ≤ Real.sqrt 2 := h1 p hp
    simpa [Metric.mem_closedBall, dist_zero_right] using h10
  have hP : P ⊆ Metric.closedBall (0 : EuclideanPlane) (Real.sqrt 2) :=
    h.trans hQ
  have hB : Bornology.IsBounded (Metric.closedBall (0 : EuclideanPlane) (Real.sqrt 2)) :=
    Metric.isBounded_closedBall
  exact Bornology.IsBounded.subset hB hP

end
