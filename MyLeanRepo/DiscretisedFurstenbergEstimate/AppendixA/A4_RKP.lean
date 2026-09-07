module

/-
  Appendix A, Step A4: Robust Kaufman refinement tied to C_Q.

  Refactored to use canonical Interfaces types.

  Whiteprint node: appendix_a_alternative / A4
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.EnergyToDeltaSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A4_PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A4_CQpiSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A4_SSetScaling
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.AffineLinePackingBound
public import MyLeanRepo.robust_kaufman_projection
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal Classical

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA4

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA

abbrev CoarseSquare (Δ : ℝ) := ℤ × ℤ
abbrev CoarseTube := AffineLine
abbrev FineTube := AffineLine

/-- Slope parameter of an affine line (a in x = a*y + b). -/
def tubeSlope (T : AffineLine) : ℝ :=
  (LemmaE.affineLineParams T).1

/-- Normalize a point by subtracting z_Q and dividing by Δ. -/
def a4_normalize (Δ : ℝ) (z_Q : Plane) (p : Plane) : Plane :=
  EuclideanSpace.equiv (Fin 2) ℝ |>.symm fun i => (p i - z_Q i) / Δ

lemma a4_normalize_injective (Δ : ℝ) (hΔ_pos : 0 < Δ) (z_Q : Plane) :
    Function.Injective (a4_normalize Δ z_Q) := by
  intro x y h
  have h1 : ∀ i : Fin 2, (a4_normalize Δ z_Q x) i = (a4_normalize Δ z_Q y) i := by
    intro i; rw [h]
  have h2 : ∀ i : Fin 2, (x i - z_Q i) / Δ = (y i - z_Q i) / Δ := by
    intro i; simpa [a4_normalize] using h1 i
  have h3 : ∀ i : Fin 2, x i = y i := by
    intro i; have h4 := h2 i; field_simp [hΔ_pos.ne'] at h4 ⊢ <;> linarith
  ext i; exact h3 i

lemma a4_normalize_unnormalize (Δ : ℝ) (hΔ_pos : 0 < Δ) (z_Q p : Plane) :
    Δ • (a4_normalize Δ z_Q p) + z_Q = p := by
  ext i
  simp [a4_normalize]
  <;> field_simp [hΔ_pos.ne'] <;> ring

/-- Slope map is 2-Lipschitz with respect to AffineLine distance. -/
lemma tubeSlope_lipschitz (ℓ₁ ℓ₂ : AffineLine)
    (hv1 : (LemmaE.getDirV ℓ₁) 1 ≠ 0)
    (hv2 : (LemmaE.getDirV ℓ₂) 1 ≠ 0)
    (ha1 : |tubeSlope ℓ₁| ≤ 1)
    (ha2 : |tubeSlope ℓ₂| ≤ 1) :
    |tubeSlope ℓ₁ - tubeSlope ℓ₂| ≤ 2 * dist ℓ₁ ℓ₂ := by
  set a1 := tubeSlope ℓ₁ with ha1_def
  set a2 := tubeSlope ℓ₂ with ha2_def
  set d : ℝ := ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ with hd_def
  set e2 : Plane := EuclideanSpace.single 1 (1 : ℝ) with he2_def
  have he2_norm : ‖e2‖ = 1 := by
    have h4 : ‖e2‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      simp [e2, EuclideanSpace.single_apply] <;> norm_num
    have h7 : 0 ≤ ‖e2‖ := by positivity
    nlinarith
  have hP1 : (ℓ₁.1.direction.starProjection e2) 0 = a1 / (1 + a1^2) ∧
      (ℓ₁.1.direction.starProjection e2) 1 = 1 / (1 + a1^2) :=
    TubesAndSlopes.starProjection_e2_semicircle ℓ₁ hv1
  have hP2 : (ℓ₂.1.direction.starProjection e2) 0 = a2 / (1 + a2^2) ∧
      (ℓ₂.1.direction.starProjection e2) 1 = 1 / (1 + a2^2) :=
    TubesAndSlopes.starProjection_e2_semicircle ℓ₂ hv2
  have h_norm_sq : ‖ℓ₁.1.direction.starProjection e2 - ℓ₂.1.direction.starProjection e2‖ ^ 2 =
      (a1 - a2)^2 / ((1 + a1^2) * (1 + a2^2)) := by
    have h_algebraic := TubesAndSlopes.semicircle_chord_algebraic a1 a2
    have h10 : (ℓ₁.1.direction.starProjection e2 - ℓ₂.1.direction.starProjection e2) 0 =
        a1 / (1 + a1^2) - a2 / (1 + a2^2) := by
      have h101 : (ℓ₁.1.direction.starProjection e2) 0 = a1 / (1 + a1^2) := hP1.1
      have h102 : (ℓ₂.1.direction.starProjection e2) 0 = a2 / (1 + a2^2) := hP2.1
      simpa [h101, h102] using rfl
    have h11 : (ℓ₁.1.direction.starProjection e2 - ℓ₂.1.direction.starProjection e2) 1 =
        1 / (1 + a1^2) - 1 / (1 + a2^2) := by
      have h111 : (ℓ₁.1.direction.starProjection e2) 1 = 1 / (1 + a1^2) := hP1.2
      have h112 : (ℓ₂.1.direction.starProjection e2) 1 = 1 / (1 + a2^2) := hP2.2
      simpa [h111, h112] using rfl
    have h_norm_eq : ‖ℓ₁.1.direction.starProjection e2 - ℓ₂.1.direction.starProjection e2‖ ^ 2 =
        ((ℓ₁.1.direction.starProjection e2 - ℓ₂.1.direction.starProjection e2) 0)^2 +
        ((ℓ₁.1.direction.starProjection e2 - ℓ₂.1.direction.starProjection e2) 1)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
    rw [h_norm_eq, h10, h11]
    exact h_algebraic
  have h_chord : ‖ℓ₁.1.direction.starProjection e2 - ℓ₂.1.direction.starProjection e2‖ =
      |a1 - a2| / Real.sqrt ((1 + a1^2) * (1 + a2^2)) := by
    have h_pos : 0 < (1 + a1^2) * (1 + a2^2) := by positivity
    have h12 : (|a1 - a2| / Real.sqrt ((1 + a1^2) * (1 + a2^2))) ^ 2 =
        (a1 - a2)^2 / ((1 + a1^2) * (1 + a2^2)) := by
      have h13 : Real.sqrt ((1 + a1^2) * (1 + a2^2)) ^ 2 = (1 + a1^2) * (1 + a2^2) :=
        Real.sq_sqrt (by positivity)
      have h14_abs : |a1 - a2| ^ 2 = (a1 - a2)^2 := by rw [sq_abs]
      rw [div_pow, h14_abs, h13]
    have h14_nonneg : 0 ≤ ‖ℓ₁.1.direction.starProjection e2 - ℓ₂.1.direction.starProjection e2‖ := by positivity
    have h15_nonneg : 0 ≤ |a1 - a2| / Real.sqrt ((1 + a1^2) * (1 + a2^2)) := by positivity
    nlinarith
  have h_op_norm : ‖ℓ₁.1.direction.starProjection e2 - ℓ₂.1.direction.starProjection e2‖ ≤ d := by
    have h : ‖(ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection) e2‖ ≤
        ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ * ‖e2‖ :=
      ContinuousLinearMap.le_opNorm (ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection) e2
    rw [he2_norm] at h
    simpa [hd_def] using h
  have h13 : (1 + a1^2) * (1 + a2^2) ≤ 4 := by
    have h14 : a1^2 ≤ 1 := by nlinarith [abs_le.mp ha1]
    have h15 : a2^2 ≤ 1 := by nlinarith [abs_le.mp ha2]
    nlinarith
  have h16 : Real.sqrt ((1 + a1^2) * (1 + a2^2)) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)] <;> nlinarith
  have h_a_bound : |a1 - a2| ≤ 2 * d := by
    rw [h_chord] at h_op_norm
    have h17 : |a1 - a2| / Real.sqrt ((1 + a1^2) * (1 + a2^2)) ≤ d := h_op_norm
    have h_sqrt_pos : 0 < Real.sqrt ((1 + a1^2) * (1 + a2^2)) := Real.sqrt_pos.mpr (by positivity)
    have h_div_mul : |a1 - a2| / Real.sqrt ((1 + a1^2) * (1 + a2^2)) *
        Real.sqrt ((1 + a1^2) * (1 + a2^2)) = |a1 - a2| := by
      field_simp [h_sqrt_pos.ne'] <;> ring
    calc |a1 - a2|
      = |a1 - a2| / Real.sqrt ((1 + a1^2) * (1 + a2^2)) *
          Real.sqrt ((1 + a1^2) * (1 + a2^2)) := h_div_mul.symm
    _ ≤ d * Real.sqrt ((1 + a1^2) * (1 + a2^2)) := by gcongr
    _ ≤ d * 2 := by gcongr
    _ = 2 * d := by ring
  have h_d_le_dist : d ≤ dist ℓ₁ ℓ₂ := by
    have hdef : dist ℓ₁ ℓ₂ = d + ‖ℓ₁.offset - ℓ₂.offset‖ := by rfl
    rw [hdef]
    exact le_add_of_nonneg_right (norm_nonneg _)
  calc |a1 - a2|
    ≤ 2 * d := h_a_bound
  _ ≤ 2 * dist ℓ₁ ℓ₂ := by gcongr

/-- Build BasicProjectionData from RKP projection output X. -/
def a4_build_basic
    (Δ s ε : ℝ) (P : Finset Plane) (boldT : CoarseTube) (σ : ℝ)
    (hσ_eq : σ = tubeSlope boldT)
    (X : Set ℝ)
    (hX_sub : X ⊆ (affineProj σ '' (P : Set Plane)))
    (hX_sset : IsDeltaSSet Δ s (Real.rpow Δ (-576 * ε)) X)
    (hX_lower : ENNReal.ofReal (Real.rpow Δ (576 * ε - s)) ≤
        Metric.externalCoveringNumber Δ.toNNReal X) :
    BasicProjectionData Δ s ε P boldT :=
  let projFun : Plane → ℝ := affineProj σ
  { σ := σ
    hσ_eq := hσ_eq
    projFun := projFun
    hprojFun := by rfl
    Pi := X
    hPi_sset := hX_sset
    hPi_lower := hX_lower
    witness := fun x => if h : x ∈ X then Classical.choose (hX_sub h) else (0 : Plane)
    h_witness_mem := by
      intro x hx
      have h_wit : (if h : x ∈ X then Classical.choose (hX_sub h) else (0 : Plane)) ∈ P := by
        rw [dif_pos hx]; exact (Classical.choose_spec (hX_sub hx)).1
      exact h_wit
    h_witness_proj := by
      intro x hx
      have h_wit : projFun ((if h : x ∈ X then Classical.choose (hX_sub h) else (0 : Plane))) = x := by
        rw [dif_pos hx]; exact (Classical.choose_spec (hX_sub hx)).2
      exact h_wit
    hPi_sub := hX_sub }

/-- Per-square A4 helper: normalize P_Q, apply RKP, construct A4_SquareData. -/
def a4_per_square_helper
    (Δ δ s t ε : ℝ)
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hΔ_small : Real.rpow Δ ε ≤ 1 / 81)
    (hΔ_small_pack : (4000 : ENNReal) * (affinePackingM : ENNReal) ≤
        ENNReal.ofReal (Real.rpow Δ (-ε)))
    (hδ_eq : δ = Δ ^ 2)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (hε_pos : 0 < ε)
    (ht : t ≤ 2)
    (hRKP_at_Δ : ∀ (P : Set Plane) (directions : Set ℝ),
      InUnitSquare P →
      directions ⊆ Set.Icc (-1 : ℝ) 1 →
      IsDeltaSSet Δ t (Real.rpow Δ (-48 * ε)) P →
      IsDeltaSSet Δ s (Real.rpow Δ (-48 * ε)) directions →
      ENNReal.ofReal (Real.rpow Δ (48 * ε - t)) ≤ Ncover Δ P →
      Ncover Δ P ≤ ENNReal.ofReal (Real.rpow Δ (-t - 48 * ε)) →
      ENNReal.ofReal (Real.rpow Δ (48 * ε - s)) ≤ Ncover Δ directions →
      Ncover Δ directions ≤ ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε)) →
      ∃ goodDirections : Set ℝ,
        goodDirections ⊆ directions ∧
        Ncover Δ directions ≤ 2 * Ncover Δ goodDirections ∧
        ∀ σ ∈ goodDirections,
          ∀ P' : Set Plane, P' ⊆ P →
            ENNReal.ofReal (Real.rpow Δ (48 * ε)) * Ncover Δ P ≤ Ncover Δ P' →
            ∃ X : Set ℝ,
              X ⊆ RobustKaufmanProjection.affineProjection σ P' ∧
              IsDeltaSSet Δ s (Real.rpow Δ (-576 * ε)) X ∧
              ENNReal.ofReal (Real.rpow Δ (576 * ε - s)) ≤ Ncover Δ X)
    (Q : CoarseSquare Δ)
    (base : A2_SquareData Δ δ s t ε Q)
    (hC_card_upper : (base.C_Q.card : ℝ) ≤ Real.rpow Δ (-s - 29 * ε))
    (hC_Q_slope_cover_upper : Metric.externalCoveringNumber Δ.toNNReal (tubeSlope '' (base.C_Q : Set CoarseTube)) ≤
      ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε)))
    (hH_Q_lower : base.H_Q ≥ Real.rpow Δ (-(s + t) + 36 * ε)) :
    A4_SquareData Δ δ s t ε Q := by
  let z_Q : Plane := EuclideanSpace.equiv (Fin 2) ℝ |>.symm fun i =>
    match i with
    | 0 => Δ * (Q.1 : ℝ)
    | 1 => Δ * (Q.2 : ℝ)
  let normalize := a4_normalize Δ z_Q
  let P_norm : Finset Plane := base.P_Q.image normalize
  let P_norm_set : Set Plane := (P_norm : Set Plane)
  let slopeSet : Set ℝ := tubeSlope '' (base.C_Q : Set CoarseTube)
  have hP_norm_card : (P_norm.card : ℝ) = (base.P_Q.card : ℝ) := by
    have h_inj : Function.Injective normalize := a4_normalize_injective Δ hΔ_pos z_Q
    simp [P_norm, Finset.card_image_of_injective _ h_inj]
  have hP_norm_separated : SeparatedAt Δ P_norm_set := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨y0, hy0, rfl⟩
    have h_ne : x0 ≠ y0 := by
      intro h; apply hxy; rw [h]
    have h_dist : dist (normalize x0) (normalize y0) = dist x0 y0 / Δ := by
      have h1 : normalize x0 - normalize y0 = (1 / Δ : ℝ) • (x0 - y0) := by
        have h_eq1 : (EuclideanSpace.equiv (Fin 2) ℝ) (normalize x0 - normalize y0) =
            (EuclideanSpace.equiv (Fin 2) ℝ) ((1 / Δ : ℝ) • (x0 - y0)) := by
          funext i; simp [a4_normalize, normalize] <;> ring
        exact (EuclideanSpace.equiv (Fin 2) ℝ).injective h_eq1
      rw [dist_eq_norm, h1, norm_smul]
      have h_pos : 0 < (1 / Δ : ℝ) := by positivity
      have h_norm : ‖(1 / Δ : ℝ)‖ = (1 / Δ : ℝ) := by
        have h : ‖(1 / Δ : ℝ)‖ = |(1 / Δ : ℝ)| := by exact Real.norm_eq_abs (1 / Δ)
        rw [h, abs_of_pos h_pos]
      rw [h_norm]
      have h_norm2 : ‖x0 - y0‖ = dist x0 y0 := by rw [dist_eq_norm]
      rw [h_norm2] <;> field_simp [hΔ_pos.ne'] <;> ring
    have h4 : Δ ^ 2 ≤ dist x0 y0 := by
      have h5 : δ ≤ dist x0 y0 := base.hP_Q_separated hx0 hy0 h_ne
      rw [hδ_eq] at h5; exact h5
    have h6 : Δ ≤ dist x0 y0 / Δ := by
      calc Δ = Δ ^ 2 / Δ := by field_simp [hΔ_pos.ne'] <;> ring
           _ ≤ dist x0 y0 / Δ := by gcongr
    rw [h_dist]; exact h6
  have hP_norm_bounded : ∀ p ∈ P_norm, p 0 ∈ Set.Icc (0 : ℝ) 1 ∧ p 1 ∈ Set.Icc (0 : ℝ) 1 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    have hq_box : q ∈ squareSet Δ Q := base.hP_Q_in_square hq
    have hq0 : q 0 ∈ Set.Ico (Δ * (Q.1 : ℝ)) (Δ * ((Q.1 : ℝ) + 1)) := by
      simpa [squareSet] using hq_box.1
    have hq1 : q 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1)) := by
      simpa [squareSet] using hq_box.2
    have h01 : 0 ≤ (normalize q) 0 := by
      have h_eq : (normalize q) 0 = (q 0 - Δ * (Q.1 : ℝ)) / Δ := by
        simp [a4_normalize, normalize] <;> rfl
      rw [h_eq]
      have h : Δ * (Q.1 : ℝ) ≤ q 0 := hq0.1
      have h' : 0 ≤ q 0 - Δ * (Q.1 : ℝ) := by linarith
      exact div_nonneg h' hΔ_pos.le
    have h02 : (normalize q) 0 ≤ 1 := by
      have h_eq : (normalize q) 0 = (q 0 - Δ * (Q.1 : ℝ)) / Δ := by
        simp [a4_normalize, normalize] <;> rfl
      rw [h_eq]
      have h : q 0 < Δ * ((Q.1 : ℝ) + 1) := hq0.2
      have h' : (q 0 - Δ * (Q.1 : ℝ)) / Δ ≤ 1 := by
        have h'' : q 0 - Δ * (Q.1 : ℝ) < Δ := by linarith
        have h_div : (q 0 - Δ * (Q.1 : ℝ)) / Δ < 1 := by
          rw [div_lt_one hΔ_pos] <;> linarith
        exact h_div.le
      exact h'
    have h11 : 0 ≤ (normalize q) 1 := by
      have h_eq : (normalize q) 1 = (q 1 - Δ * (Q.2 : ℝ)) / Δ := by
        simp [a4_normalize, normalize] <;> rfl
      rw [h_eq]
      have h : Δ * (Q.2 : ℝ) ≤ q 1 := hq1.1
      have h' : 0 ≤ q 1 - Δ * (Q.2 : ℝ) := by linarith
      exact div_nonneg h' hΔ_pos.le
    have h12 : (normalize q) 1 ≤ 1 := by
      have h_eq : (normalize q) 1 = (q 1 - Δ * (Q.2 : ℝ)) / Δ := by
        simp [a4_normalize, normalize] <;> rfl
      rw [h_eq]
      have h : q 1 < Δ * ((Q.2 : ℝ) + 1) := hq1.2
      have h' : (q 1 - Δ * (Q.2 : ℝ)) / Δ ≤ 1 := by
        have h'' : q 1 - Δ * (Q.2 : ℝ) < Δ := by linarith
        have h_div : (q 1 - Δ * (Q.2 : ℝ)) / Δ < 1 := by
          rw [div_lt_one hΔ_pos] <;> linarith
        exact h_div.le
      exact h'
    exact ⟨⟨h01, h02⟩, ⟨h11, h12⟩⟩
  have hP_norm_unnormalize : ∀ p ∈ P_norm, Δ • p + z_Q ∈ base.P_Q := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    have h_eq : Δ • normalize q + z_Q = q := a4_normalize_unnormalize Δ hΔ_pos z_Q q
    rw [h_eq]; exact hq
  have hP_unit : P_norm_set ⊆ {p : Plane | p 0 ∈ Set.Icc (0 : ℝ) 1 ∧ p 1 ∈ Set.Icc (0 : ℝ) 1} := by
    intro p hp; exact hP_norm_bounded p hp
  have hslope_bounded : slopeSet ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro σ hσ
    rcases hσ with ⟨boldT, hboldT, rfl⟩
    have h : |tubeSlope boldT| ≤ 1 := base.hC_Q_slope_bound boldT hboldT
    exact ⟨by linarith [abs_le.mp h], by linarith [abs_le.mp h]⟩
  have hδ_pos : 0 < δ := by rw [hδ_eq] <;> positivity
  have ht_nonneg : 0 ≤ t := by linarith
  have hP_sset : IsDeltaSSet Δ t (Real.rpow Δ (-48 * ε)) P_norm_set := by
    have h_norm_eq : normalize = fun p : Plane => (1 / Δ : ℝ) • p - (1 / Δ : ℝ) • z_Q := by
      funext p; ext i; simp [a4_normalize, normalize] <;> ring
    have hP_norm_set_eq : P_norm_set =
        ((fun p : Plane => (1 / Δ : ℝ) • p - (1 / Δ : ℝ) • z_Q) '' (base.P_Q : Set Plane)) := by
      simp [P_norm_set, P_norm, h_norm_eq] <;> rfl
    rw [hP_norm_set_eq]
    have h_sset_raw : IsDeltaSSet (δ / Δ) t
        (Real.rpow Δ (-t - 10 * ε) * Δ ^ t)
        ((fun p : Plane => (1 / Δ : ℝ) • p - (1 / Δ : ℝ) • z_Q) '' (base.P_Q : Set Plane)) :=
      sset_normalize base.hP_Q_sset hΔ_pos z_Q hδ_pos ht_nonneg (Real.rpow_pos_of_pos hΔ_pos _)
    have hδ_div : δ / Δ = Δ := by
      rw [hδ_eq]; field_simp [hΔ_pos.ne'] <;> ring
    rw [hδ_div] at h_sset_raw
    have h_const : Real.rpow Δ (-t - 10 * ε) * Δ ^ t = Real.rpow Δ (-10 * ε) := by
      have h_rpow : (Δ ^ t : ℝ) = Real.rpow Δ t := by simp
      rw [h_rpow]
      have h1 : Real.rpow Δ (-t - 10 * ε) * Real.rpow Δ t = Real.rpow Δ ((-t - 10 * ε) + t) :=
        (Real.rpow_add hΔ_pos (-t - 10 * ε) t).symm
      have h2 : ((-t - 10 * ε) + t) = -10 * ε := by ring
      rw [h1, h2]
    rw [h_const] at h_sset_raw
    have h_weaken : Real.rpow Δ (-10 * ε) ≤ Real.rpow Δ (-48 * ε) := by
      have h_exp : -10 * ε ≥ -48 * ε := by linarith
      have hΔ_lt_one : Δ ≤ 1 := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one h_exp
    have hC_pos : 0 < Real.rpow Δ (-48 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    refine' ⟨h_sset_raw.1, h_sset_raw.2.1, hC_pos, h_sset_raw.2.2.2.1, _⟩
    intro x r hr
    have h4 := h_sset_raw.2.2.2.2 x r hr
    calc (Metric.externalCoveringNumber Δ.toNNReal (_ ∩ Metric.closedBall x r) : ENNReal)
      ≤ ENNReal.ofReal (Real.rpow Δ (-10 * ε)) * (ENNReal.ofReal r) ^ t *
          (Metric.externalCoveringNumber Δ.toNNReal _ : ENNReal) := h4
    _ ≤ ENNReal.ofReal (Real.rpow Δ (-48 * ε)) * (ENNReal.ofReal r) ^ t *
          (Metric.externalCoveringNumber Δ.toNNReal _ : ENNReal) := by gcongr <;> exact h_weaken
  have hslope_sset : IsDeltaSSet Δ s (Real.rpow Δ (-48 * ε)) slopeSet := by
    have h_weaken : Real.rpow Δ (-25 * ε) ≤ Real.rpow Δ (-48 * ε) := by
      have h_exp : -25 * ε ≥ -48 * ε := by linarith
      have hΔ_le_one : Δ ≤ 1 := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_le_one h_exp
    rcases base.hC_Q_slope_sset with ⟨hne, hδ, hC, hs, h_main⟩
    have hC42_pos : 0 < Real.rpow Δ (-48 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_factor : ENNReal.ofReal (Real.rpow Δ (-25 * ε)) ≤
        ENNReal.ofReal (Real.rpow Δ (-48 * ε)) :=
      ENNReal.ofReal_le_ofReal h_weaken
    refine' ⟨hne, hδ, hC42_pos, hs, _⟩
    intro x r hr
    have h4 := h_main x r hr
    have h51 : ENNReal.ofReal (Real.rpow Δ (-25 * ε)) * (ENNReal.ofReal r) ^ s ≤
        ENNReal.ofReal (Real.rpow Δ (-48 * ε)) * (ENNReal.ofReal r) ^ s :=
      mul_le_mul_of_nonneg_right h_factor (by positivity)
    have h5 : ENNReal.ofReal (Real.rpow Δ (-25 * ε)) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber Δ.toNNReal slopeSet : ENNReal) ≤
        ENNReal.ofReal (Real.rpow Δ (-48 * ε)) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber Δ.toNNReal slopeSet : ENNReal) :=
      mul_le_mul_of_nonneg_right h51 (by positivity)
    exact le_trans h4 h5
  have hP_lower : ENNReal.ofReal (Real.rpow Δ (48 * ε - t)) ≤
      Metric.externalCoveringNumber Δ.toNNReal P_norm_set := by
    have hpack : ENNReal.ofReal (1 / 81 : ℝ) * ↑(P_norm.card) ≤
        Metric.externalCoveringNumber Δ.toNNReal P_norm_set :=
      ncover_lower_bound_separated81 hΔ_pos hP_norm_separated
    have hcard : (P_norm.card : ℝ) ≥ Real.rpow Δ (-t + 5 * ε) := by
      have h1 : (P_norm.card : ℝ) = (base.P_Q.card : ℝ) := by exact_mod_cast hP_norm_card
      rw [h1]; exact base.hP_Q_card_lower
    have h_rpow_nonneg : 0 ≤ Real.rpow Δ (-t + 5 * ε) := Real.rpow_nonneg (by linarith) _
    have h_small : (1 / 81 : ℝ) ≥ Real.rpow Δ (22 * ε) := by
      have h1 : Real.rpow Δ (22 * ε) ≤ Real.rpow Δ ε := by
        have h_exp : 22 * ε ≥ ε := by linarith
        have hΔ_le_one : Δ ≤ 1 := by linarith
        exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_le_one h_exp
      have h2 : Real.rpow Δ ε ≤ 1 / 81 := hΔ_small
      linarith
    have h_rpow_add : Real.rpow Δ (22 * ε) * Real.rpow Δ (-t + 5 * ε) =
        Real.rpow Δ ((22 * ε) + (-t + 5 * ε)) :=
      (Real.rpow_add hΔ_pos (22 * ε) (-t + 5 * ε)).symm
    have h_exp_eq27 : (22 * ε) + (-t + 5 * ε) = 27 * ε - t := by ring
    have h_main27 : (1 / 81 : ℝ) * (P_norm.card : ℝ) ≥ Real.rpow Δ (27 * ε - t) := by
      have h1 : (1 / 81 : ℝ) * (P_norm.card : ℝ) ≥
          Real.rpow Δ (22 * ε) * Real.rpow Δ (-t + 5 * ε) := by
        gcongr <;> linarith [h_rpow_nonneg]
      rw [h_rpow_add, h_exp_eq27] at h1; exact h1
    have h_weaken27_42 : Real.rpow Δ (27 * ε - t) ≥ Real.rpow Δ (48 * ε - t) := by
      have h_exp : 48 * ε - t ≥ 27 * ε - t := by linarith
      have hΔ_le_one : Δ ≤ 1 := by linarith
      have h : Real.rpow Δ (48 * ε - t) ≤ Real.rpow Δ (27 * ε - t) :=
        Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_le_one h_exp
      exact h
    have h_main : (1 / 81 : ℝ) * (P_norm.card : ℝ) ≥ Real.rpow Δ (48 * ε - t) :=
      le_trans h_weaken27_42 h_main27
    have h_enn : ENNReal.ofReal (Real.rpow Δ (48 * ε - t)) ≤
        ENNReal.ofReal ((1 / 81 : ℝ) * (P_norm.card : ℝ)) := by gcongr <;> exact h_main
    have h3 : ENNReal.ofReal (1 / 81 : ℝ) * (↑(P_norm.card) : ENNReal) =
        ENNReal.ofReal ((1 / 81 : ℝ) * (P_norm.card : ℝ)) := by
      have h4 : (↑(P_norm.card) : ENNReal) = ENNReal.ofReal (P_norm.card : ℝ) := by simp
      rw [h4, ← ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [h3] at hpack; exact le_trans h_enn hpack
  have hP_upper : Metric.externalCoveringNumber Δ.toNNReal P_norm_set ≤
      ENNReal.ofReal (Real.rpow Δ (-t - 48 * ε)) := by
    have h1 : Metric.externalCoveringNumber Δ.toNNReal P_norm_set ≤ ↑(P_norm.card) := by
      have h2 : P_norm_set.encard = ↑(P_norm.card) := by simp [P_norm_set] <;> rfl
      have h3 : Metric.externalCoveringNumber Δ.toNNReal P_norm_set ≤ P_norm_set.encard := by exact Metric.externalCoveringNumber_le_encard_self P_norm_set
      rw [h2] at h3; exact h3
    have h2 : (P_norm.card : ℝ) = (base.P_Q.card : ℝ) := by
      have h_inj : Function.Injective normalize := a4_normalize_injective Δ hΔ_pos z_Q
      simp [P_norm, Finset.card_image_of_injective _ h_inj]
    have h3 : (base.P_Q.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε) := base.hP_Q_card_upper
    have h4 : Real.rpow Δ (-t - 3 * ε) ≤ Real.rpow Δ (-t - 48 * ε) := by
      have h_exp : -t - 3 * ε ≥ -t - 48 * ε := by linarith
      have hΔ_le_one : Δ ≤ 1 := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_le_one h_exp
    have h5 : (Metric.externalCoveringNumber Δ.toNNReal P_norm_set : ENNReal) ≤
        ENNReal.ofReal (P_norm.card : ℝ) := by exact_mod_cast h1
    calc (Metric.externalCoveringNumber Δ.toNNReal P_norm_set : ENNReal)
      ≤ ENNReal.ofReal (P_norm.card : ℝ) := h5
    _ = ENNReal.ofReal (base.P_Q.card : ℝ) := by rw [h2]
    _ ≤ ENNReal.ofReal (Real.rpow Δ (-t - 3 * ε)) := by gcongr
    _ ≤ ENNReal.ofReal (Real.rpow Δ (-t - 48 * ε)) := by gcongr
  have hslope_lower : ENNReal.ofReal (Real.rpow Δ (48 * ε - s)) ≤
      Metric.externalCoveringNumber Δ.toNNReal slopeSet :=
    have h_weaken : ENNReal.ofReal (Real.rpow Δ (48 * ε - s)) ≤
        ENNReal.ofReal (Real.rpow Δ (25 * ε - s)) := by
      have h_exp : 48 * ε - s ≥ 25 * ε - s := by linarith
      have hΔ_le_one : Δ ≤ 1 := by linarith
      have h : Real.rpow Δ (48 * ε - s) ≤ Real.rpow Δ (25 * ε - s) :=
        Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_le_one h_exp
      exact ENNReal.ofReal_le_ofReal h
    le_trans h_weaken base.hC_Q_slope_cover_lower
  have hslope_upper : Metric.externalCoveringNumber Δ.toNNReal slopeSet ≤
      ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε)) :=
    hC_Q_slope_cover_upper

  let h_rkp_result := hRKP_at_Δ P_norm_set slopeSet hP_unit hslope_bounded
      hP_sset hslope_sset hP_lower hP_upper hslope_lower hslope_upper
  let goodDirections : Set ℝ := Classical.choose h_rkp_result
  have hgd_spec := Classical.choose_spec h_rkp_result
  have hgd_sub : goodDirections ⊆ slopeSet := hgd_spec.1
  have hgd_cover := hgd_spec.2.1
  have hgd_proj_raw : ∀ (σ : ℝ), σ ∈ goodDirections →
      ∀ (P' : Set Plane), P' ⊆ P_norm_set →
        ENNReal.ofReal (Real.rpow Δ (48 * ε)) * Metric.externalCoveringNumber Δ.toNNReal P_norm_set ≤
          Metric.externalCoveringNumber Δ.toNNReal P' →
        ∃ (X : Set ℝ),
          X ⊆ (fun p : Plane => p 0 - σ * p 1) '' P' ∧
          IsDeltaSSet Δ s (Real.rpow Δ (-576 * ε)) X ∧
          ENNReal.ofReal (Real.rpow Δ (576 * ε - s)) ≤
            Metric.externalCoveringNumber Δ.toNNReal X := by
    intro σ hσ P' hP'_sub hcover
    have h := hgd_spec.2.2 σ hσ P' hP'_sub (by simpa [Ncover] using hcover)
    rcases h with ⟨X, hX_sub, hX_sset, hX_lower⟩
    refine' ⟨X, _, hX_sset, _⟩
    · simpa [RobustKaufmanProjection.affineProjection] using hX_sub
    · exact hX_lower
  let C_Q_pi : Finset CoarseTube :=
    base.C_Q.filter (fun T => tubeSlope T ∈ goodDirections)
  have hC_Q_pi_sub : C_Q_pi ⊆ base.C_Q := Finset.filter_subset _ _
  have h_good_img : goodDirections ⊆ tubeSlope '' (C_Q_pi : Set CoarseTube) := by
    intro σ hσ
    have h1 : σ ∈ slopeSet := hgd_sub hσ
    rcases h1 with ⟨T, hT, rfl⟩
    have h2 : T ∈ C_Q_pi := by
      simp only [C_Q_pi, Finset.mem_filter]; exact ⟨hT, hσ⟩
    exact ⟨T, h2, rfl⟩
  have hC_Q_pi_card : (base.C_Q.card : ℝ) ≤
      Real.rpow Δ (-ε) * (C_Q_pi.card : ℝ) :=
    hC_Q_pi_card_main2 (hΔ_pos := hΔ_pos) (f := tubeSlope)
      (hC_Q_sep := base.hC_Q_separated) (hC_Q_pi_sub := hC_Q_pi_sub)
      (h_cover_transfer := base.hC_Q_cover_transfer) (h_rkp := hgd_cover)
      (h_good_img := h_good_img) (h_small := hΔ_small_pack)
  have hC_Q_pi_sset : IsDeltaSSet Δ s (Real.rpow Δ (-59 * ε)) (C_Q_pi : Set CoarseTube) :=
    hC_Q_pi_sset_main (hΔ_pos := hΔ_pos) (hε_pos := hε_pos) (hΔ_lt_one := by linarith [hΔ_lt_half])
      (f := tubeSlope) (hC_Q_sset := base.hC_Q_sset)
      (hC_Q_sep := base.hC_Q_separated) (hC_Q_pi_sub := hC_Q_pi_sub)
      (h_cover_transfer := base.hC_Q_cover_transfer) (h_rkp := hgd_cover)
      (h_good_img := h_good_img) (hC2_Q_loss := base.hC2_Q_loss)
      (h_small := by
        have h1 : (4000 : ENNReal) * (affinePackingM : ENNReal) ≤
            ENNReal.ofReal (Real.rpow Δ (-ε)) := hΔ_small_pack
        have h2 : Real.rpow Δ (-ε) ≤ Real.rpow Δ (-49 * ε) := by
          have h3 : -ε ≥ -49 * ε := by linarith
          have h4 : Δ ≤ 1 := by linarith [hΔ_lt_half]
          exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos h4 h3
        have h5 : 0 ≤ Real.rpow Δ (-49 * ε) := Real.rpow_nonneg (by linarith) _
        exact le_trans h1 ((ENNReal.ofReal_le_ofReal_iff h5).mpr h2))

  let projData : ∀ boldT ∈ C_Q_pi, ProjectionData Δ s ε P_norm boldT := by
    intro boldT hboldT
    have h_filter : boldT ∈ base.C_Q ∧ tubeSlope boldT ∈ goodDirections :=
      Finset.mem_filter.mp hboldT
    let σ := tubeSlope boldT
    have hσ_in : σ ∈ goodDirections := h_filter.2
    have h_base_cond : ENNReal.ofReal (Real.rpow Δ (48 * ε)) *
        Metric.externalCoveringNumber Δ.toNNReal P_norm_set ≤
        Metric.externalCoveringNumber Δ.toNNReal P_norm_set := by
      have h2 : Real.rpow Δ (48 * ε) ≤ 1 := Real.rpow_le_one hΔ_pos.le (by linarith) (by linarith)
      have h3 : ENNReal.ofReal (Real.rpow Δ (48 * ε)) ≤ 1 := ENNReal.ofReal_le_one.mpr (by linarith)
      simpa using mul_le_mul_of_nonneg_right h3 (by positivity)
    let h_exists_X := hgd_proj_raw σ hσ_in P_norm_set (by rfl) h_base_cond
    let X : Set ℝ := Classical.choose h_exists_X
    have hX_spec := Classical.choose_spec h_exists_X
    have hX_sub : X ⊆ (fun p : Plane => p 0 - σ * p 1) '' P_norm_set := hX_spec.1
    have hX_sset : IsDeltaSSet Δ s (Real.rpow Δ (-576 * ε)) X := hX_spec.2.1
    have hX_lower : ENNReal.ofReal (Real.rpow Δ (576 * ε - s)) ≤
        Metric.externalCoveringNumber Δ.toNNReal X := hX_spec.2.2
    let basic := a4_build_basic Δ s ε P_norm boldT σ (by simp [σ]) X hX_sub hX_sset hX_lower
    have h_robust : ∀ (P' : Finset Plane), P' ⊆ P_norm →
        Metric.externalCoveringNumber Δ.toNNReal (P_norm : Set Plane) ≤
          ENNReal.ofReal (Real.rpow Δ (-48 * ε)) *
            Metric.externalCoveringNumber Δ.toNNReal (P' : Set Plane) →
        BasicProjectionData Δ s ε P' boldT := by
      intro P' hP'_sub hcover
      set a := Metric.externalCoveringNumber Δ.toNNReal P_norm_set
      set c := Metric.externalCoveringNumber Δ.toNNReal (P' : Set Plane)
      set b25 := ENNReal.ofReal (Real.rpow Δ (-48 * ε))
      set d25 := ENNReal.ofReal (Real.rpow Δ (48 * ε))
      have hpos1 : 0 < Real.rpow Δ (-48 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have hpos2 : 0 < Real.rpow Δ (48 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have hmul : Real.rpow Δ (-48 * ε) * Real.rpow Δ (48 * ε) = 1 := by
        have hadd : Real.rpow Δ ((-48 * ε) + (48 * ε)) = Real.rpow Δ (-48 * ε) * Real.rpow Δ (48 * ε) :=
          Real.rpow_add hΔ_pos (-48 * ε) (48 * ε)
        have h2 : (-48 * ε) + (48 * ε) = 0 := by ring
        have h3 : Real.rpow Δ ((-48 * ε) + (48 * ε)) = 1 := by rw [h2] <;> simp
        rw [h3] at hadd; exact hadd.symm
      have hbd : b25 * d25 = 1 := by
        have h4 : b25 * d25 = ENNReal.ofReal (Real.rpow Δ (-48 * ε) * Real.rpow Δ (48 * ε)) := by
          rw [ENNReal.ofReal_mul] <;> exact hpos1.le
        rw [h4, hmul] <;> simp
      have h : a ≤ b25 * c := by simpa [b25] using hcover
      have h2 : d25 * a ≤ c := by
        have h21 : d25 * a ≤ d25 * (b25 * c) := by gcongr
        have h22 : d25 * (b25 * c) = c := by
          calc d25 * (b25 * c) = (d25 * b25) * c := by rw [mul_assoc]
            _ = (b25 * d25) * c := by rw [mul_comm d25 b25]
            _ = 1 * c := by rw [hbd]
            _ = c := by ring
        rw [h22] at h21; exact h21
      let h_exists' := hgd_proj_raw σ hσ_in (P' : Set Plane) (by simpa [P_norm_set] using hP'_sub) h2
      let X' : Set ℝ := Classical.choose h_exists'
      have hX'_spec := Classical.choose_spec h_exists'
      exact a4_build_basic Δ s ε P' boldT σ (by simp [σ]) X' hX'_spec.1 hX'_spec.2.1 hX'_spec.2.2
    exact { basic with h_robust := h_robust }

  exact
    { base := base
      z_Q := z_Q
      P_norm := P_norm
      hP_norm_card := hP_norm_card
      hP_norm_separated := hP_norm_separated
      hP_norm_bounded := hP_norm_bounded
      hP_norm_unnormalize := hP_norm_unnormalize
      C_Q_pi := C_Q_pi
      hC_Q_pi_sub := hC_Q_pi_sub
      hC_Q_pi_sset := hC_Q_pi_sset
      hC_Q_pi_card := hC_Q_pi_card
      projData := projData
      hC_card_upper := hC_card_upper
      hC_Q_slope_cover_upper := hC_Q_slope_cover_upper
      hH_Q_lower := hH_Q_lower }

def A4_rkp_refinement
    (Δ δ s t ε : ℝ) (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hΔ_small : Real.rpow Δ ε ≤ 1 / 81)
    (hΔ_small_pack : (4000 : ENNReal) * (affinePackingM : ENNReal) ≤
        ENNReal.ofReal (Real.rpow Δ (-ε)))
    (hδ_eq : δ = Δ ^ 2)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (hε_pos : 0 < ε)
    (ht : t ≤ 2)
    (hRKP_at_Δ : ∀ (P : Set Plane) (directions : Set ℝ),
      InUnitSquare P →
      directions ⊆ Set.Icc (-1 : ℝ) 1 →
      IsDeltaSSet Δ t (Real.rpow Δ (-48 * ε)) P →
      IsDeltaSSet Δ s (Real.rpow Δ (-48 * ε)) directions →
      ENNReal.ofReal (Real.rpow Δ (48 * ε - t)) ≤ Ncover Δ P →
      Ncover Δ P ≤ ENNReal.ofReal (Real.rpow Δ (-t - 48 * ε)) →
      ENNReal.ofReal (Real.rpow Δ (48 * ε - s)) ≤ Ncover Δ directions →
      Ncover Δ directions ≤ ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε)) →
      ∃ goodDirections : Set ℝ,
        goodDirections ⊆ directions ∧
        Ncover Δ directions ≤ 2 * Ncover Δ goodDirections ∧
        ∀ σ ∈ goodDirections,
          ∀ P' : Set Plane, P' ⊆ P →
            ENNReal.ofReal (Real.rpow Δ (48 * ε)) * Ncover Δ P ≤ Ncover Δ P' →
            ∃ X : Set ℝ,
              X ⊆ RobustKaufmanProjection.affineProjection σ P' ∧
              IsDeltaSSet Δ s (Real.rpow Δ (-576 * ε)) X ∧
              ENNReal.ofReal (Real.rpow Δ (576 * ε - s)) ≤ Ncover Δ X)
    (a3 : A3_Output Δ δ s t ε) :
    A4_Output Δ δ s t ε := by
  let Qset := a3.Qset
  let perSquare : ∀ Q ∈ Qset, A4_SquareData Δ δ s t ε Q :=
    fun Q hQ =>
      let base := a3.perSquare Q hQ
      a4_per_square_helper Δ δ s t ε hΔ_pos hΔ_lt_half hΔ_small hΔ_small_pack hδ_eq
        hs hs1 hst hε_pos ht hRKP_at_Δ Q base
        (a3.hC_card_upper Q hQ) (a3.hC_Q_slope_cover_upper Q hQ) (a3.hH_Q_lower Q hQ)
  exact
    { Qset := Qset
      perSquare := perSquare
      hQset_sset := a3.hQset_sset
      K_uniform := a3.K_uniform
      H_uniform := a3.H_uniform
      C2_uniform := a3.C2_uniform
      C_card_uniform := a3.C_card_uniform
      hK_loss := a3.hK_loss
      hC2_loss := a3.hC2_loss
      hH_uniform_lower := a3.hH_uniform_lower
      hH_uniform := a3.hH_uniform
      hC_card_lower := a3.hC_card_exp_lower
      hC_card_upper := a3.hC_card_exp_upper
      hC_card_uniform := a3.hC_card_uniform
      hQset_phys_growth := a3.hQset_phys_growth }

end DirecretisedFurstenbergEstimate.AppendixA4
