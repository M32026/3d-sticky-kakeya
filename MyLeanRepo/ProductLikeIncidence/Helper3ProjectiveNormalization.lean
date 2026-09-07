module

/-
# Helper 3: Projective Normalization

Standalone lemma for the projective normalization step
(Obligation3 projective transform + NormalizeAndExtract).

Takes endgame directions, energy set, coordinate energy bounds, and normalization
constants as explicit inputs. Produces projective transform F, transformed E3',
rounding, and extracted S1/S2/E3''.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.Obligation3ProjectiveTransform
public import MyLeanRepo.ProductLikeIncidence.NormalizeAndExtract
public import MyLeanRepo.ProductLikeIncidence.EnergyScaling
public import MyLeanRepo.ProductLikeIncidence.MeasureSupportHelpers
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Bornology

namespace ProductLikeIncidence.ProductReduction

private lemma helper3_riesz_eq (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {X : Type*} [MeasurableSpace X] [MetricSpace X] (ν : Measure X) :
    robust_projection_main.rieszEnergy α hδ ν = robust_projection.rieszEnergy α hδ ν := by
  rfl

/-- Transfer boundedness from `productLikeRealLineCopy A` to `A` via Lipschitz projection. -/
private lemma helper3_bounded_transfer (A : Set ℝ)
    (hA : Bornology.IsBounded (productLikeRealLineCopy A)) :
    Bornology.IsBounded A := by
  let π : EuclideanSpace ℝ (Fin 1) → ℝ := fun p => p 0
  have hπ_lip : LipschitzWith 1 π := by
    intro x y
    have h : |x 0 - y 0| ≤ ‖x - y‖ := by
      rw [EuclideanSpace.norm_eq]
      have h2 : |(x - y) 0| ^ 2 ≤ ∑ i : Fin 1, |(x - y) i| ^ 2 := by
        rw [Fin.sum_univ_one] <;> exact le_refl _
      have h3 : 0 ≤ |(x - y) 0| := by positivity
      exact Real.le_sqrt_of_sq_le h2
    have h_dist : dist (π x) (π y) ≤ dist x y := by
      simpa [π, dist_eq_norm, Real.norm_eq_abs] using h
    have h_edist : edist (π x) (π y) ≤ (↑(1 : NNReal) : ENNReal) * edist x y := by
      have h1 : edist (π x) (π y) ≤ edist x y := by
        rw [edist_dist, edist_dist]
        exact ENNReal.ofReal_le_ofReal h_dist
      have h2 : (↑(1 : NNReal) : ENNReal) * edist x y = edist x y := by simp
      rw [h2]
      exact h1
    exact h_edist
  have h_img_bdd : Bornology.IsBounded (π '' productLikeRealLineCopy A) := by
    have h : LipschitzWith 1 π := hπ_lip
    exact LipschitzWith.isBounded_image hπ_lip hA
  have h_img_eq : π '' productLikeRealLineCopy A = A := by
    ext z
    simp [π, productLikeRealLineCopy]
    <;> constructor
    · rintro ⟨p, hp, rfl⟩; exact hp
    · intro hz
      have h_main : z ∈ π '' productLikeRealLineCopy A := by
        simp only [π, Set.mem_image, productLikeRealLineCopy, Set.mem_setOf_eq]
        refine ⟨(WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => z), hz, ?_⟩
        simp
      exact h_main
  have h_final : Bornology.IsBounded A := by
    convert h_img_bdd using 1
    exact h_img_eq.symm
  exact h_final

/-- A bounded subset of the integer grid `δℤ` is finite. -/
private lemma helper3_bounded_grid_finite (δ : ℝ) (hδ_pos : 0 < δ)
    (A : Set ℝ) (hA_sub : A ⊆ productLikeIntegerGrid δ)
    (hA_bdd : Bornology.IsBounded A) : A.Finite := by
  by_cases hA_empty : A = ∅
  · rw [hA_empty]; exact Set.finite_empty
  · have hA_nonempty : A.Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hA_empty
    let x0 : ℝ := Classical.choose hA_nonempty
    have hx0 : x0 ∈ A := Classical.choose_spec hA_nonempty
    have h1 : ∃ (C : ℝ), ∀ (x : ℝ), x ∈ A → ∀ (y : ℝ), y ∈ A → dist x y ≤ C := by
      have h : Bornology.IsBounded A := hA_bdd
      exact Metric.isBounded_iff.mp hA_bdd
    rcases h1 with ⟨C, hC⟩
    let r : ℝ := max C 1
    have hr_pos : 0 < r := by positivity
    have hdist : ∀ (x : ℝ), x ∈ A → ∀ (y : ℝ), y ∈ A → dist x y ≤ r := by
      intro x hx y hy
      have h : dist x y ≤ C := hC x hx y hy
      exact le_trans h (le_max_left C 1)
    let c : ℝ := x0
    have h_sub : A ⊆ Metric.closedBall c r := by
      intro y hy
      have h3 : dist y c ≤ r := hdist y hy c hx0
      exact h3
    set M : ℝ := |c| + r with hM_def
    have h2 : ∀ y ∈ A, |y| ≤ M := by
      intro y hy
      have h3 : y ∈ Metric.closedBall c r := h_sub hy
      have h4 : dist y c ≤ r := h3
      have h5 : |y - c| ≤ r := h4
      calc |y|
        = |y - c + c| := by ring_nf
        _ ≤ |y - c| + |c| := by exact abs_add_le (y - c) c
        _ ≤ r + |c| := by linarith
        _ = M := by simp [hM_def] <;> ring
    set K : ℤ := Int.ceil (M / δ) with hK_def
    have hK_ge : (M / δ) ≤ (K : ℝ) := Int.le_ceil _
    have h_main : A ⊆ (fun k : ℤ => δ * (k : ℝ)) '' Set.Icc (-K) K := by
      intro x hx
      have hx_grid : x ∈ productLikeIntegerGrid δ := hA_sub hx
      rcases hx_grid with ⟨k, hk⟩
      have h4 : |δ * (k : ℝ)| ≤ M := by
        have h5 : |x| ≤ M := h2 x hx
        rw [hk] at h5; exact h5
      have h6 : δ * |(k : ℝ)| ≤ M := by
        have h7 : |δ * (k : ℝ)| = δ * |(k : ℝ)| := by rw [abs_mul, abs_of_pos hδ_pos]
        rw [h7] at h4; exact h4
      have h5 : |(k : ℝ)| ≤ M / δ := by
        have h8 : |(k : ℝ)| * δ ≤ M := by
          have h9 : |(k : ℝ)| * δ = δ * |(k : ℝ)| := by ring
          rw [h9]; exact h6
        calc |(k : ℝ)|
          = (|(k : ℝ)| * δ) / δ := by field_simp [hδ_pos.ne'] <;> ring
        _ ≤ M / δ := by gcongr
      have h5' : -(M / δ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ M / δ := by exact abs_le.mp h5
      have h7 : -(K : ℝ) ≤ (k : ℝ) := by
        have h8 : -(K : ℝ) ≤ -(M / δ) := by exact neg_le_neg hK_ge
        exact le_trans h8 h5'.1
      have h9 : (k : ℝ) ≤ (K : ℝ) := le_trans h5'.2 hK_ge
      have h11 : -K ≤ k := by exact_mod_cast h7
      have h12 : k ≤ K := by exact_mod_cast h9
      exact ⟨k, ⟨h11, h12⟩, Eq.symm hk⟩
    have h_fin : ((fun k : ℤ => δ * (k : ℝ)) '' Set.Icc (-K) K).Finite :=
      Set.Finite.image _ (Set.finite_Icc _ _)
    exact h_fin.subset h_main

lemma projective_normalization_helper
    {δ κ0 rho_sep : ℝ}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_le_one : δ ≤ 1) (hδ_lt_one : δ < 1)
    (hκ0_pos : 0 < κ0) (hκ0_le_one : κ0 ≤ 1)
    (θ1 θ2 θ3 : ℝ)
    (hθ1_lt_θ3 : θ1 < θ3) (hθ3_lt_θ2 : θ3 < θ2)
    (hθ1_in_Icc : θ1 ∈ Set.Icc (0 : ℝ) 1)
    (hθ2_in_Icc : θ2 ∈ Set.Icc (0 : ℝ) 1)
    (hθ3_in_Icc : θ3 ∈ Set.Icc (0 : ℝ) 1)
    (h_dir_sep13 : θ3 - θ1 ≥ δ ^ rho_sep)
    (h_dir_sep32 : θ2 - θ3 ≥ δ ^ rho_sep)
    (E3 : Set (EuclideanSpace ℝ (Fin 2)))
    (μE3 : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2)))
    (hμE3_prob : IsProbabilityMeasure μE3)
    (hE3_nonempty : E3.Nonempty)
    (hμE3_support : μE3.support = E3)
    (Pbar_param : Set (EuclideanSpace ℝ (Fin 2)))
    (hPbar_bounded : Bornology.IsBounded Pbar_param)
    (hE3_sub_Pbar : E3 ⊆ Pbar_param)
    (R : ℝ) (k_R : ℕ)
    (hR_eq_pow2 : R = (2 : ℝ) ^ k_R)
    (hR_ge1 : 1 ≤ R)
    (hPbar_Rbox : ∀ p ∈ Pbar_param, |p 0| ≤ R ∧ |p 1| ≤ R)
    (P_y : ℝ → Set (EuclideanSpace ℝ (Fin 2)))
    (hP_y_bdd : ∀ y, Bornology.IsBounded (P_y y))
    (Y : Set ℝ) (hY_fin : Y.Finite) (hY_nonempty : Y.Nonempty)
    (q_bad q_coord_energy q_norm_energy rho_sel : ℝ)
    (h_qcoord_pos : 0 < q_coord_energy)
    (h_qnorm_pos : 0 < q_norm_energy)
    (h_coord_energy0 : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
          ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1)) μE3) ≤
      ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))))
    (h_coord_energy1 : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
          ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1)) μE3) ≤
      ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))))
    (h_exp_le : q_bad + 6 * rho_sel + 2 * κ0 * rho_sep ≤ q_coord_energy)
    (C_energy C_extract : ℝ)
    (hC_energy_pos : 0 < C_energy)
    (hC_energy_large : (4 * R) ^ (2 * κ0) ≤ C_energy)
    (hC_extract_pos : 0 < C_extract)
    (hδ_kappa_small : δ ^ κ0 ≤ 1 / 128)
    (h_energy_absorb : C_energy * (δ / (4 * R)) ^ (-q_coord_energy) ≤
        (δ / (4 * R)) ^ (-q_norm_energy))
    (hC_extract_large : robust_projection_main.energyToLargeMassDeltaSetC
        (δ / (4 * R)) κ0
        ((3 : ℝ) ^ (2 * κ0) * (δ / (4 * R)) ^ (-q_norm_energy)) ≤ C_extract) :
    ∃ (F F_inv : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (x : ℝ → ℝ)
      (E3' : Set (EuclideanSpace ℝ (Fin 2)))
      (μE3' : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2)))
      (P_y' : ℝ → Set (EuclideanSpace ℝ (Fin 2)))
      (L_proj C_inv : ℝ)
      (round_fun : ℝ → ℝ)
      (S1 S2 : Set ℝ)
      (E3'' : Set (EuclideanSpace ℝ (Fin 2))),
      (∀ p, (F p) 0 = ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1) ∧
                (F p) 1 = ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1)) ∧
      (∀ p ∈ Pbar_param, F_inv (F p) = p) ∧
      (∀ p' ∈ F '' Pbar_param, F (F_inv p') = p') ∧
      E3' = F '' E3 ∧
      μE3' = Measure.map F μE3 ∧
      IsProbabilityMeasure μE3' ∧
      μE3'.support = E3' ∧
      E3'.Nonempty ∧
      (∀ y, P_y' y = F '' (P_y y)) ∧
      (∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y))) ∧
      (∀ y, y ≠ θ2 →
        affineProjection (x y) E3' =
          scaleSet (((θ2 - θ3) / (θ2 - θ1)) / ((θ2 - y) / (θ2 - θ1)))
            (affineProjection y E3)) ∧
      0 ≤ L_proj ∧
      (∀ u v, dist (F u) (F v) ≤ L_proj * dist u v) ∧
      0 ≤ C_inv ∧
      C_inv ≤ 4 * Real.sqrt 2 * δ ^ (-rho_sep) ∧
      (∀ u v, dist (F_inv u) (F_inv v) ≤ C_inv * dist u v) ∧
      (∀ z, |z - round_fun z| ≤ δ / 2) ∧
      (∀ z, round_fun z ∈ productLikeIntegerGrid δ) ∧
      S1 ⊆ productLikeIntegerGrid δ ∧
      S2 ⊆ productLikeIntegerGrid δ ∧
      (∀ a ∈ S1, ∀ b ∈ S1, a ≠ b → |a - b| ≥ δ) ∧
      (∀ a ∈ S2, ∀ b ∈ S2, a ≠ b → |a - b| ≥ δ) ∧
      S1 ⊆ Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round_fun (p 0)) E3' ∧
      S2 ⊆ Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round_fun (p 1)) E3' ∧
      IsProductLikeRealDeltaSCSet δ κ0 C_extract S1 ∧
      IsProductLikeRealDeltaSCSet δ κ0 C_extract S2 ∧
      S1.Finite ∧ S2.Finite ∧ S1.Nonempty ∧ S2.Nonempty ∧
      E3'' ⊆ E3' ∧
      μE3' E3'' ≥ ENNReal.ofReal (1 / 2 : ℝ) ∧
      (∀ p ∈ E3'', round_fun (p 0) ∈ S1 ∧ round_fun (p 1) ∈ S2) := by
  let R_norm : ℝ := 2 * R
  let L_norm : ℝ := 4 * R
  let k_norm : ℕ := k_R + 2
  have hL_norm_eq : L_norm = (2 : ℝ) ^ k_norm := by
    simp [R_norm, L_norm, k_norm, hR_eq_pow2, pow_succ] <;> ring
  have hL_norm_2R : L_norm = 2 * R_norm := by simp [R_norm, L_norm] <;> ring
  have hR_norm_pos : 0 < R_norm := by positivity
  have hL_norm_pos : 0 < L_norm := by positivity
  have hL_norm_ge1 : 1 ≤ L_norm := by simp [L_norm, R_norm] <;> linarith [hR_ge1]
  have hR_norm_int : ∃ (c : ℤ), R_norm = (c : ℝ) := by
    have h : R_norm = 2 * R := by rfl
    rw [h, hR_eq_pow2]; refine ⟨(2 : ℤ) ^ (k_R + 1), ?_⟩; simp [pow_succ] <;> ring

  -- Uniform ν_Y on Y
  let Y_finset : Finset ℝ := hY_fin.toFinset
  have hY_finset_coe : (Y_finset : Set ℝ) = Y := hY_fin.coe_toFinset
  have hY_finset_nonempty : Y_finset.Nonempty := by
    have h : (Y_finset : Set ℝ).Nonempty := by rw [hY_finset_coe]; exact hY_nonempty
    exact (Finite.toFinset_nonempty hY_fin).mpr hY_nonempty
  let ν_Y : Measure ℝ := ∑ y ∈ Y_finset, (1 / (Y_finset.card : ENNReal)) • Measure.dirac y
  have hν_Y_prob : IsProbabilityMeasure ν_Y := by
    refine' ⟨_⟩
    have hcard_pos : 0 < Y_finset.card := Finset.card_pos.mpr hY_finset_nonempty
    have hne : (Y_finset.card : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr hcard_pos.ne'
    have htop : (Y_finset.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top Y_finset.card
    have h : ν_Y Set.univ = 1 := by
      simp [ν_Y, Finset.sum_apply, hcard_pos.ne']
      <;> exact ENNReal.mul_inv_cancel hne htop
    exact h
  have hν_Y_supp : ν_Y.support ⊆ Y := by
    have h1 : ν_Y.support = (Y_finset : Set ℝ) := support_uniform_finset hY_finset_nonempty
    rw [h1, hY_finset_coe] <;> exact Set.Subset.refl _
  letI : IsProbabilityMeasure ν_Y := hν_Y_prob
  letI : IsProbabilityMeasure μE3 := hμE3_prob

  -- Obligation3
  rcases obligation3_projective_transform_all
      (rho_sep := rho_sep) (hδ_pos := hδ_pos) (_hδ_lt_one := hδ_lt_one)
      (_hkappa_pos := hκ0_pos) (Pbar := Pbar_param) (E3 := E3) (μE3 := μE3)
      (Y := Y) (ν_Y := ν_Y) (P_y := P_y)
      (hθ1_lt_θ3 := hθ1_lt_θ3) (hθ3_lt_θ2 := hθ3_lt_θ2)
      (hθ1_in_unit := hθ1_in_Icc) (hθ2_in_unit := hθ2_in_Icc)
      (hθ3_in_unit := hθ3_in_Icc)
      (hPbar_bounded := hPbar_bounded) (hE3_sub_Pbar := hE3_sub_Pbar)
      (hE3_bounded := hPbar_bounded.subset hE3_sub_Pbar)
      (hμE3_support := hμE3_support) (hE3_nonempty := hE3_nonempty)
      (hP_y_bdd := hP_y_bdd)
      (h_dir_sep13 := h_dir_sep13) (h_dir_sep32 := h_dir_sep32)
      (hν_Y_supp := hν_Y_supp)
    with ⟨F, F_inv, x, _Pbar', E3', μE3', P_y', L_proj, C_inv,
      _C_q0, _C_q1, _C_q01, _E_q0, _E_q1, h_all⟩

  rcases h_all with ⟨hPbar'_eq, hE3'_eq, hμE3'_eq, hPy'_eq, hF_formula,
    hF_inv1, hF_inv2, hE3'_nonempty, hμE3'_prob, hμE3'_supp,
    hx_formula, _h_fl, h_proj_id,
    hL_proj_nonneg, hF_lip, hC_inv_nonneg, hC_inv_le, hF_inv_lip, _rest⟩
  letI : IsProbabilityMeasure μE3' := hμE3'_prob

  -- F is continuous (hence measurable) from the Lipschitz bound
  have hF_cont : Continuous F := by
    have h_uc : UniformContinuous F := by
      rw [Metric.uniformContinuous_iff]
      intro ε hε
      use ε / (L_proj + 1)
      constructor
      · positivity
      · intro x y hxy
        have hpos : 0 < L_proj + 1 := by linarith
        calc dist (F x) (F y) ≤ L_proj * dist x y := hF_lip x y
          _ ≤ L_proj * (ε / (L_proj + 1)) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hL_proj_nonneg
          _ = (L_proj * ε) / (L_proj + 1) := by field_simp [hpos.ne'] <;> ring
          _ < ε := by
            have h : L_proj * ε < (L_proj + 1) * ε := by gcongr <;> linarith
            have h2 : (L_proj * ε) / (L_proj + 1) < ((L_proj + 1) * ε) / (L_proj + 1) := by gcongr
            have h3 : ((L_proj + 1) * ε) / (L_proj + 1) = ε := by field_simp [hpos.ne'] <;> ring
            rw [h3] at h2; exact h2
    exact h_uc.continuous
  have hF_meas : Measurable F := hF_cont.measurable

  -- E3' bound
  have hE3'_bound : ∀ p ∈ E3', |p 0| ≤ R_norm ∧ |p 1| ≤ R_norm := by
    intro p hp
    have hp' : p ∈ F '' E3 := by rw [hE3'_eq] at hp; exact hp
    rcases hp' with ⟨q, hq, rfl⟩
    have hq_Pbar : q ∈ Pbar_param := hE3_sub_Pbar hq
    have hq_bounds : |q 0| ≤ R ∧ |q 1| ≤ R := hPbar_Rbox q hq_Pbar
    have hθ2_abs : |θ2| ≤ 1 := by
      have h1 : 0 ≤ θ2 := hθ2_in_Icc.1
      have h2 : θ2 ≤ 1 := hθ2_in_Icc.2
      rw [abs_of_nonneg h1]; exact h2
    have hθ1_abs : |θ1| ≤ 1 := by
      have h1 : 0 ≤ θ1 := hθ1_in_Icc.1
      have h2 : θ1 ≤ 1 := hθ1_in_Icc.2
      rw [abs_of_nonneg h1]; exact h2
    have hb3 : |((θ3 - θ1) / (θ2 - θ1))| ≤ 1 := by
      have h_pos : 0 < θ2 - θ1 := by linarith [hθ1_lt_θ3, hθ3_lt_θ2]
      have h_nonneg : 0 ≤ (θ3 - θ1) / (θ2 - θ1) := by positivity
      have h_le : (θ3 - θ1) / (θ2 - θ1) ≤ 1 := by
        apply (div_le_one h_pos).mpr; linarith [hθ1_lt_θ3, hθ3_lt_θ2]
      rw [abs_of_nonneg h_nonneg]; linarith
    have ha3 : |((θ2 - θ3) / (θ2 - θ1))| ≤ 1 := by
      have h_pos : 0 < θ2 - θ1 := by linarith [hθ1_lt_θ3, hθ3_lt_θ2]
      have h_nonneg : 0 ≤ (θ2 - θ3) / (θ2 - θ1) := by positivity
      have h_le : (θ2 - θ3) / (θ2 - θ1) ≤ 1 := by
        apply (div_le_one h_pos).mpr; linarith [hθ1_lt_θ3, hθ3_lt_θ2]
      rw [abs_of_nonneg h_nonneg]; linarith
    have h0 : |(F q) 0| ≤ R_norm := by
      have h1 : (F q) 0 = ((θ3 - θ1) / (θ2 - θ1)) * (q 0 * θ2 + q 1) := (hF_formula q).1
      rw [h1]
      have h_tri : |q 0 * θ2 + q 1| ≤ |q 0| * |θ2| + |q 1| := by
        calc |q 0 * θ2 + q 1| ≤ |q 0 * θ2| + |q 1| := by exact abs_add_le (q.ofLp 0 * θ2) (q.ofLp 1)
             _ = |q 0| * |θ2| + |q 1| := by rw [abs_mul]
      calc |((θ3 - θ1) / (θ2 - θ1)) * (q 0 * θ2 + q 1)|
        = |(θ3 - θ1) / (θ2 - θ1)| * |q 0 * θ2 + q 1| := by rw [abs_mul]
      _ ≤ 1 * |q 0 * θ2 + q 1| := by gcongr <;> exact hb3
      _ = |q 0 * θ2 + q 1| := by ring
      _ ≤ |q 0| * |θ2| + |q 1| := by simpa using h_tri
      _ ≤ R * 1 + R := by have hq0 : |q 0| ≤ R := hq_bounds.1; have hq1 : |q 1| ≤ R := hq_bounds.2; gcongr <;> linarith [hθ2_abs]
      _ = R_norm := by simp [R_norm] <;> ring
    have h2 : |(F q) 1| ≤ R_norm := by
      have h3 : (F q) 1 = ((θ2 - θ3) / (θ2 - θ1)) * (q 0 * θ1 + q 1) := (hF_formula q).2
      rw [h3]
      have h_tri2 : |q 0 * θ1 + q 1| ≤ |q 0| * |θ1| + |q 1| := by
        calc |q 0 * θ1 + q 1| ≤ |q 0 * θ1| + |q 1| := by exact abs_add_le (q.ofLp 0 * θ1) (q.ofLp 1)
             _ = |q 0| * |θ1| + |q 1| := by rw [abs_mul]
      calc |((θ2 - θ3) / (θ2 - θ1)) * (q 0 * θ1 + q 1)|
        = |(θ2 - θ3) / (θ2 - θ1)| * |q 0 * θ1 + q 1| := by rw [abs_mul]
      _ ≤ 1 * |q 0 * θ1 + q 1| := by gcongr <;> exact ha3
      _ = |q 0 * θ1 + q 1| := by ring
      _ ≤ |q 0| * |θ1| + |q 1| := h_tri2
      _ ≤ R * 1 + R := by have hq0 : |q 0| ≤ R := hq_bounds.1; have hq1 : |q 1| ≤ R := hq_bounds.2; gcongr <;> linarith [hθ1_abs]
      _ = R_norm := by simp [R_norm] <;> ring
    exact ⟨h0, h2⟩

  -- Energy scaling
  have h_real_ineq : δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep)) ≤
      (δ / L_norm) ^ (-q_coord_energy) := by
    have h1 : 0 < δ / L_norm := by positivity
    have h2 : δ / L_norm ≤ δ := by
      have hL_ge1 : 1 ≤ L_norm := hL_norm_ge1
      have h : δ / L_norm ≤ δ / 1 := by gcongr
      simpa using h
    have h3 : δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep)) ≤ δ ^ (-q_coord_energy) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le (by linarith [h_exp_le])
    have hq_pos : 0 < q_coord_energy := h_qcoord_pos
    have h5 : (δ / L_norm) ^ q_coord_energy ≤ δ ^ q_coord_energy := by
      gcongr <;> linarith
    have h6 : 0 < (δ / L_norm) ^ q_coord_energy := by positivity
    have h7 : 0 < δ ^ q_coord_energy := by positivity
    have h8 : (δ ^ q_coord_energy)⁻¹ ≤ ((δ / L_norm) ^ q_coord_energy)⁻¹ := by
      gcongr
      <;> linarith
    have h9 : δ ^ (-q_coord_energy) = (δ ^ q_coord_energy)⁻¹ := by
      rw [Real.rpow_neg (by linarith)] <;> ring
    have h10 : (δ / L_norm) ^ (-q_coord_energy) = ((δ / L_norm) ^ q_coord_energy)⁻¹ := by
      rw [Real.rpow_neg (by linarith)] <;> ring
    have h4 : δ ^ (-q_coord_energy) ≤ (δ / L_norm) ^ (-q_coord_energy) := by
      rw [h9, h10]; exact h8
    exact le_trans h3 h4

  have h_energy_x_norm : robust_projection_main.rieszEnergy (2 * κ0) (div_pos hδ_pos hL_norm_pos)
      (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => normalizeMap R_norm L_norm (p 0)) μE3') ≤
    ENNReal.ofReal (C_energy * (δ / L_norm) ^ (-q_coord_energy)) := by
    rw [helper3_riesz_eq (2 * κ0) (div_pos hδ_pos hL_norm_pos) _]
    have h_scale := rieszEnergy_normalizeMap_scaling (α := 2 * κ0) (hδ := hδ_pos) (hL_pos := hL_norm_pos)
      (R := R_norm) (L := L_norm)
      (h := fun p : EuclideanSpace ℝ (Fin 2) => p 0) (hh_meas := by fun_prop) (μ := μE3')
    have h_scale' : robust_projection.rieszEnergy (2 * κ0) (div_pos hδ_pos hL_norm_pos)
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => normalizeMap R_norm L_norm (p 0)) μE3') =
        ENNReal.ofReal (L_norm ^ (2 * κ0)) * robust_projection.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0) μE3') := by
      exact h_scale
    rw [h_scale']
    have h_meas_eq : Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0) μE3' =
        Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
          ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1)) μE3 := by
      have h_proj0_meas : Measurable (fun p : EuclideanSpace ℝ (Fin 2) => p 0) := by fun_prop
      have h_func : (fun p : EuclideanSpace ℝ (Fin 2) => p 0) ∘ F =
          (fun p : EuclideanSpace ℝ (Fin 2) =>
            ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1)) := by
        funext p
        exact (hF_formula p).1
      rw [hμE3'_eq, Measure.map_map h_proj0_meas hF_meas, h_func]
    rw [h_meas_eq]
    have h_bound : robust_projection.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
          ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1)) μE3) ≤
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) := by
      have h_eq := helper3_riesz_eq (2 * κ0) hδ_pos
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
          ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1)) μE3)
      rw [←h_eq]
      exact h_coord_energy0
    have h_mul : ENNReal.ofReal (L_norm ^ (2 * κ0)) *
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) ≤
      ENNReal.ofReal (C_energy * (δ / L_norm) ^ (-q_coord_energy)) := by
      have h_pos1 : 0 ≤ C_energy := hC_energy_pos.le
      have h_pos2 : 0 ≤ (δ / L_norm) ^ (-q_coord_energy) := by positivity
      have h_rhs : ENNReal.ofReal (C_energy * (δ / L_norm) ^ (-q_coord_energy)) =
          ENNReal.ofReal C_energy * ENNReal.ofReal ((δ / L_norm) ^ (-q_coord_energy)) := by
        rw [ENNReal.ofReal_mul h_pos1]
      have hC_large : L_norm ^ (2 * κ0) ≤ C_energy := by
        have h_eq : L_norm = 4 * R := by simp [L_norm, R_norm]
        rw [h_eq]
        exact hC_energy_large
      rw [h_rhs]
      have h : ENNReal.ofReal (L_norm ^ (2 * κ0)) ≤ ENNReal.ofReal C_energy :=
        ENNReal.ofReal_le_ofReal hC_large
      have h' : ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) ≤
          ENNReal.ofReal ((δ / L_norm) ^ (-q_coord_energy)) :=
        ENNReal.ofReal_le_ofReal h_real_ineq
      exact mul_le_mul' h h'
    exact le_trans (mul_le_mul_left' h_bound _) h_mul

  have h_energy_y_norm : robust_projection_main.rieszEnergy (2 * κ0) (div_pos hδ_pos hL_norm_pos)
      (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => normalizeMap R_norm L_norm (p 1)) μE3') ≤
    ENNReal.ofReal (C_energy * (δ / L_norm) ^ (-q_coord_energy)) := by
    rw [helper3_riesz_eq (2 * κ0) (div_pos hδ_pos hL_norm_pos) _]
    have h_scale := rieszEnergy_normalizeMap_scaling (α := 2 * κ0) (hδ := hδ_pos) (hL_pos := hL_norm_pos)
      (R := R_norm) (L := L_norm)
      (h := fun p : EuclideanSpace ℝ (Fin 2) => p 1) (hh_meas := by fun_prop) (μ := μE3')
    have h_scale' : robust_projection.rieszEnergy (2 * κ0) (div_pos hδ_pos hL_norm_pos)
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => normalizeMap R_norm L_norm (p 1)) μE3') =
        ENNReal.ofReal (L_norm ^ (2 * κ0)) * robust_projection.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 1) μE3') := by
      exact h_scale
    rw [h_scale']
    have h_meas_eq : Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 1) μE3' =
        Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
          ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1)) μE3 := by
      have h_proj1_meas : Measurable (fun p : EuclideanSpace ℝ (Fin 2) => p 1) := by fun_prop
      have h_func : (fun p : EuclideanSpace ℝ (Fin 2) => p 1) ∘ F =
          (fun p : EuclideanSpace ℝ (Fin 2) =>
            ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1)) := by
        funext p
        exact (hF_formula p).2
      rw [hμE3'_eq, Measure.map_map h_proj1_meas hF_meas, h_func]
    have h_bound : robust_projection.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
          ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1)) μE3) ≤
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) := by
      exact h_coord_energy1
    have h_main : robust_projection.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 1) μE3') ≤
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) := by
      rw [h_meas_eq]
      exact h_bound
    have h_mul : ENNReal.ofReal (L_norm ^ (2 * κ0)) *
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) ≤
      ENNReal.ofReal (C_energy * (δ / L_norm) ^ (-q_coord_energy)) := by
      have h_pos1 : 0 ≤ C_energy := hC_energy_pos.le
      have h_pos2 : 0 ≤ (δ / L_norm) ^ (-q_coord_energy) := by positivity
      have h_rhs : ENNReal.ofReal (C_energy * (δ / L_norm) ^ (-q_coord_energy)) =
          ENNReal.ofReal C_energy * ENNReal.ofReal ((δ / L_norm) ^ (-q_coord_energy)) := by
        rw [ENNReal.ofReal_mul h_pos1]
      have hC_large : L_norm ^ (2 * κ0) ≤ C_energy := by
        have h_eq : L_norm = 4 * R := by simp [L_norm, R_norm]
        rw [h_eq]
        exact hC_energy_large
      rw [h_rhs]
      have h : ENNReal.ofReal (L_norm ^ (2 * κ0)) ≤ ENNReal.ofReal C_energy :=
        ENNReal.ofReal_le_ofReal hC_large
      have h' : ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) ≤
          ENNReal.ofReal ((δ / L_norm) ^ (-q_coord_energy)) :=
        ENNReal.ofReal_le_ofReal h_real_ineq
      exact mul_le_mul' h h'
    exact le_trans (mul_le_mul_left' h_main _) h_mul

  have h_energy_absorb' : C_energy * (δ / L_norm) ^ (-q_coord_energy) ≤
      (δ / L_norm) ^ (-q_norm_energy) := by
    have h_eq : δ / L_norm = δ / (4 * R) := by
      have h : L_norm = 4 * R := by simp [L_norm, R_norm]
      rw [h]
    rw [h_eq]
    exact h_energy_absorb

  have hC_extract_large' : robust_projection_main.energyToLargeMassDeltaSetC
      (δ / L_norm) κ0
      ((3 : ℝ) ^ (2 * κ0) * (δ / L_norm) ^ (-q_norm_energy)) ≤ C_extract := by
    have h_eq : δ / L_norm = δ / (4 * R) := by
      have h : L_norm = 4 * R := by simp [L_norm, R_norm]
      rw [h]
    rw [h_eq]
    exact hC_extract_large

  -- Normalize and extract
  rcases normalize_and_extract
      (hδ_pos := hδ_pos) (hδ_dyadic := hδ_dyadic) (hδ_le_one := hδ_lt_one.le)
      (hkappa_pos := hκ0_pos) (hκ0_le_one := hκ0_le_one)
      (hη_total_pos := h_qcoord_pos) (hη_energy_pos := h_qnorm_pos)
      (hδ_kappa_small := hδ_kappa_small)
      (hC_extract_pos := hC_extract_pos)
      (R := R_norm) (L := L_norm) (k := k_norm)
      (hR_pos := hR_norm_pos) (hL := hL_norm_eq) (hL_2R := hL_norm_2R)
      (hL_pos := hL_norm_pos) (hR_int := hR_norm_int)
      (h_energy_absorb := h_energy_absorb')
      (hC_extract_large := hC_extract_large')
      (hE3'_supp := hμE3'_supp)
      (h_bound := hE3'_bound)
      (h_energy_x_norm := h_energy_x_norm)
      (h_energy_y_norm := h_energy_y_norm)
    with ⟨round_fun, S1, S2, E3'',
      h_round_near, hround_grid, hS1_grid, hS2_grid,
      hS1_sep, hS2_sep,
      hS1_sub_img, hS2_sub_img,
      hS1_delta, hS2_delta,
      hE3''_sub, hE3''_mass, hE3''_round⟩

  -- Transfer boundedness from productLikeRealLineCopy A to A
  have h_bdd_transfer : ∀ (A : Set ℝ),
      Bornology.IsBounded (productLikeRealLineCopy A) → Bornology.IsBounded A :=
    fun A hA => helper3_bounded_transfer A hA

  have hS1_bdd : Bornology.IsBounded S1 := h_bdd_transfer S1 hS1_delta.1
  have hS2_bdd : Bornology.IsBounded S2 := h_bdd_transfer S2 hS2_delta.1

  have h_grid_finite_of_bdd : ∀ (A : Set ℝ), A ⊆ productLikeIntegerGrid δ →
      Bornology.IsBounded A → A.Finite :=
    fun A hA_sub hA_bdd => helper3_bounded_grid_finite δ hδ_pos A hA_sub hA_bdd

  have hS1_finite : S1.Finite := h_grid_finite_of_bdd S1 hS1_grid hS1_bdd
  have hS2_finite : S2.Finite := h_grid_finite_of_bdd S2 hS2_grid hS2_bdd

  have hS1_nonempty : S1.Nonempty := by
    have h : (productLikeRealLineCopy S1).Nonempty := hS1_delta.2.1
    rcases h with ⟨x, hx⟩
    exact ⟨x 0, hx⟩
  have hS2_nonempty : S2.Nonempty := by
    have h : (productLikeRealLineCopy S2).Nonempty := hS2_delta.2.1
    rcases h with ⟨x, hx⟩
    exact ⟨x 0, hx⟩

  have hF_inv2' : ∀ p' ∈ F '' Pbar_param, F (F_inv p') = p' := by
    rw [←hPbar'_eq]
    exact hF_inv2

  exact ⟨F, F_inv, x, E3', μE3', P_y', L_proj, C_inv, round_fun, S1, S2, E3'',
    hF_formula, hF_inv1, hF_inv2', hE3'_eq, hμE3'_eq, hμE3'_prob, hμE3'_supp,
    hE3'_nonempty, hPy'_eq, hx_formula, h_proj_id,
    hL_proj_nonneg, hF_lip, hC_inv_nonneg, hC_inv_le, hF_inv_lip,
    h_round_near, hround_grid, hS1_grid, hS2_grid,
    hS1_sep, hS2_sep,
    hS1_sub_img, hS2_sub_img, hS1_delta, hS2_delta,
    hS1_finite, hS2_finite, hS1_nonempty, hS2_nonempty,
    hE3''_sub, hE3''_mass, hE3''_round⟩

end ProductLikeIncidence.ProductReduction
