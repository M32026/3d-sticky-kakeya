module

/-
# Glue H3→H4: Admission-Free Composition Theorem

Wires Helper3 (projective normalization) outputs through bridge lemmas and
supplements into Helper4 (dense graph) exact inputs.

## What this theorem proves

Given:
- Helper3's full existential output (F, F_inv, E3', μE3', round_fun, S1, S2, E3'', etc.)
- Upstream Helper2 data (E3fin, E3 size, direction projection bounds, per-cube occupancy)
- Uniform measure on E3
- C_extract from Bridge H2→H3
- Helper4 parameters (c_dense, absorption threshold)

Produces every input required by `dense_graph_helper`, including:
- E3' finiteness, size, half-size E3''
- Occupancy bound with M_G_real ≤ 1024 · δ^{-2ρ_sep}
- Coordinate projection bounds (factor 2) via scalar_covering_upper
- Exact third-projection identity (q0+q1 = π_{θ3})
- S1/S2 rounding covering bounds (factor 3)
- Pbar construction containing both Pbar_param and E3'

## Key gap-fill strategies

1. **Projection bounds**: Helper3 discards Obligation3's `C_q0=C_q1=2` bounds.
   We re-prove them from the F formula:
   - coord0(E3') = scaleSet b3 · π_{θ2}(E3), b3 ≤ 1 ⇒ factor 2
   - coord1(E3') = scaleSet a3 · π_{θ1}(E3), a3 ≤ 1 ⇒ factor 2
   - coord0+coord1(E3') = π_{θ3}(E3) exactly ⇒ factor 1

2. **Occupancy**: `occupancy_from_inv_lipschitz` with L = C_inv + 1 gives
   per-cube bound `(2·L·√2+6)²`, matching M_G_real.

3. **Uniform measure**: If μE3 is uniform on finite E3, then μE3' = map F μE3
   is uniform on E3' (F injective on E3 via F_inv left-inverse).

## Dependencies (all in repository)
- `CoreDefinitions`, `ProjectionBasic`, `ProductLikeBasic`
- `BoundedOccupancy` (`occupancy_from_inv_lipschitz`)
- `BasicUtilities` (`rounded_projection_bound`)
- `FourSectorChart` (`scalar_covering_upper`)
- Mathlib

## Whiteprint node
Glue theorem composing Helper3 → Bridge → Supplements → Helper4.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.BoundedOccupancy
public import MyLeanRepo.ProductLikeIncidence.BasicUtilities
public import MyLeanRepo.ProductLikeIncidence.FourSectorChart
public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal MeasureTheory Classical Finset

namespace ProductLikeIncidence.ProductReduction

/-! ========================================================================
   Private helper lemmas
   ======================================================================== -/

/-- Evaluate a sum of weighted Dirac measures on a measurable set. -/
private lemma glue_sum_dirac_apply {α : Type*} [MeasurableSpace α]
    (S : Finset α) (c : ENNReal) {A : Set α} (hA : MeasurableSet A) :
    (∑ p ∈ S, c • Measure.dirac p) A = c * (S.filter (· ∈ A)).card := by
  rw [Measure.finsetSum_apply]
  have h1 : ∑ p ∈ S, (c • Measure.dirac p) A = c * ∑ p ∈ S, (Measure.dirac p A) := by
    rw [Finset.mul_sum] <;> rfl
  rw [h1]
  have h2 : ∑ p ∈ S, (Measure.dirac p A) = (S.filter (· ∈ A)).card := by
    have h3 : ∀ p ∈ S, Measure.dirac p A = if p ∈ A then (1 : ENNReal) else 0 := by
      intro p _
      rw [Measure.dirac_apply' p hA]
      simp [Set.indicator_apply] <;> split_ifs <;> simp
    rw [Finset.sum_congr rfl h3]
    have h4 : ∑ p ∈ S, (if p ∈ A then (1 : ENNReal) else 0) = (S.filter (· ∈ A)).card := by
      rw [Finset.sum_ite] <;> simp
    exact h4
  rw [h2] <;> rfl

/-- Uniform measure mass ≥ 1/2 implies encard ≥ half. -/
private lemma glue_mass_half_to_encard
    {E3' E3'' : Set (EuclideanSpace ℝ (Fin 2))}
    {μE3' : Measure (EuclideanSpace ℝ (Fin 2))}
    (hE3'_fin : E3'.Finite)
    (hE3'_nonempty : E3'.Nonempty)
    (hμE3'_uniform : μE3' = ∑ p ∈ hE3'_fin.toFinset,
        (1 / ENat.toENNReal E3'.encard) • Measure.dirac p)
    (hE3''_sub : E3'' ⊆ E3')
    (h_mass : μE3' E3'' ≥ ENNReal.ofReal (1 / 2 : ℝ)) :
    ENat.toENNReal E3''.encard ≥ ENat.toENNReal E3'.encard / 2 := by
  let S : Finset _ := hE3'_fin.toFinset
  have hE3''_fin : E3''.Finite := hE3'_fin.subset hE3''_sub
  let S'' : Finset _ := hE3''_fin.toFinset
  have hS : (S : Set _) = E3' := Finite.coe_toFinset hE3'_fin
  have hS'' : (S'' : Set _) = E3'' := Finite.coe_toFinset hE3''_fin
  have h_filter : S.filter (· ∈ E3'') = S'' := by
    ext x; simp only [Finset.mem_filter, hS''] <;> aesop
  have h_card' : ENat.toENNReal E3'.encard = (S.card : ENNReal) := by
    have h1 : E3'.encard = S.card := by rw [← hS] <;> simp
    rw [h1] <;> simp
  have h_card'' : ENat.toENNReal E3''.encard = (S''.card : ENNReal) := by
    have h1 : E3''.encard = S''.card := by rw [← hS''] <;> simp
    rw [h1] <;> simp
  have h_eval : μE3' E3'' = (S''.card : ENNReal) / (S.card : ENNReal) := by
    rw [hμE3'_uniform, h_card']
    have hA : MeasurableSet E3'' := hE3''_fin.measurableSet
    have h_sum := glue_sum_dirac_apply (A := E3'') S (1 / (S.card : ENNReal)) hA
    rw [h_sum, h_filter] <;> simp [div_eq_mul_inv] <;> ring
  rw [h_eval] at h_mass
  rw [h_card'', h_card']
  have hne : S.Nonempty := by
    have h : (↑S : Set (EuclideanSpace ℝ (Fin 2))).Nonempty := by
      rw [hS]; exact hE3'_nonempty
    simpa [Finset.coe_nonempty] using h
  have h_pos : (S.card : ENNReal) ≠ 0 := by
    have h : S.card ≠ 0 := Finset.card_ne_zero.mpr hne
    exact_mod_cast h
  have h_main : (S''.card : ENNReal) / (S.card : ENNReal) ≥ ENNReal.ofReal (1 / 2 : ℝ) := h_mass
  have h_mult : ((S''.card : ENNReal) / (S.card : ENNReal)) * (S.card : ENNReal) = (S''.card : ENNReal) := by
    rw [ENNReal.div_mul_cancel h_pos] <;> simp
  have h : ((S''.card : ENNReal) / (S.card : ENNReal)) * (S.card : ENNReal) ≥
      ENNReal.ofReal (1 / 2 : ℝ) * (S.card : ENNReal) :=
    mul_le_mul_of_nonneg_right h_main (by positivity)
  rw [h_mult] at h
  have h_div : ENNReal.ofReal (1 / 2 : ℝ) * (S.card : ENNReal) = (S.card : ENNReal) / 2 := by
    have h1 : ENNReal.ofReal (1 / 2 : ℝ) = (1 : ENNReal) / 2 := by
      have h2 : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
      rw [h2, ENNReal.ofReal_inv_of_pos (by norm_num)] <;> norm_num
    rw [h1]
    have h2 : (1 : ENNReal) / 2 * (S.card : ENNReal) = (S.card : ENNReal) / 2 := by
      rw [one_div, mul_comm] <;> rfl
    exact h2
  rw [h_div] at h
  exact h

/-- M_G_real bound: (2*(C_inv+1)*sqrt 2 + 6)^2 ≤ 1024 * δ^{-2*rho_sep}. -/
private lemma glue_M_G_bound
    {δ rho_sep C_inv : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (hrho_sep_pos : 0 < rho_sep)
    (hC_inv_nonneg : 0 ≤ C_inv)
    (hC_inv_le : C_inv ≤ 4 * Real.sqrt 2 * δ ^ (-rho_sep)) :
    let L_occ := C_inv + 1
    let M_G_real := (2 * L_occ * Real.sqrt 2 + 6) ^ 2
    M_G_real ≤ 1024 * δ ^ (-2 * rho_sep) := by
  dsimp only
  set L_occ : ℝ := C_inv + 1 with hL_occ_def
  have hδ_neg_rho_sep_ge_one : 1 ≤ δ ^ (-rho_sep) := by
    have h11 : -rho_sep ≤ 0 := by linarith
    have h12 : δ ^ (-rho_sep) ≥ δ ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h11
    simpa using h12
  have hL_occ_pos : 0 < L_occ := by
    dsimp only [L_occ]; have h : 0 ≤ C_inv := hC_inv_nonneg; linarith
  have h1 : L_occ ≤ (4 * Real.sqrt 2 + 1) * δ ^ (-rho_sep) := by
    dsimp only [L_occ]
    have h3 : C_inv ≤ 4 * Real.sqrt 2 * δ ^ (-rho_sep) := hC_inv_le
    have h4 : (1 : ℝ) ≤ δ ^ (-rho_sep) := hδ_neg_rho_sep_ge_one
    linarith
  have h_sqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h_sqrt2_mul : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    have h : Real.sqrt 2 * Real.sqrt 2 = (Real.sqrt 2) ^ 2 := by ring
    rw [h, h_sqrt2_sq]
  have h4 : 2 * L_occ * Real.sqrt 2 + 6 ≤ (22 + 2 * Real.sqrt 2) * δ ^ (-rho_sep) := by
    have h5 : 2 * L_occ * Real.sqrt 2 ≤
        (16 + 2 * Real.sqrt 2) * δ ^ (-rho_sep) := by
      have h51 : 2 * L_occ * Real.sqrt 2 ≤
          2 * ((4 * Real.sqrt 2 + 1) * δ ^ (-rho_sep)) * Real.sqrt 2 := by gcongr <;> linarith
      have h52 : 2 * ((4 * Real.sqrt 2 + 1) * δ ^ (-rho_sep)) * Real.sqrt 2 ≤
          (16 + 2 * Real.sqrt 2) * δ ^ (-rho_sep) := by
        have h : 2 * (4 * Real.sqrt 2 + 1) * Real.sqrt 2 ≤ 16 + 2 * Real.sqrt 2 := by
          nlinarith [Real.sqrt_nonneg 2, h_sqrt2_mul]
        have hpos : 0 ≤ δ ^ (-rho_sep) := by positivity
        nlinarith
      exact le_trans h51 h52
    have h7 : 6 ≤ 6 * δ ^ (-rho_sep) := by
      have h8 : (1 : ℝ) ≤ δ ^ (-rho_sep) := hδ_neg_rho_sep_ge_one
      have h9 : 6 * (1 : ℝ) ≤ 6 * δ ^ (-rho_sep) := by gcongr
      simpa using h9
    linarith
  have h_pos1 : 0 ≤ 2 * L_occ * Real.sqrt 2 + 6 := by positivity
  have h_pos2 : 0 ≤ (22 + 2 * Real.sqrt 2) * δ ^ (-rho_sep) := by positivity
  have h8 : (2 * L_occ * Real.sqrt 2 + 6) ^ 2 ≤
      ((22 + 2 * Real.sqrt 2) * δ ^ (-rho_sep)) ^ 2 := by gcongr
  have h9 : ((22 + 2 * Real.sqrt 2) * δ ^ (-rho_sep)) ^ 2 =
      (22 + 2 * Real.sqrt 2) ^ 2 * (δ ^ (-rho_sep)) ^ 2 := by
    rw [mul_pow] <;> ring
  have h10 : (δ ^ (-rho_sep)) ^ 2 = δ ^ (-2 * rho_sep) := by
    have h101 : (δ ^ (-rho_sep)) ^ 2 = (δ ^ (-rho_sep)) * (δ ^ (-rho_sep)) := by ring
    rw [h101]
    have h102 : (δ ^ (-rho_sep)) * (δ ^ (-rho_sep)) = δ ^ ((-rho_sep) + (-rho_sep)) :=
      Eq.symm (Real.rpow_add hδ_pos (-rho_sep) (-rho_sep))
    rw [h102]; have h103 : (-rho_sep) + (-rho_sep) = -2 * rho_sep := by ring
    rw [h103]
  have h11 : (22 + 2 * Real.sqrt 2) ^ 2 ≤ (1024 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h12 : 0 ≤ δ ^ (-2 * rho_sep) := by positivity
  calc
    (2 * L_occ * Real.sqrt 2 + 6) ^ 2
      ≤ ((22 + 2 * Real.sqrt 2) * δ ^ (-rho_sep)) ^ 2 := h8
    _ = (22 + 2 * Real.sqrt 2) ^ 2 * (δ ^ (-rho_sep)) ^ 2 := h9
    _ = (22 + 2 * Real.sqrt 2) ^ 2 * δ ^ (-2 * rho_sep) := by rw [h10]
    _ ≤ 1024 * δ ^ (-2 * rho_sep) := by nlinarith [h11, h12]

/-- Rounding covering bound for coordinate 1 (S2). -/
private lemma glue_rounding_S2
    {δ : ℝ} (hδ_pos : 0 < δ)
    {E : Set (EuclideanSpace ℝ (Fin 2))}
    {S : Set ℝ}
    (round_fun : ℝ → ℝ)
    (h_round_near : ∀ x, |round_fun x - x| ≤ δ / 2)
    (hS_sub_img : S ⊆ Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round_fun (p 1)) E)
    (hE_bounded : Bornology.IsBounded E) :
    Nreal δ S ≤ 3 * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E) := by
  let B : Set ℝ := Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E
  let R : Set ℝ := Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round_fun (p 1)) E
  have h_coord_le_norm : ∀ (x : EuclideanSpace ℝ (Fin 2)), |x 1| ≤ ‖x‖ := by
    intro x
    have h1 : ‖x‖ ^ 2 = ∑ i : Fin 2, (x i) ^ 2 := EuclideanSpace.real_norm_sq_eq x
    have h2 : (x 1) ^ 2 ≤ ∑ i : Fin 2, (x i) ^ 2 := by
      rw [Fin.sum_univ_two]; exact le_add_of_nonneg_left (sq_nonneg _)
    have h3 : (x 1) ^ 2 ≤ ‖x‖ ^ 2 := by rw [h1] at *; exact h2
    have h4 : |x 1| ≤ ‖x‖ := by nlinarith [abs_nonneg (x 1), norm_nonneg x, sq_abs (x 1)]
    exact h4
  have h_proj_dist : ∀ (p q : EuclideanSpace ℝ (Fin 2)),
      dist (p 1) (q 1) ≤ dist p q := by
    intro p q
    have h1 : dist (p 1) (q 1) = |p 1 - q 1| := by simp [Real.dist_eq]
    rw [h1]
    have h5 : |(p - q) 1| ≤ ‖p - q‖ := h_coord_le_norm (p - q)
    have h6 : (p - q) 1 = p 1 - q 1 := by simp
    rw [h6] at h5
    have h7 : ‖p - q‖ = dist p q := by simp [dist_eq_norm]
    rw [h7] at h5; exact h5
  have hB_bdd : Bornology.IsBounded B :=
    image_bounded_of_lipschitz hE_bounded (show (0 : ℝ) ≤ 1 from by norm_num)
      (fun x y => by simpa using h_proj_dist x y)
  have h_close : ∀ (p : ℝ), p ∈ R → ∃ (q : ℝ), q ∈ B ∧ |p - q| ≤ (↑(1 : ℕ) : ℝ) * δ := by
    intro p hp
    rcases hp with ⟨e, heE, rfl⟩
    let x : ℝ := e 1
    have hx_B : x ∈ B := ⟨e, heE, rfl⟩
    have h_dist : |round_fun x - x| ≤ δ / 2 := h_round_near x
    have hδ2 : δ / 2 ≤ (↑(1 : ℕ) : ℝ) * δ := by simp; linarith
    exact ⟨x, hx_B, le_trans h_dist hδ2⟩
  have h_main : dyadicCoveringNumber δ (productLikeRealLineCopy R) ≤
      (2 * (1 : ℕ) + 1) * dyadicCoveringNumber δ (productLikeRealLineCopy B) :=
    SetDiscretizationBridge.thickening_covering_factor (M := 1) hδ_pos hB_bdd h_close
  have h_realLine : ∀ (A : Set ℝ), productLikeRealLineCopy A = realLineCopy A := by
    intro A; rfl
  rw [h_realLine R, h_realLine B] at h_main
  have h_toENNReal : ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy R)) ≤
      ENat.toENNReal ((2 * (1 : ℕ) + 1) * dyadicCoveringNumber δ (realLineCopy B)) := by
    have h_mono' : Monotone ENat.toENNReal := by
      intro a b h; exact ENat.toENNReal_le.mpr h
    exact h_mono' h_main
  have h_mul : ENat.toENNReal ((2 * (1 : ℕ) + 1) * dyadicCoveringNumber δ (realLineCopy B)) =
      ENat.toENNReal (2 * (1 : ℕ) + 1) * ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy B)) := by
    rw [ENat.toENNReal_mul]
  rw [h_mul] at h_toENNReal
  have h_val : ENat.toENNReal (2 * (1 : ℕ) + 1) = (3 : ENNReal) := by norm_num
  rw [h_val] at h_toENNReal
  have hR_goal : Nreal δ R ≤ (3 : ENNReal) * Nreal δ B := by
    dsimp only [Nreal]; exact h_toENNReal
  have hS_sub_R : S ⊆ R := hS_sub_img
  have h_mono : Nreal δ S ≤ Nreal δ R := robust_projection_main.Nreal_mono_local hS_sub_R
  exact le_trans h_mono hR_goal

/-! ========================================================================
   Main glue theorem
   ======================================================================== -/

/-- **Glue H3→H4**: Admission-free composition theorem.

Takes Helper3's full output plus upstream Helper2 data and produces every
input required by `dense_graph_helper`. No sorrys, no hidden assumptions.

The final `dense_graph_helper` call is left as a function parameter so this
file remains self-contained (Helper3/Helper4 live in scratch, not the repo). -/
lemma glue_H3_to_H4
    -- ===== Basic parameters =====
    {δ κ0 η η_work L_exp rho_sel rho_sep : ℝ}
    {C_extract : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hη_pos : 0 < η)
    (hη_work_pos : 0 < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (hL_exp_pos : 0 < L_exp)
    (hrho_sel_pos : 0 < rho_sel)
    (hrho_sep_pos : 0 < rho_sep)
    -- ===== Density / absorption =====
    (c_dense : ENNReal)
    (hc_dense_eq : c_dense = ENNReal.ofReal (δ ^ (3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work)))
    (hδ_small_absorb : δ ^ qAbsorb η_work ≤ 1 / (2 * 1024 * 6 * 6))
    -- ===== Upstream: E3 and Pbar_param =====
    {Pbar_param : Set (EuclideanSpace ℝ (Fin 2))}
    (hPbar_bounded : Bornology.IsBounded Pbar_param)
    {E3 : Set (EuclideanSpace ℝ (Fin 2))}
    {E3fin : Finset (EuclideanSpace ℝ (Fin 2))}
    (hE3fin_eq : (E3fin : Set _) = E3)
    (hE3_nonempty : E3.Nonempty)
    (hE3_sub_Pbar : E3 ⊆ Pbar_param)
    (hE3_size : ENat.toENNReal E3.encard ≥
        ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar_param)
    -- ===== Upstream: direction projection bounds =====
    {θ1 θ2 θ3 : ℝ}
    (hθ1_lt_θ3 : θ1 < θ3)
    (hθ3_lt_θ2 : θ3 < θ2)
    (hθ1_in_Icc : θ1 ∈ Set.Icc (0 : ℝ) 1)
    (hθ2_in_Icc : θ2 ∈ Set.Icc (0 : ℝ) 1)
    (hθ3_in_Icc : θ3 ∈ Set.Icc (0 : ℝ) 1)
    (h_proj_θ2 : Nreal δ (affineProjection θ2 E3) ≤
        ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)))
    (h_proj_θ1 : Nreal δ (affineProjection θ1 E3) ≤
        ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)))
    (h_proj_θ3 : Nreal δ (affineProjection θ3 E3) ≤
        ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)))
    -- ===== Upstream: occupancy of E3 =====
    (hE3_occupancy : ∀ Q ∈ dyadicCubes 2 δ, (E3 ∩ Q).encard ≤ 1)
    -- ===== Upstream: uniform measure on E3 =====
    {μE3 : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2))}
    [hμE3_prob : MeasureTheory.IsProbabilityMeasure μE3]
    (hμE3_uniform : μE3 = ∑ p ∈ E3fin,
        (1 / ENat.toENNReal E3.encard) • Measure.dirac p)
    -- ===== Helper3 output =====
    {F F_inv : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hF_formula : ∀ p, (F p) 0 = ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1) ∧
                          (F p) 1 = ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1))
    (hF_inv1 : ∀ p ∈ Pbar_param, F_inv (F p) = p)
    {E3' : Set (EuclideanSpace ℝ (Fin 2))}
    (hE3'_eq : E3' = F '' E3)
    {μE3' : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2))}
    (hμE3'_eq : μE3' = MeasureTheory.Measure.map F μE3)
    [hμE3'_prob : MeasureTheory.IsProbabilityMeasure μE3']
    (hE3'_nonempty : E3'.Nonempty)
    {L_proj C_inv : ℝ}
    (hL_proj_nonneg : 0 ≤ L_proj)
    (hF_lip : ∀ u v, dist (F u) (F v) ≤ L_proj * dist u v)
    (hC_inv_nonneg : 0 ≤ C_inv)
    (hC_inv_le : C_inv ≤ 4 * Real.sqrt 2 * δ ^ (-rho_sep))
    (hF_inv_lip : ∀ u v, dist (F_inv u) (F_inv v) ≤ C_inv * dist u v)
    {round_fun : ℝ → ℝ}
    (h_round_near : ∀ z, |z - round_fun z| ≤ δ / 2)
    (hround_grid : ∀ z, round_fun z ∈ productLikeIntegerGrid δ)
    {S1 S2 : Set ℝ}
    (hS1_grid : S1 ⊆ productLikeIntegerGrid δ)
    (hS2_grid : S2 ⊆ productLikeIntegerGrid δ)
    (hS1_sep : ∀ a ∈ S1, ∀ b ∈ S1, a ≠ b → |a - b| ≥ δ)
    (hS2_sep : ∀ a ∈ S2, ∀ b ∈ S2, a ≠ b → |a - b| ≥ δ)
    (hS1_sub_img : S1 ⊆ Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round_fun (p 0)) E3')
    (hS2_sub_img : S2 ⊆ Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round_fun (p 1)) E3')
    (hS1_delta : IsProductLikeRealDeltaSCSet δ κ0 C_extract S1)
    (hS2_delta : IsProductLikeRealDeltaSCSet δ κ0 C_extract S2)
    (hS1_finite : S1.Finite)
    (hS2_finite : S2.Finite)
    (hS1_nonempty : S1.Nonempty)
    (hS2_nonempty : S2.Nonempty)
    {E3'' : Set (EuclideanSpace ℝ (Fin 2))}
    (hE3''_sub : E3'' ⊆ E3')
    (hE3''_mass : μE3' E3'' ≥ ENNReal.ofReal (1 / 2 : ℝ))
    (hE3''_round : ∀ p ∈ E3'', round_fun (p 0) ∈ S1 ∧ round_fun (p 1) ∈ S2)
    :
    -- ===== Conclusion: every exact input needed by dense_graph_helper =====
    ∃ (Pbar : Set (EuclideanSpace ℝ (Fin 2))) (M_G_real : ℝ),
      Pbar_param ⊆ Pbar ∧
      E3' ⊆ Pbar ∧
      Bornology.IsBounded Pbar ∧
      (Nplane δ Pbar ≠ ⊤) ∧
      E3'.Finite ∧
      (ENat.toENNReal E3'.encard ≥
        ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar_param) ∧
      E3'' ⊆ E3' ∧
      (ENat.toENNReal E3''.encard ≥ ENat.toENNReal E3'.encard / 2) ∧
      (0 < M_G_real) ∧
      (M_G_real ≤ 1024 * δ ^ (-2 * rho_sep)) ∧
      (∀ Q ∈ dyadicCubes 2 δ,
        ENat.toENNReal (E3' ∩ Q).encard ≤ ENNReal.ofReal M_G_real) ∧
      (Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 0) '' E3') ≤
        (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal))) ∧
      (Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 1) '' E3') ≤
        (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal))) ∧
      (Nreal δ S1 ≤ (3 : ENNReal) * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E3')) ∧
      (Nreal δ S2 ≤ (3 : ENNReal) * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E3')) ∧
      (Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 0 + q 1) '' E3') ≤
        ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar).toReal))) ∧
      (Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 0 + q 1) '' E3') ≤
        ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal))) := by
  -- ========================================================================
  -- 0. Define Pbar and M_G_real
  -- ========================================================================
  let Pbar : Set (EuclideanSpace ℝ (Fin 2)) := Pbar_param ∪ E3'
  let L_occ : ℝ := C_inv + 1
  let M_G_real : ℝ := (2 * L_occ * Real.sqrt 2 + 6) ^ 2

  have hPbar_param_sub_Pbar : Pbar_param ⊆ Pbar := by simp [Pbar]
  have hE3'_sub_Pbar : E3' ⊆ Pbar := by simp [Pbar]

  -- Pbar bounded: union of bounded Pbar_param and bounded E3'
  have hE3_bounded : Bornology.IsBounded E3 := hPbar_bounded.subset hE3_sub_Pbar
  let L_proj_nn : NNReal := ⟨L_proj, hL_proj_nonneg⟩
  have hF_lip' : LipschitzWith L_proj_nn F := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have h_eq : (L_proj_nn : ℝ) = L_proj := by
      simp [L_proj_nn] <;> rfl
    rw [h_eq]
    exact hF_lip u v
  have hF_cont : Continuous F := hF_lip'.continuous
  have hF_meas : Measurable F := hF_cont.measurable
  have hE3'_bounded : Bornology.IsBounded E3' := by
    rw [hE3'_eq]
    exact hF_lip'.isBounded_image hE3_bounded
  have hPbar_bounded' : Bornology.IsBounded Pbar :=
    Bornology.IsBounded.union hPbar_bounded hE3'_bounded

  -- Nplane δ Pbar ≠ ⊤
  have hPbar_top : Nplane δ Pbar ≠ ⊤ := by
    have hfin : (dyadicCubesMeeting δ Pbar).Finite :=
      dyadicCubesMeeting_finite hδ_pos hPbar_bounded'
    let sFinset := hfin.toFinset
    have hcard : (dyadicCubesMeeting δ Pbar).encard = ↑sFinset.card :=
      Set.Finite.encard_eq_coe_toFinset_card hfin
    simp only [Nplane, dyadicCoveringNumber, hcard] <;> simp

  -- ========================================================================
  -- 1. E3' finite and size
  -- ========================================================================
  have hE3_finite : E3.Finite := by
    rw [← hE3fin_eq] <;> exact E3fin.finite_toSet
  have hE3'_finite : E3'.Finite := by
    rw [hE3'_eq]; exact Set.Finite.image F hE3_finite

  have hF_inj_on_E3 : Set.InjOn F E3 := by
    intro p hp q hq h_eq
    have hpP : p ∈ Pbar_param := hE3_sub_Pbar hp
    have hqP : q ∈ Pbar_param := hE3_sub_Pbar hq
    have h1 : F_inv (F p) = p := hF_inv1 p hpP
    have h2 : F_inv (F q) = q := hF_inv1 q hqP
    have h3 : F_inv (F p) = F_inv (F q) := by rw [h_eq]
    rw [h1, h2] at h3; exact h3

  have h_encard_eq : ENat.toENNReal E3'.encard = ENat.toENNReal E3.encard := by
    rw [hE3'_eq]
    have h : (F '' E3).encard = E3.encard := hF_inj_on_E3.encard_image
    rw [h]

  have hE3'_size : ENat.toENNReal E3'.encard ≥
      ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar_param := by
    rw [h_encard_eq]; exact hE3_size

  -- ========================================================================
  -- 2. Uniform measure on E3' and E3'' half
  -- ========================================================================
  have hE3fin_nonempty : E3fin.Nonempty := by
    rcases hE3_nonempty with ⟨x, hx⟩
    have hx' : x ∈ (E3fin : Set _) := by
      rw [hE3fin_eq]
      exact hx
    exact ⟨x, by simpa using hx'⟩

  let E3'fin : Finset (EuclideanSpace ℝ (Fin 2)) := hE3'_finite.toFinset
  have hE3'fin_coe : (E3'fin : Set _) = E3' := Finite.coe_toFinset hE3'_finite

  have hμE3'_uniform : μE3' = ∑ p ∈ E3'fin,
      (1 / ENat.toENNReal E3'.encard) • Measure.dirac p := by
    rw [hμE3'_eq, hμE3_uniform]
    have hF_inj_finset : ∀ (x : EuclideanSpace ℝ (Fin 2)), x ∈ E3fin →
        ∀ (y : EuclideanSpace ℝ (Fin 2)), y ∈ E3fin → F x = F y → x = y := by
      intro x hx y hy h
      exact hF_inj_on_E3 (by rw [←hE3fin_eq] <;> exact hx)
        (by rw [←hE3fin_eq] <;> exact hy) h
    have h_ae : AEMeasurable F (∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard) • Measure.dirac p) :=
      hF_meas.aemeasurable
    have h1 : Measure.map F (∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard) • Measure.dirac p) =
        ∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard) • Measure.dirac (F p) := by
      rw [Measure.map_finset_sum h_ae]
      apply Finset.sum_congr rfl
      intro p _
      have h_map_smul : Measure.map F ((1 / ENat.toENNReal E3.encard) • Measure.dirac p) =
          (1 / ENat.toENNReal E3.encard) • Measure.map F (Measure.dirac p) := by
        rw [Measure.map_smul]
      rw [h_map_smul]
      have h_map_dirac : Measure.map F (Measure.dirac p) = Measure.dirac (F p) :=
        Measure.map_dirac' hF_meas p
      rw [h_map_dirac]
    have h_encard_eq' : ENat.toENNReal (F '' E3).encard = ENat.toENNReal E3.encard := by
      rw [hF_inj_on_E3.encard_image]
    have h2 : ∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard) • Measure.dirac (F p) =
        ∑ p' ∈ Finset.image F E3fin, (1 / ENat.toENNReal E3.encard) • Measure.dirac p' := by
      rw [Finset.sum_image hF_inj_finset] <;> rfl
    rw [h1, h2]
    have h3 : ENat.toENNReal E3'.encard = ENat.toENNReal E3.encard := h_encard_eq
    rw [h3]
    have h4 : Finset.image F E3fin = E3'fin := by
      apply Finset.coe_injective
      ext z; simp [hE3'_eq, hE3fin_eq, hE3'fin_coe] <;> tauto
    rw [h4]

  have hE3''_half : ENat.toENNReal E3''.encard ≥ ENat.toENNReal E3'.encard / 2 :=
    glue_mass_half_to_encard hE3'_finite hE3'_nonempty hμE3'_uniform hE3''_sub hE3''_mass

  -- ========================================================================
  -- 3. Occupancy bound for E3'
  -- ========================================================================
  have hL_occ_pos : 0 < L_occ := by
    dsimp only [L_occ]; have h : 0 ≤ C_inv := hC_inv_nonneg; linarith
  have hF_inv_lip_occ : ∀ u v, dist (F_inv u) (F_inv v) ≤ L_occ * dist u v := by
    intro u v
    have h : dist (F_inv u) (F_inv v) ≤ C_inv * dist u v := hF_inv_lip u v
    have h2 : C_inv * dist u v ≤ L_occ * dist u v := by
      have h3 : 0 ≤ dist u v := by positivity
      gcongr <;> linarith
    exact le_trans h h2

  have h_occupancy : ∀ Q ∈ dyadicCubes 2 δ,
      ENat.toENNReal (E3' ∩ Q).encard ≤ ENNReal.ofReal M_G_real :=
    occupancy_from_inv_lipschitz
      (hδ_pos := hδ_pos) (hL_pos := hL_occ_pos)
      (hE3_finite := hE3_finite)
      (hF_left_inv := fun p hp => hF_inv1 p (hE3_sub_Pbar hp))
      (hF_inv_lip := hF_inv_lip_occ)
      (h_per_cube := hE3_occupancy)
      (hE3''_sub := by rw [hE3'_eq] <;> exact Set.Subset.refl _)

  have hM_G_pos : 0 < M_G_real := by positivity
  have hM_G_bound1024 : M_G_real ≤ 1024 * δ ^ (-2 * rho_sep) :=
    glue_M_G_bound hδ_pos hδ_lt_one hrho_sep_pos hC_inv_nonneg hC_inv_le

  -- ========================================================================
  -- 4. Coordinate projection bounds (re-proved from F formula)
  -- ========================================================================
  let b3 : ℝ := (θ3 - θ1) / (θ2 - θ1)
  let a3 : ℝ := (θ2 - θ3) / (θ2 - θ1)

  have hb3_pos : 0 < b3 := by apply div_pos <;> linarith
  have ha3_pos : 0 < a3 := by apply div_pos <;> linarith
  have hb3_le_one : b3 ≤ 1 := by
    apply (div_le_one (by linarith)).mpr; linarith
  have ha3_le_one : a3 ≤ 1 := by
    apply (div_le_one (by linarith)).mpr; linarith

  -- coord0(E3') = scaleSet b3 (affineProjection θ2 E3)
  have h_q0_set : (fun q : EuclideanSpace ℝ (Fin 2) => q 0) '' E3' =
      scaleSet b3 (affineProjection θ2 E3) := by
    ext z
    simp only [Set.mem_image, scaleSet, hE3'_eq]
    constructor
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨p 0 * θ2 + p 1, ⟨p, hp, rfl⟩, ?_⟩
      have h1 : (F p) 0 = b3 * (p 0 * θ2 + p 1) := by
        simpa [b3] using (hF_formula p).1
      exact h1.symm
    · rintro ⟨w, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨F p, ⟨p, hp, rfl⟩, ?_⟩
      have h1 : (F p) 0 = b3 * (p 0 * θ2 + p 1) := by
        simpa [b3] using (hF_formula p).1
      simpa using h1

  have h_proj_θ2_bdd : Bornology.IsBounded (affineProjection θ2 E3) :=
    projectionSet.bounded θ2 hE3_bounded

  have h_coord0_bound : Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 0) '' E3') ≤
      (2 : ENNReal) * Nreal δ (affineProjection θ2 E3) := by
    rw [h_q0_set]
    have h : Nreal δ (scaleSet b3 (affineProjection θ2 E3)) ≤
        (Nat.ceil (|b3|) + 1 : ENNReal) * Nreal δ (affineProjection θ2 E3) :=
      FourSectorChart.scalar_covering_upper hδ_pos (abs_nonneg b3) h_proj_θ2_bdd (le_refl |b3|)
    have h_ceil : Nat.ceil (|b3|) = 1 := by
      have h2 : |b3| = b3 := by rw [abs_of_nonneg (le_of_lt hb3_pos)]
      rw [h2]
      rw [Nat.ceil_eq_iff (by norm_num)]
      refine' ⟨_, _⟩
      · simpa using hb3_pos
      · exact_mod_cast hb3_le_one
    have h_coeff : (Nat.ceil (|b3|) + 1 : ENNReal) = (2 : ENNReal) := by
      rw [h_ceil]
      norm_cast
    rw [h_coeff] at h
    exact h

  -- coord1(E3') = scaleSet a3 (affineProjection θ1 E3)
  have h_q1_set : (fun q : EuclideanSpace ℝ (Fin 2) => q 1) '' E3' =
      scaleSet a3 (affineProjection θ1 E3) := by
    ext z
    simp only [Set.mem_image, scaleSet, hE3'_eq]
    constructor
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨p 0 * θ1 + p 1, ⟨p, hp, rfl⟩, ?_⟩
      have h1 : (F p) 1 = a3 * (p 0 * θ1 + p 1) := by
        simpa [a3] using (hF_formula p).2
      exact h1.symm
    · rintro ⟨w, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨F p, ⟨p, hp, rfl⟩, ?_⟩
      have h1 : (F p) 1 = a3 * (p 0 * θ1 + p 1) := by
        simpa [a3] using (hF_formula p).2
      simpa using h1

  have h_proj_θ1_bdd : Bornology.IsBounded (affineProjection θ1 E3) :=
    projectionSet.bounded θ1 hE3_bounded

  have h_coord1_bound : Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 1) '' E3') ≤
      (2 : ENNReal) * Nreal δ (affineProjection θ1 E3) := by
    rw [h_q1_set]
    have h : Nreal δ (scaleSet a3 (affineProjection θ1 E3)) ≤
        (Nat.ceil (|a3|) + 1 : ENNReal) * Nreal δ (affineProjection θ1 E3) :=
      FourSectorChart.scalar_covering_upper hδ_pos (abs_nonneg a3) h_proj_θ1_bdd (le_refl |a3|)
    have h_ceil : Nat.ceil (|a3|) = 1 := by
      have h2 : |a3| = a3 := by rw [abs_of_nonneg (le_of_lt ha3_pos)]
      rw [h2]
      rw [Nat.ceil_eq_iff (by norm_num)]
      refine' ⟨_, _⟩
      · simpa using ha3_pos
      · exact_mod_cast ha3_le_one
    have h_coeff : (Nat.ceil (|a3|) + 1 : ENNReal) = (2 : ENNReal) := by
      rw [h_ceil]
      norm_cast
    rw [h_coeff] at h
    exact h

  -- Compose with direction projection bounds
  have h_proj_x : Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 0) '' E3') ≤
      (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by
    calc Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 0) '' E3')
      ≤ (2 : ENNReal) * Nreal δ (affineProjection θ2 E3) := h_coord0_bound
    _ ≤ (2 : ENNReal) * (ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal))) :=
        mul_le_mul_of_nonneg_left h_proj_θ2 (by positivity)
    _ = (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by ring

  have h_proj_y : Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 1) '' E3') ≤
      (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by
    calc Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 1) '' E3')
      ≤ (2 : ENNReal) * Nreal δ (affineProjection θ1 E3) := h_coord1_bound
    _ ≤ (2 : ENNReal) * (ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal))) :=
        mul_le_mul_of_nonneg_left h_proj_θ1 (by positivity)
    _ = (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by ring

  -- ========================================================================
  -- 5. Third projection: exact identity with affineProjection θ3 E3
  -- ========================================================================
  have h_third_identity : ∀ (p : EuclideanSpace ℝ (Fin 2)),
      (F p) 0 + (F p) 1 = p 0 * θ3 + p 1 := by
    intro p
    have hf0 : (F p) 0 = ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1) := (hF_formula p).1
    have hf1 : (F p) 1 = ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1) := (hF_formula p).2
    rw [hf0, hf1]
    have hD : θ2 - θ1 ≠ 0 := by linarith
    field_simp [hD] <;> ring
  have h_set : (fun q : EuclideanSpace ℝ (Fin 2) => q 0 + q 1) '' E3' =
      affineProjection θ3 E3 := by
    ext z
    simp only [Set.mem_image, affineProjection, hE3'_eq]
    constructor
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, (h_third_identity p).symm⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨F p, ⟨p, hp, rfl⟩, ?_⟩
      exact h_third_identity p

  -- Third projection bound with Pbar (not Pbar_param)
  have hN_param_le : Nplane δ Pbar_param ≤ Nplane δ Pbar := by
    apply ENat.toENNReal_mono
    apply Set.encard_mono
    intro Q hQ
    have hQ1 : Q ∈ dyadicCubes 2 δ := hQ.1
    have hQ2 : (Q ∩ Pbar_param).Nonempty := hQ.2
    have h_inter_sub : Q ∩ Pbar_param ⊆ Q ∩ Pbar := by
      intro x hx; exact ⟨hx.1, hPbar_param_sub_Pbar hx.2⟩
    have hQ3 : (Q ∩ Pbar).Nonempty := Set.Nonempty.mono h_inter_sub hQ2
    exact ⟨hQ1, hQ3⟩
  have hN_param_top : Nplane δ Pbar_param ≠ ⊤ := ne_top_of_le_ne_top hPbar_top hN_param_le
  have h_toReal_le : (Nplane δ Pbar_param).toReal ≤ (Nplane δ Pbar).toReal :=
    ENNReal.toReal_mono hPbar_top hN_param_le
  have h_sqrt_le : Real.sqrt ((Nplane δ Pbar_param).toReal) ≤
      Real.sqrt ((Nplane δ Pbar).toReal) := Real.sqrt_le_sqrt h_toReal_le

  have h_third_proj_E3'_param : Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 0 + q 1) '' E3') ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by
    rw [h_set]
    exact h_proj_θ3

  have h_third_proj_E3' : Nreal δ ((fun q : EuclideanSpace ℝ (Fin 2) => q 0 + q 1) '' E3') ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar).toReal)) := by
    rw [h_set]
    calc Nreal δ (affineProjection θ3 E3)
      ≤ ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := h_proj_θ3
    _ ≤ ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar).toReal)) := by
      gcongr <;> exact h_sqrt_le

  -- ========================================================================
  -- 6. S1/S2 rounding covering bounds
  -- ========================================================================
  have hS1_bound : Nreal δ S1 ≤
      (3 : ENNReal) * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E3') :=
    rounded_projection_bound hδ_pos round_fun (fun x => by simpa [abs_sub_comm] using h_round_near x) hS1_sub_img hE3'_bounded

  have hS2_bound : Nreal δ S2 ≤
      (3 : ENNReal) * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E3') :=
    glue_rounding_S2 hδ_pos round_fun (fun x => by simpa [abs_sub_comm] using h_round_near x) hS2_sub_img hE3'_bounded

  -- ========================================================================
  -- 7. Package all Helper4 exact inputs
  -- ========================================================================
  refine' ⟨Pbar, M_G_real, _⟩
  exact ⟨hPbar_param_sub_Pbar, hE3'_sub_Pbar, hPbar_bounded', hPbar_top,
    hE3'_finite, hE3'_size, hE3''_sub, hE3''_half,
    hM_G_pos, hM_G_bound1024, h_occupancy,
    h_proj_x, h_proj_y, hS1_bound, hS2_bound, h_third_proj_E3', h_third_proj_E3'_param⟩

  -- NOTE: Applying dense_graph_helper with these exact inputs yields the final
  -- ∃ Gamma, ... conclusion. It is not called here because Helper4 lives in
  -- scratch and cannot be imported from this self-contained repository file.

end ProductLikeIncidence.ProductReduction
