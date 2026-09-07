module

/-
# Phase 2 Transport — Projective Normalization (Point-Set Only)

Wires together:
1. Point-set transport through projective map G (homeomorphism, Lipschitz, covering)
2. FullLambda scalar covering bound for projections via FourSectorChart.scalar_covering_upper

## IMPORTANT: No direction transport here

Direction measure normalization (pole removal, chart selection, pushforward)
belongs to Phase 7, AFTER BSG extraction. Phase 2 only transports point sets
through the projective map G.

## Projection identity

For y ≠ θ2:
  let a3 := (θ2-θ3)/(θ2-θ1)
  let a_y := (θ2-y)/(θ2-θ1)
  let fullLambda(y) := a3/a_y
Then:
  projectionSet (x y) E3' = scaleSet fullLambda(y) (projectionSet y E3)

And the covering bound (FORWARD direction):
  Nreal δ (projectionSet (x y) E3') ≤
    (⌈|fullLambda(y)|⌉ + 1) * Nreal δ (projectionSet y E3)

## Whiteprint node
`phase2_transport`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.Compat
public import MyLeanRepo.ProductLikeIncidence.PbarPrimeConstruction
public import MyLeanRepo.ProductLikeIncidence.FourSectorChart
public import MyLeanRepo.OSWPrelude

@[expose] public section


noncomputable section

open Set ENNReal Bornology MeasureTheory Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-! ========================================================================
   Private helper lemmas
-/

private lemma pelican_euclidean_norm_sq (z : EuclideanSpace ℝ (Fin 2)) :
    ‖z‖^2 = (z 0)^2 + (z 1)^2 := by
  have h1 : ‖z‖ = Real.sqrt ((z 0)^2 + (z 1)^2) := by
    simpa [EuclideanSpace.norm_eq, Fin.sum_univ_two] using rfl
  rw [h1, Real.sq_sqrt] <;> positivity

private lemma pelican_cs2 (a b x y : ℝ) :
    (a * x + b * y)^2 ≤ (a^2 + b^2) * (x^2 + y^2) := by
  nlinarith [sq_nonneg (a * y - b * x)]

private lemma pelican_sum_ineq (a0 a1 a2 a3 x0 x1 : ℝ)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) :
    (a0 + a2) * x0 + (a1 + a3) * x1 ≤ (a0 + a1 + a2 + a3) * (x0 + x1) := by
  have h : (a0 + a1 + a2 + a3) * (x0 + x1) - ((a0 + a2) * x0 + (a1 + a3) * x1) =
      a0 * x1 + a1 * x0 + a2 * x1 + a3 * x0 := by ring
  have hpos : 0 ≤ a0 * x1 + a1 * x0 + a2 * x1 + a3 * x0 := by
    have h1 : 0 ≤ a0 * x1 := mul_nonneg ha0 hx1
    have h2 : 0 ≤ a1 * x0 := mul_nonneg ha1 hx0
    have h3 : 0 ≤ a2 * x1 := mul_nonneg ha2 hx1
    have h4 : 0 ≤ a3 * x0 := mul_nonneg ha3 hx0
    linarith
  have h' : 0 ≤ (a0 + a1 + a2 + a3) * (x0 + x1) - ((a0 + a2) * x0 + (a1 + a3) * x1) := by
    rw [h] <;> exact hpos
  linarith

private lemma pelican_coord_le_norm (z : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    |z i| ≤ ‖z‖ := by
  have h_norm_sq : ‖z‖^2 = (z 0)^2 + (z 1)^2 := pelican_euclidean_norm_sq z
  have h_sq : (z i)^2 ≤ ‖z‖^2 := by
    rw [h_norm_sq]
    fin_cases i
    · exact le_add_of_nonneg_right (sq_nonneg (z 1))
    · exact le_add_of_nonneg_left (sq_nonneg (z 0))
  have h_abs_sq : |z i|^2 = (z i)^2 := by simp
  have h1 : |z i|^2 ≤ ‖z‖^2 := by
    rw [h_abs_sq] <;> exact h_sq
  have h_abs_sqrt : Real.sqrt (|z i|^2) = |z i| := by
    rw [Real.sqrt_sq (abs_nonneg (z i))]
  have h_norm_sqrt : Real.sqrt (‖z‖^2) = ‖z‖ := by
    rw [Real.sqrt_sq (norm_nonneg z)]
  have h5 : Real.sqrt (|z i|^2) ≤ Real.sqrt (‖z‖^2) := Real.sqrt_le_sqrt h1
  rw [h_abs_sqrt, h_norm_sqrt] at h5
  exact h5

private lemma pelican_equiv_symm_coord {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    ((EuclideanSpace.equiv (Fin n) ℝ).symm f) i = f i := by
  have h1 : (EuclideanSpace.equiv (Fin n) ℝ) ((EuclideanSpace.equiv (Fin n) ℝ).symm f) = f :=
    (EuclideanSpace.equiv (Fin n) ℝ).apply_symm_apply f
  exact congr_fun h1 i

/-! ========================================================================
   Main theorem: Phase 2 point-set transport
-/

/-- Phase 2: projective normalization of point-set data ONLY.

Takes Phase 1 output (point sets Pbar/E3/μE3/P_y, selected directions
θ1<θ3<θ2) and produces:
- Projective map G and inverse G_inv (V,U ordering)
- Cross-ratio coefficient x(y)
- Transported point sets Pbar', E3', μE3', P_y'
- Forward/backward covering constants C_forward, C_backward
- Inverse Lipschitz constant C_inv for G_inv
- Projection identity with forward covering bound using arbitrary M = |fullLambda(y)|
-/
theorem phase2_transport
    {δ : ℝ} (hδ_pos : 0 < δ)
    -- Selected directions (Phase 1 output)
    {θ1 θ2 θ3 : ℝ}
    (hθ1_lt_θ3 : θ1 < θ3) (hθ3_lt_θ2 : θ3 < θ2)
    (hθ1_in_unit : θ1 ∈ Set.Icc 0 1)
    (hθ2_in_unit : θ2 ∈ Set.Icc 0 1)
    (hθ3_in_unit : θ3 ∈ Set.Icc 0 1)
    -- Point data (Phase 1 output)
    {Pbar E3 : Set (EuclideanSpace ℝ (Fin 2))}
    (hPbar_bounded : IsBounded Pbar)
    (hE3_sub_Pbar : E3 ⊆ Pbar)
    (hE3_bounded : IsBounded E3)
    {μE3 : Measure (EuclideanSpace ℝ (Fin 2))}
    [IsProbabilityMeasure μE3]
    (hμE3_support : μE3.support = E3)
    (hE3_nonempty : E3.Nonempty)
    {P_y : ℝ → Set (EuclideanSpace ℝ (Fin 2))}
    (hPy_bounded : ∀ y, IsBounded (P_y y)) :
    ∃ (G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (G_inv : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (x : ℝ → ℝ)
      (Pbar' E3' : Set (EuclideanSpace ℝ (Fin 2)))
      (μE3' : Measure (EuclideanSpace ℝ (Fin 2)))
      (P_y' : ℝ → Set (EuclideanSpace ℝ (Fin 2)))
      (C_forward C_backward : ENNReal)
      (C_inv : ℝ),
      (∀ p, G p = ![
          ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1),
          ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1)]) ∧
      (∀ p, G_inv (G p) = p) ∧
      (∀ q, G (G_inv q) = q) ∧
      Function.Injective G ∧
      (∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y))) ∧
      Pbar' = G '' Pbar ∧
      E3' = G '' E3 ∧
      μE3' = Measure.map G μE3 ∧
      (∀ y, P_y' y = G '' (P_y y)) ∧
      μE3'.support = E3' ∧
      IsProbabilityMeasure μE3' ∧
      IsBounded Pbar' ∧
      IsBounded E3' ∧
      (∀ y, IsBounded (P_y' y)) ∧
      C_forward ≠ ⊤ ∧ C_backward ≠ ⊤ ∧
      (ENat.toENNReal (dyadicCoveringNumber δ Pbar') ≤
          C_forward * ENat.toENNReal (dyadicCoveringNumber δ Pbar)) ∧
      (∀ y, ENat.toENNReal (dyadicCoveringNumber δ (P_y' y)) ≤
          C_forward * ENat.toENNReal (dyadicCoveringNumber δ (P_y y))) ∧
      (ENat.toENNReal (dyadicCoveringNumber δ Pbar) ≤
          C_backward * ENat.toENNReal (dyadicCoveringNumber δ Pbar')) ∧
      (∀ y, ENat.toENNReal (dyadicCoveringNumber δ (P_y y)) ≤
          C_backward * ENat.toENNReal (dyadicCoveringNumber δ (P_y' y))) ∧
      0 ≤ C_inv ∧
      C_inv = Real.sqrt 2 * (1 / (θ3 - θ1) + 1 / (θ2 - θ3) + θ1 / (θ3 - θ1) + θ2 / (θ2 - θ3)) ∧
      (∀ (u v : EuclideanSpace ℝ (Fin 2)),
        dist (G_inv u) (G_inv v) ≤ C_inv * dist u v) ∧
      (∀ (y : ℝ), y ≠ θ2 →
        let a3 := (θ2 - θ3) / (θ2 - θ1)
        let a_y := (θ2 - y) / (θ2 - θ1)
        let fullLambda := a3 / a_y
        let M := |fullLambda|
        Nreal δ (projectionSet (x y) E3') ≤
          (Nat.ceil M + 1 : ENNReal) * Nreal δ (projectionSet y E3)) := by
  -- =====================================================================
  -- Define G, G_inv, x explicitly
  -- =====================================================================
  let b3 := (θ3 - θ1) / (θ2 - θ1)
  let a3 := (θ2 - θ3) / (θ2 - θ1)
  let G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun p =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![
      b3 * (p 0 * θ2 + p 1),
      a3 * (p 0 * θ1 + p 1)]
  let G_inv : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun q =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![ q 0 / (θ3 - θ1) - q 1 / (θ2 - θ3),
      -θ1 * q 0 / (θ3 - θ1) + θ2 * q 1 / (θ2 - θ3)]
  let x : ℝ → ℝ := fun y =>
    ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y))

  have h_θ2_ne_θ1 : θ2 ≠ θ1 := by linarith
  have h_θ3_ne_θ1 : θ3 ≠ θ1 := by linarith
  have h_θ3_ne_θ2 : θ3 ≠ θ2 := by linarith
  have hD_ne : θ2 - θ1 ≠ 0 := by linarith
  have h31_ne : θ3 - θ1 ≠ 0 := by linarith
  have h23_ne : θ2 - θ3 ≠ 0 := by linarith

  have hG_formula : ∀ p, G p = ![
      b3 * (p 0 * θ2 + p 1),
      a3 * (p 0 * θ1 + p 1)] := by
    intro p; ext i; fin_cases i <;> simp [G, pelican_equiv_symm_coord] <;> ring

  have hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)) := by
    intro y; rfl

  -- =====================================================================
  -- Coordinate formulas
  -- =====================================================================
  have hG_coord : ∀ p, (G p) 0 = b3 * (p 0 * θ2 + p 1) ∧
                         (G p) 1 = a3 * (p 0 * θ1 + p 1) := by
    intro p
    have h := hG_formula p
    constructor
    · have h2 := congr_fun h 0; simpa using h2
    · have h2 := congr_fun h 1; simpa using h2

  have hGinv_coord_simp : ∀ q,
      (G_inv q) 0 = q 0 / (θ3 - θ1) - q 1 / (θ2 - θ3) ∧
      (G_inv q) 1 = -θ1 * q 0 / (θ3 - θ1) + θ2 * q 1 / (θ2 - θ3) := by
    intro q
    constructor
    · change ((EuclideanSpace.equiv (Fin 2) ℝ).symm
          ![q 0 / (θ3 - θ1) - q 1 / (θ2 - θ3),
            -θ1 * q 0 / (θ3 - θ1) + θ2 * q 1 / (θ2 - θ3)]) 0 =
          q 0 / (θ3 - θ1) - q 1 / (θ2 - θ3)
      rw [pelican_equiv_symm_coord]
      <;> simp
    · change ((EuclideanSpace.equiv (Fin 2) ℝ).symm
          ![q 0 / (θ3 - θ1) - q 1 / (θ2 - θ3),
            -θ1 * q 0 / (θ3 - θ1) + θ2 * q 1 / (θ2 - θ3)]) 1 =
          -θ1 * q 0 / (θ3 - θ1) + θ2 * q 1 / (θ2 - θ3)
      rw [pelican_equiv_symm_coord]
      <;> simp

  -- =====================================================================
  -- Inverse properties
  -- =====================================================================
  have hG_inv1 : ∀ p, G_inv (G p) = p := by
    intro p
    have hgp0 : (G p) 0 = b3 * (p 0 * θ2 + p 1) := (hG_coord p).1
    have hgp1 : (G p) 1 = a3 * (p 0 * θ1 + p 1) := (hG_coord p).2
    rcases hGinv_coord_simp (G p) with ⟨hgi1, hgi2⟩
    ext i
    fin_cases i
    · have h : (G_inv (G p)) 0 = p 0 := by
        calc (G_inv (G p)) 0
          = (G p) 0 / (θ3 - θ1) - (G p) 1 / (θ2 - θ3) := hgi1
        _ = b3 * (p 0 * θ2 + p 1) / (θ3 - θ1) - a3 * (p 0 * θ1 + p 1) / (θ2 - θ3) := by rw [hgp0, hgp1]
        _ = p 0 := by
          dsimp only [b3, a3]
          field_simp [hD_ne, h31_ne, h23_ne] <;> ring
      exact h
    · have h : (G_inv (G p)) 1 = p 1 := by
        calc (G_inv (G p)) 1
          = -θ1 * (G p) 0 / (θ3 - θ1) + θ2 * (G p) 1 / (θ2 - θ3) := hgi2
        _ = -θ1 * (b3 * (p 0 * θ2 + p 1)) / (θ3 - θ1) + θ2 * (a3 * (p 0 * θ1 + p 1)) / (θ2 - θ3) := by rw [hgp0, hgp1]
        _ = p 1 := by
          dsimp only [b3, a3]
          field_simp [hD_ne, h31_ne, h23_ne] <;> ring
      exact h

  have hG_inv2 : ∀ q, G (G_inv q) = q := by
    intro q
    rcases hGinv_coord_simp q with ⟨hgi0, hgi1⟩
    rcases hG_coord (G_inv q) with ⟨hgc0, hgc1⟩
    ext i
    fin_cases i
    · have h : (G (G_inv q)) 0 = q 0 := by
        calc (G (G_inv q)) 0
          = b3 * ((G_inv q) 0 * θ2 + (G_inv q) 1) := hgc0
        _ = b3 * ((q 0 / (θ3 - θ1) - q 1 / (θ2 - θ3)) * θ2 +
                   (-θ1 * q 0 / (θ3 - θ1) + θ2 * q 1 / (θ2 - θ3))) := by rw [hgi0, hgi1]
        _ = q 0 := by
          dsimp only [b3]
          field_simp [h31_ne, h23_ne] <;> ring
      exact h
    · have h : (G (G_inv q)) 1 = q 1 := by
        calc (G (G_inv q)) 1
          = a3 * ((G_inv q) 0 * θ1 + (G_inv q) 1) := hgc1
        _ = a3 * ((q 0 / (θ3 - θ1) - q 1 / (θ2 - θ3)) * θ1 +
                   (-θ1 * q 0 / (θ3 - θ1) + θ2 * q 1 / (θ2 - θ3))) := by rw [hgi0, hgi1]
        _ = q 1 := by
          dsimp only [a3]
          field_simp [h31_ne, h23_ne] <;> ring
      exact h

  have hG_inj : Function.Injective G := by
    intro p q h
    have h1 : G_inv (G p) = G_inv (G q) := by rw [h]
    rw [hG_inv1 p, hG_inv1 q] at h1
    exact h1

  -- =====================================================================
  -- Continuity of G and G_inv
  -- =====================================================================
  let e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (Fin 2 → ℝ) := EuclideanSpace.equiv (Fin 2) ℝ

  have hG_cont : Continuous G := by
    have h1 : Continuous (fun p : EuclideanSpace ℝ (Fin 2) => (G p) 0) := by
      have h_eq : (fun p => (G p) 0) = fun p => b3 * (p 0 * θ2 + p 1) := by
        funext p; exact (hG_coord p).1
      rw [h_eq]; fun_prop
    have h2 : Continuous (fun p => (G p) 1) := by
      have h_eq : (fun p => (G p) 1) = fun p => a3 * (p 0 * θ1 + p 1) := by
        funext p; exact (hG_coord p).2
      rw [h_eq]; fun_prop
    have h_all : ∀ (i : Fin 2), Continuous (fun p => (e (G p)) i) := by
      intro i; have h_i : (fun p => (e (G p)) i) = (fun p => (G p) i) := by funext p; rfl
      rw [h_i]; fin_cases i <;> assumption
    have hvec : Continuous (fun p => e (G p)) := continuous_pi h_all
    have h_eq : G = e.symm ∘ (fun p => e (G p)) := by funext p; exact e.left_inv (G p)
    rw [h_eq]; exact e.symm.continuous.comp hvec

  have hGinv_cont : Continuous G_inv := by
    have h1 : Continuous (fun q => (G_inv q) 0) := by
      have h_eq : (fun q => (G_inv q) 0) =
          fun q => q 0 / (θ3 - θ1) - q 1 / (θ2 - θ3) := by
        funext q; exact (hGinv_coord_simp q).1
      rw [h_eq]; fun_prop
    have h2 : Continuous (fun q => (G_inv q) 1) := by
      have h_eq : (fun q => (G_inv q) 1) =
          fun q => -θ1 * q 0 / (θ3 - θ1) + θ2 * q 1 / (θ2 - θ3) := by
        funext q; exact (hGinv_coord_simp q).2
      rw [h_eq]; fun_prop
    have h_all : ∀ (i : Fin 2), Continuous (fun q => (e (G_inv q)) i) := by
      intro i; have h_i : (fun q => (e (G_inv q)) i) = (fun q => (G_inv q) i) := by funext q; rfl
      rw [h_i]; fin_cases i <;> assumption
    have hvec : Continuous (fun q => e (G_inv q)) := continuous_pi h_all
    have h_eq : G_inv = e.symm ∘ (fun q => e (G_inv q)) := by funext q; exact e.left_inv (G_inv q)
    rw [h_eq]; exact e.symm.continuous.comp hvec

  -- =====================================================================
  -- Lipschitz bound for G
  -- =====================================================================
  let C_U : ℝ := Real.sqrt ((b3 * θ2)^2 + b3^2 + (a3 * θ1)^2 + a3^2)
  have hC_U_nonneg : 0 ≤ C_U := Real.sqrt_nonneg _
  have hC_U2 : C_U^2 = (b3 * θ2)^2 + b3^2 + (a3 * θ1)^2 + a3^2 := by
    rw [Real.sq_sqrt] <;> positivity

  have hG_sub : ∀ (x y : EuclideanSpace ℝ (Fin 2)), G x - G y = G (x - y) := by
    intro x y
    ext i
    fin_cases i <;> simp [hG_coord, Pi.sub_apply] <;> ring

  have hG_lip : ∀ (x y : EuclideanSpace ℝ (Fin 2)),
      ‖G x - G y‖ ≤ C_U * ‖x - y‖ := by
    intro x y
    let v := x - y
    have h_lin : G x - G y = G v := hG_sub x y
    rw [h_lin]
    have h1 : ‖G v‖^2 ≤ C_U^2 * ‖v‖^2 := by
      rw [pelican_euclidean_norm_sq (G v), pelican_euclidean_norm_sq v, hC_U2]
      have hcoord := hG_coord v
      rw [hcoord.1, hcoord.2]
      have hcs1 := pelican_cs2 (b3 * θ2) b3 (v 0) (v 1)
      have hcs2 := pelican_cs2 (a3 * θ1) a3 (v 0) (v 1)
      nlinarith
    have hv_nonneg : 0 ≤ ‖v‖ := by positivity
    have h_sqrt : Real.sqrt (‖G v‖^2) ≤ Real.sqrt (C_U^2 * ‖v‖^2) := Real.sqrt_le_sqrt h1
    have h_left : Real.sqrt (‖G v‖^2) = ‖G v‖ := by
      rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_nonneg (by positivity)]
    have h_right : Real.sqrt (C_U^2 * ‖v‖^2) = C_U * ‖v‖ := by
      have h_mul : Real.sqrt (C_U^2 * ‖v‖^2) = Real.sqrt (C_U^2) * Real.sqrt (‖v‖^2) := by
        rw [Real.sqrt_mul] <;> positivity
      rw [h_mul]
      have hF : Real.sqrt (C_U^2) = C_U := by
        rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_nonneg hC_U_nonneg]
      have hv : Real.sqrt (‖v‖^2) = ‖v‖ := by
        rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_nonneg hv_nonneg]
      rw [hF, hv] <;> ring
    rw [h_left, h_right] at h_sqrt
    exact h_sqrt

  -- =====================================================================
  -- Lipschitz bound for G_inv (L1-norm approach)
  -- =====================================================================
  set c0 := 1 / (θ3 - θ1) with hc0
  set c1 := 1 / (θ2 - θ3) with hc1
  set c2 := θ1 / (θ3 - θ1) with hc2
  set c3 := θ2 / (θ2 - θ3) with hc3

  let C_inv : ℝ := Real.sqrt 2 * (|c0| + |c1| + |c2| + |c3|)
  have hC_inv_nonneg : 0 ≤ C_inv := by positivity

  have h_l2_le_l1 : ∀ (z : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ |z 0| + |z 1| := by
    intro z
    have h : ‖z‖^2 ≤ (|z 0| + |z 1|)^2 := by
      rw [pelican_euclidean_norm_sq z]
      have h2 : (z 0)^2 + (z 1)^2 ≤ (|z 0| + |z 1|)^2 := by
        cases' abs_cases (z 0) with hz0 hz0 <;> cases' abs_cases (z 1) with hz1 hz1 <;> nlinarith
      exact h2
    have h3 : 0 ≤ |z 0| + |z 1| := by positivity
    have h4 : 0 ≤ ‖z‖ := norm_nonneg _
    exact (sq_le_sq₀ h4 h3).mp h

  have h_l1_le_sqrt2_l2 : ∀ (w : EuclideanSpace ℝ (Fin 2)), |w 0| + |w 1| ≤ Real.sqrt 2 * ‖w‖ := by
    intro w
    have h4 : (|w 0| + |w 1|)^2 ≤ 2 * ‖w‖^2 := by
      rw [pelican_euclidean_norm_sq w]
      have h51 : 0 ≤ (|w 0| - |w 1|)^2 := by positivity
      have h52 : |w 0|^2 = (w 0)^2 := by simp
      have h53 : |w 1|^2 = (w 1)^2 := by simp
      have h5 : 2 * |w 0| * |w 1| ≤ (w 0)^2 + (w 1)^2 := by
        have h : (|w 0| - |w 1|)^2 ≥ 0 := h51
        have h_expand : (|w 0| - |w 1|)^2 = |w 0|^2 + |w 1|^2 - 2 * |w 0| * |w 1| := by ring
        have h' : |w 0|^2 + |w 1|^2 - 2 * |w 0| * |w 1| ≥ 0 := by
          rw [h_expand] at h; exact h
        linarith [h52, h53]
      have h6 : (|w 0| + |w 1|)^2 = (w 0)^2 + (w 1)^2 + 2 * |w 0| * |w 1| := by
        have h7 : |w 0|^2 = (w 0)^2 := by simp
        have h8 : |w 1|^2 = (w 1)^2 := by simp
        calc (|w 0| + |w 1|)^2
          = |w 0|^2 + |w 1|^2 + 2 * |w 0| * |w 1| := by ring
        _ = (w 0)^2 + (w 1)^2 + 2 * |w 0| * |w 1| := by rw [h7, h8] <;> ring
      linarith
    have h5 : 0 ≤ |w 0| + |w 1| := by positivity
    have h6 : 0 ≤ Real.sqrt 2 * ‖w‖ := by positivity
    have h7 : (Real.sqrt 2 * ‖w‖)^2 = 2 * ‖w‖^2 := by
      have h8 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
      calc (Real.sqrt 2 * ‖w‖)^2
        = (Real.sqrt 2)^2 * ‖w‖^2 := by ring
      _ = 2 * ‖w‖^2 := by rw [h8] <;> ring
    have h9 : (|w 0| + |w 1|)^2 ≤ (Real.sqrt 2 * ‖w‖)^2 := by
      rw [h7]; exact h4
    exact (sq_le_sq₀ h5 h6).mp h9

  have hGinv_sub : ∀ (u v : EuclideanSpace ℝ (Fin 2)), G_inv u - G_inv v = G_inv (u - v) := by
    intro u v
    ext i
    fin_cases i <;> simp [hGinv_coord_simp, Pi.sub_apply] <;> ring

  have hGinv_lip : ∀ (u v : EuclideanSpace ℝ (Fin 2)),
      ‖G_inv u - G_inv v‖ ≤ C_inv * ‖u - v‖ := by
    intro u v
    set w := u - v with hw_def
    have h_lin : G_inv u - G_inv v = G_inv w := hGinv_sub u v
    rw [h_lin]
    have hcoord := hGinv_coord_simp w
    have h_eq0 : (G_inv w) 0 = c0 * w 0 - c1 * w 1 := by
      rw [hcoord.1]; simp [hc0, hc1] <;> ring
    have h_eq1 : (G_inv w) 1 = -c2 * w 0 + c3 * w 1 := by
      rw [hcoord.2]; simp [hc2, hc3] <;> ring
    have h1 : |(G_inv w) 0| ≤ |c0| * |w 0| + |c1| * |w 1| := by
      rw [h_eq0]
      have h : |c0 * w 0 - c1 * w 1| ≤ |c0 * w 0| + |c1 * w 1| := by exact abs_sub (c0 * w.ofLp 0) (c1 * w.ofLp 1)
      rw [abs_mul, abs_mul] at h
      exact h
    have h2 : |(G_inv w) 1| ≤ |c2| * |w 0| + |c3| * |w 1| := by
      rw [h_eq1]
      have h : |-c2 * w 0 + c3 * w 1| ≤ |-c2 * w 0| + |c3 * w 1| := by exact abs_add_le (-c2 * w.ofLp 0) (c3 * w.ofLp 1)
      have h' : |-c2 * w 0| = |c2| * |w 0| := by simp [abs_mul]
      rw [h', abs_mul] at h
      exact h
    have h_sum : |(G_inv w) 0| + |(G_inv w) 1| ≤
        (|c0| + |c1| + |c2| + |c3|) * (|w 0| + |w 1|) := by
      calc |(G_inv w) 0| + |(G_inv w) 1|
        ≤ (|c0| * |w 0| + |c1| * |w 1|) + (|c2| * |w 0| + |c3| * |w 1|) := add_le_add h1 h2
      _ = (|c0| + |c2|) * |w 0| + (|c1| + |c3|) * |w 1| := by ring
      _ ≤ (|c0| + |c1| + |c2| + |c3|) * (|w 0| + |w 1|) :=
        pelican_sum_ineq |c0| |c1| |c2| |c3| |w 0| |w 1|
          (by positivity) (by positivity) (by positivity) (by positivity)
          (by positivity) (by positivity)
    calc ‖G_inv w‖
      ≤ |(G_inv w) 0| + |(G_inv w) 1| := h_l2_le_l1 (G_inv w)
    _ ≤ (|c0| + |c1| + |c2| + |c3|) * (|w 0| + |w 1|) := h_sum
    _ ≤ (|c0| + |c1| + |c2| + |c3|) * (Real.sqrt 2 * ‖w‖) := by
      gcongr
      exact h_l1_le_sqrt2_l2 w
    _ = C_inv * ‖w‖ := by
      dsimp only [C_inv] <;> ring

  have hC_inv_pos : 0 < C_inv := by
    have h_c0_pos : 0 < c0 := by
      dsimp only [c0, hc0]
      apply div_pos zero_lt_one
      linarith
    have h_abs_pos : 0 < |c0| + |c1| + |c2| + |c3| := by
      have h1 : 0 < |c0| := abs_pos.mpr (ne_of_gt h_c0_pos)
      have h2 : 0 ≤ |c1| + |c2| + |c3| := by positivity
      linarith
    dsimp only [C_inv]
    exact mul_pos (by positivity) h_abs_pos

  have hC_inv_formula : C_inv = Real.sqrt 2 * (1 / (θ3 - θ1) + 1 / (θ2 - θ3) + θ1 / (θ3 - θ1) + θ2 / (θ2 - θ3)) := by
    dsimp only [C_inv, c0, c1, c2, c3]
    have h_pos1 : 0 < θ3 - θ1 := by linarith
    have h_pos2 : 0 < θ2 - θ3 := by linarith
    have h_nonneg1 : 0 ≤ θ1 := hθ1_in_unit.1
    have h_nonneg2 : 0 ≤ θ2 := hθ2_in_unit.1
    have h_abs1 : |1 / (θ3 - θ1)| = 1 / (θ3 - θ1) := by rw [abs_of_pos] <;> positivity
    have h_abs2 : |1 / (θ2 - θ3)| = 1 / (θ2 - θ3) := by rw [abs_of_pos] <;> positivity
    have h_abs3 : |θ1 / (θ3 - θ1)| = θ1 / (θ3 - θ1) := by rw [abs_of_nonneg] <;> positivity
    have h_abs4 : |θ2 / (θ2 - θ3)| = θ2 / (θ2 - θ3) := by rw [abs_of_nonneg] <;> positivity
    rw [h_abs1, h_abs2, h_abs3, h_abs4] <;> ring

  have hGinv_lip_dist : ∀ (u v : EuclideanSpace ℝ (Fin 2)),
      dist (G_inv u) (G_inv v) ≤ C_inv * dist u v := by
    intro u v
    have h1 : dist (G_inv u) (G_inv v) = ‖G_inv u - G_inv v‖ := by
      simp [dist_eq_norm]
    have h2 : dist u v = ‖u - v‖ := by simp [dist_eq_norm]
    rw [h1, h2]
    exact hGinv_lip u v

  -- =====================================================================
  -- Define transported data and constants
  -- =====================================================================
  let Pbar' : Set (EuclideanSpace ℝ (Fin 2)) := G '' Pbar
  let E3' : Set (EuclideanSpace ℝ (Fin 2)) := G '' E3
  let μE3' : Measure (EuclideanSpace ℝ (Fin 2)) := Measure.map G μE3
  let P_y' : ℝ → Set (EuclideanSpace ℝ (Fin 2)) := fun y => G '' (P_y y)
  let C_forward : ENNReal := ENNReal.ofReal ((4 * C_U + 6) ^ 2)
  let C_backward : ENNReal := ENNReal.ofReal ((4 * C_inv + 6) ^ 2)

  have hC_forward_ne_top : C_forward ≠ ⊤ := by
    simp [C_forward] <;> positivity
  have hC_backward_ne_top : C_backward ≠ ⊤ := by
    simp [C_backward] <;> positivity

  -- =====================================================================
  -- Boundedness
  -- =====================================================================
  have hPbar'_bdd : IsBounded Pbar' :=
    Defect36.lipschitz_image_bounded hC_U_nonneg hG_lip hPbar_bounded
  have hE3'_bdd : IsBounded E3' :=
    Defect36.lipschitz_image_bounded hC_U_nonneg hG_lip hE3_bounded
  have hPy'_bdd : ∀ y, IsBounded (P_y' y) := fun y =>
    Defect36.lipschitz_image_bounded hC_U_nonneg hG_lip (hPy_bounded y)

  -- =====================================================================
  -- Forward covering bounds
  -- =====================================================================
  have h_fwd_Pbar : ENat.toENNReal (dyadicCoveringNumber δ Pbar') ≤
      C_forward * ENat.toENNReal (dyadicCoveringNumber δ Pbar) :=
    Defect36.lipschitz_covering_upper hδ_pos hC_U_nonneg hG_lip hPbar_bounded

  have h_fwd_Py : ∀ y, ENat.toENNReal (dyadicCoveringNumber δ (P_y' y)) ≤
      C_forward * ENat.toENNReal (dyadicCoveringNumber δ (P_y y)) := fun y =>
    Defect36.lipschitz_covering_upper hδ_pos hC_U_nonneg hG_lip (hPy_bounded y)

  -- =====================================================================
  -- Backward covering bounds (apply Lipschitz covering to G_inv)
  -- =====================================================================
  have h_bwd_Pbar : ENat.toENNReal (dyadicCoveringNumber δ Pbar) ≤
      C_backward * ENat.toENNReal (dyadicCoveringNumber δ Pbar') := by
    have h1 : Pbar ⊆ G_inv '' Pbar' := by
      intro x hx
      refine ⟨G x, ⟨x, hx, rfl⟩, ?_⟩
      exact hG_inv1 x
    have h2 : ENat.toENNReal (dyadicCoveringNumber δ Pbar) ≤
        ENat.toENNReal (dyadicCoveringNumber δ (G_inv '' Pbar')) :=
      ENat.toENNReal_mono (dyadicCoveringNumber_mono h1)
    have h3 := Defect36.lipschitz_covering_upper hδ_pos hC_inv_nonneg hGinv_lip hPbar'_bdd
    exact h2.trans h3

  have h_bwd_Py : ∀ y, ENat.toENNReal (dyadicCoveringNumber δ (P_y y)) ≤
      C_backward * ENat.toENNReal (dyadicCoveringNumber δ (P_y' y)) := by
    intro y
    have h1 : P_y y ⊆ G_inv '' (P_y' y) := by
      intro x hx
      refine ⟨G x, ⟨x, hx, rfl⟩, ?_⟩
      exact hG_inv1 x
    have h2 : ENat.toENNReal (dyadicCoveringNumber δ (P_y y)) ≤
        ENat.toENNReal (dyadicCoveringNumber δ (G_inv '' (P_y' y))) :=
      ENat.toENNReal_mono (dyadicCoveringNumber_mono h1)
    have h3 := Defect36.lipschitz_covering_upper hδ_pos hC_inv_nonneg hGinv_lip (hPy'_bdd y)
    exact h2.trans h3

  -- =====================================================================
  -- Homeomorphism and measure support
  -- =====================================================================
  let hG_homeo : Homeomorph (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
    { toFun := G
      invFun := G_inv
      left_inv := hG_inv1
      right_inv := hG_inv2
      continuous_toFun := hG_cont
      continuous_invFun := hGinv_cont }

  have hG_open : IsOpenMap G := hG_homeo.isOpenMap
  have hG_meas : Measurable G := hG_cont.measurable

  have h_support : μE3'.support = E3' := by
    have h_support_map : (Measure.map G μE3).support = G '' μE3.support := by
      ext y
      constructor
      · intro h
        let x := G_inv y
        have hGx : G x = y := hG_inv2 y
        have hx : x ∈ μE3.support := by
          rw [Measure.mem_support_iff_forall x]
          intro U hU
          rcases mem_nhds_iff.mp hU with ⟨V, hV_sub, hV_open, hxV⟩
          have hGV_open : IsOpen (G '' V) := hG_open V hV_open
          have hyV : y ∈ G '' V := by
            rw [←hGx]; exact ⟨x, hxV, rfl⟩
          have h_nhds : G '' V ∈ nhds y := hGV_open.mem_nhds hyV
          have h_pos1 : 0 < (Measure.map G μE3) (G '' V) :=
            (Measure.mem_support_iff_forall y).mp h (G '' V) h_nhds
          have h_eq : (Measure.map G μE3) (G '' V) = μE3 (G ⁻¹' (G '' V)) :=
            Measure.map_apply hG_meas hGV_open.measurableSet
          rw [h_eq] at h_pos1
          have h_preimg : G ⁻¹' (G '' V) = V := by
            ext z; simp [hG_inj]
          rw [h_preimg] at h_pos1
          have h_le : μE3 V ≤ μE3 U := measure_mono hV_sub
          exact lt_of_lt_of_le h_pos1 h_le
        exact ⟨x, hx, hGx⟩
      · rintro ⟨x, hx, rfl⟩
        rw [Measure.mem_support_iff_forall (G x)]
        intro V hV
        rcases mem_nhds_iff.mp hV with ⟨W, hW_sub, hW_open, hyW⟩
        have h_preimg_open : IsOpen (G ⁻¹' W) := hW_open.preimage hG_cont
        have hxW : x ∈ G ⁻¹' W := hyW
        have h_preimg_nhds : G ⁻¹' W ∈ nhds x := h_preimg_open.mem_nhds hxW
        have h_pos1 : 0 < μE3 (G ⁻¹' W) :=
          (Measure.mem_support_iff_forall x).mp hx (G ⁻¹' W) h_preimg_nhds
        have h_eq : (Measure.map G μE3) W = μE3 (G ⁻¹' W) :=
          Measure.map_apply hG_meas hW_open.measurableSet
        have h_pos2 : 0 < (Measure.map G μE3) W := by
          rw [h_eq]; exact h_pos1
        have h_le : (Measure.map G μE3) W ≤ (Measure.map G μE3) V := measure_mono hW_sub
        exact lt_of_lt_of_le h_pos2 h_le
    rw [h_support_map, hμE3_support]

  -- =====================================================================
  -- Probability measure
  -- =====================================================================
  have h_prob : IsProbabilityMeasure μE3' := by
    have hG_aemeas : AEMeasurable G μE3 := hG_meas.aemeasurable
    exact Measure.isProbabilityMeasure_map hG_aemeas

  -- =====================================================================
  -- Projection identity and forward covering bound
  --
  -- For y ≠ θ2, the cross-ratio identity gives:
  --   (a3/a_y) * π_y(p) = x(y) * (Gp)_0 + (Gp)_1 = π_{x(y)}(Gp)
  -- Therefore:
  --   π_{x(y)}(G '' E3) = scaleSet (a3/a_y) (π_y(E3))
  --
  -- Applying scalar_covering_upper with M = |a3/a_y|:
  --   N(π_{x(y)}(E3')) ≤ (⌈M⌉+1) * N(π_y(E3))
  -- =====================================================================
  have h_proj_transfer : ∀ (y : ℝ), y ≠ θ2 →
      let a3 := (θ2 - θ3) / (θ2 - θ1)
      let a_y := (θ2 - y) / (θ2 - θ1)
      let fullLambda := a3 / a_y
      let M := |fullLambda|
      Nreal δ (projectionSet (x y) E3') ≤
        (Nat.ceil M + 1 : ENNReal) * Nreal δ (projectionSet y E3) := by
    intro y hy
    dsimp only
    set a3 := (θ2 - θ3) / (θ2 - θ1) with ha3
    set a_y := (θ2 - y) / (θ2 - θ1) with hay
    set fullLambda := a3 / a_y with hfl
    set M := |fullLambda| with hM

    have hay_ne : a_y ≠ 0 := by
      dsimp only [a_y]
      have h : (θ2 - y) / (θ2 - θ1) ≠ 0 := by
        apply div_ne_zero
        · exact sub_ne_zero.mpr (Ne.symm hy)
        · exact hD_ne
      exact h

    -- Cross-ratio identity: x y * (G p) 0 + (G p) 1 = fullLambda * (p 0 * y + p 1)
    have h_cross : ∀ (p : EuclideanSpace ℝ (Fin 2)),
        x y * (G p) 0 + (G p) 1 = fullLambda * (p 0 * y + p 1) := by
      intro p
      have hgp0 : (G p) 0 = b3 * (p 0 * θ2 + p 1) := (hG_coord p).1
      have hgp1 : (G p) 1 = a3 * (p 0 * θ1 + p 1) := (hG_coord p).2
      rw [hgp0, hgp1]
      dsimp only [fullLambda, a3, a_y, x, b3]
      field_simp [hD_ne, h31_ne, h23_ne, hy] <;> ring

    -- Set identity: projectionSet (x y) E3' = scaleSet fullLambda (projectionSet y E3)
    have hE3'_def : E3' = G '' E3 := rfl
    have h_set_id : projectionSet (x y) E3' = scaleSet fullLambda (projectionSet y E3) := by
      ext z
      simp only [projectionSet, affineProjection, scaleSet, Set.mem_image, hE3'_def]
      constructor
      · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
        refine ⟨p 0 * y + p 1, ⟨p, hp, rfl⟩, ?_⟩
        have h := h_cross p
        have h_comm : x y * (G p) 0 = (G p) 0 * x y := by ring
        rw [h_comm] at h
        exact h.symm
      · rintro ⟨w, ⟨p, hp, rfl⟩, rfl⟩
        refine ⟨G p, ⟨p, hp, rfl⟩, ?_⟩
        have h := h_cross p
        have h_comm : x y * (G p) 0 = (G p) 0 * x y := by ring
        rw [h_comm] at h
        exact h

    -- Boundedness of projectionSet y E3
    have h_proj_bdd : IsBounded (projectionSet y E3) :=
      projectionSet.bounded y hE3_bounded

    -- Apply scalar covering bound
    rw [h_set_id]
    have hM_nonneg : 0 ≤ M := abs_nonneg fullLambda
    have h_abs : |fullLambda| ≤ M := by
      simpa [hM] using le_refl M
    exact ProductLikeIncidence.FourSectorChart.scalar_covering_upper
      hδ_pos hM_nonneg h_proj_bdd h_abs

  -- =====================================================================
  -- Assemble output
  -- =====================================================================
  exact ⟨G, G_inv, x, Pbar', E3', μE3', P_y', C_forward, C_backward, C_inv,
    hG_formula, hG_inv1, hG_inv2, hG_inj, hx_formula, rfl, rfl, rfl,
    (fun _ => rfl), h_support, h_prob, hPbar'_bdd, hE3'_bdd, hPy'_bdd,
    hC_forward_ne_top, hC_backward_ne_top, h_fwd_Pbar, h_fwd_Py,
    h_bwd_Pbar, h_bwd_Py, hC_inv_nonneg, hC_inv_formula, hGinv_lip_dist, h_proj_transfer⟩

end ProductLikeIncidence.ProductReduction
