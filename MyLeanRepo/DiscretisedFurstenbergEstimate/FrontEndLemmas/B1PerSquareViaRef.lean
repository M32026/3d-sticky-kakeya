module

/-
  B1 per-square upper bound via Ref_fin injection.

  Given a swap-aware reference set Ref_fin with transported S-set and separation,
  inject each config fibre into Ref_fin ∩ coarse Q and bound using the S-set
  property plus the global card upper.

  Whiteprint node: b1_per_square_via_ref
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.B1_Sublemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1CardBounds
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.SquareGeometry
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionOnScales
open SquareGeometry

attribute [local instance] Classical.propDecidable

abbrev NiceConfig n s C₁ M := CombiningTheorem.NiceConfiguration n s C₁ M
abbrev DSquare n := DiscretisedFurstenbergEstimate.DyadicSquare n

/-- Helper: rpow product simplification. -/
private lemma rpow_mul_helper {x : ℝ} (hx : 0 < x) (a b c : ℝ) :
    Real.rpow x a * Real.rpow x b * Real.rpow x c = Real.rpow x (a + b + c) := by
  have h1 : Real.rpow x a * Real.rpow x b = Real.rpow x (a + b) :=
    (Real.rpow_add hx a b).symm
  rw [h1]
  have h2 : Real.rpow x (a + b) * Real.rpow x c = Real.rpow x (a + b + c) :=
    (Real.rpow_add hx (a + b) c).symm
  exact h2

/-- Helper: (Δ^2)^a = Δ^(2a). -/
private lemma rpow_delta2 {Δ : ℝ} (hΔ_pos : 0 < Δ) (a : ℝ) :
    Real.rpow (Δ ^ 2) a = Real.rpow Δ (2 * a) := by
  have h3 : Real.rpow Δ (2 * a) = Real.rpow (Real.rpow Δ 2) a :=
    Real.rpow_mul hΔ_pos.le 2 a
  have h4 : Real.rpow Δ 2 = Δ ^ 2 := by simp [Real.rpow_two]
  rw [h4] at h3
  exact h3.symm

/-- Per-square upper bound via injection into Ref_fin ∩ coarse square Q. -/
lemma b1_per_square_upper_via_ref
    {n m : ℕ} (hnm : m ≤ n)
    {s C₁ : ℝ} {M : ℕ}
    (config : NiceConfig n s C₁ M)
    {Δ δ_n u ε point_int_run C_Pbar : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_n_pos : 0 < δ_n)
    (hδ_n_eq : δ_n = dyadicDelta n)
    (hδ_n_eq2 : δ_n = Δ ^ 2)
    (hΔ_eq : Δ = dyadicDelta m)
    {Pbar : Finset EuclideanPlane}
    {Ref_fin : Finset EuclideanPlane}
    (hRef_card : Ref_fin.card = Pbar.card)
    (hPbar_card : (Pbar.card : ℝ) ≤ 100 * Real.rpow δ_n (-u))
    (hRef_sset : IsDeltaSSet δ_n u C_Pbar (Ref_fin : Set EuclideanPlane))
    (hRef_sep : Set.Pairwise (Ref_fin : Set EuclideanPlane) (fun p q => δ_n ≤ dist p q))
    {P_oriented : Set EuclideanPlane}
    (hP_oriented_sub_Ref : P_oriented ⊆ (Ref_fin : Set EuclideanPlane))
    (h_squares_meet : ∀ (q : DSquare n), q ∈ config.P₀ →
        ((q.toSet : Set EuclideanPlane) ∩ P_oriented).Nonempty)
    (hC_Pbar_bound : C_Pbar ≤ Real.rpow δ_n (-point_int_run))
    (hpoint_int_run_gap : 2 * point_int_run + ε / 4 ≤ 7 * ε / 20)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (hconfig_P0_nonempty : config.P₀.Nonempty) :
    ∀ Q ∈ config.P₀.image (InductionConfigurations.containingSquare hnm),
      ((config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card : ℝ) ≤
        Real.rpow Δ (-u - 3 * ε / 5) := by
  let csq := InductionConfigurations.containingSquare hnm
  let coarseP₀_orig : Finset (DSquare m) := config.P₀.image csq
  intro Q hQ
  classical
  let fibre := config.P₀.filter (fun p => csq p = Q)
  let f : DSquare n → EuclideanPlane := fun q =>
    if h : q ∈ config.P₀ then (h_squares_meet q h).some else (0 : EuclideanPlane)
  have hf1 : ∀ q ∈ config.P₀, f q ∈ (q.toSet : Set EuclideanPlane) ∧ f q ∈ P_oriented := by
    intro q hq
    have h_eq : f q = (h_squares_meet q hq).some := by
      unfold f; rw [dif_pos hq] <;> rfl
    rw [h_eq]; exact Classical.choose_spec (h_squares_meet q hq)
  have hf_inj : Set.InjOn f (config.P₀ : Set (DSquare n)) := by
    intro q1 hq1 q2 hq2 h_eq
    by_contra hne
    have h_disj : Disjoint (q1.toSet : Set EuclideanPlane) (q2.toSet : Set EuclideanPlane) :=
      dyadicSquare_toSet_disjoint hne
    have h1 : f q1 ∈ (q1.toSet : Set EuclideanPlane) := (hf1 q1 hq1).1
    have h2 : f q2 ∈ (q2.toSet : Set EuclideanPlane) := (hf1 q2 hq2).1
    rw [h_eq] at h1
    exact Set.disjoint_left.mp h_disj h1 h2
  let c := squareCenter Δ Q
  have hQ_sub : (Q.toSet : Set EuclideanPlane) ⊆ Metric.closedBall c Δ :=
    dyadicSquare_covered_by_center hΔ_pos hΔ_eq Q
  let R_ball := Ref_fin.filter (fun p => p ∈ Metric.closedBall c Δ)
  have h_fibre_inj : ∀ q ∈ fibre, f q ∈ (R_ball : Set EuclideanPlane) := by
    intro q hq
    have hq' : q ∈ config.P₀ := (Finset.mem_filter.mp hq).1
    have hcsq : csq q = Q := (Finset.mem_filter.mp hq).2
    have h1 : f q ∈ (q.toSet : Set EuclideanPlane) := (hf1 q hq').1
    have h2 : f q ∈ P_oriented := (hf1 q hq').2
    have h3 : f q ∈ (Ref_fin : Set EuclideanPlane) := hP_oriented_sub_Ref h2
    have h4 : (q.toSet : Set EuclideanPlane) ⊆ (Q.toSet : Set EuclideanPlane) := by
      rw [←hcsq]; exact fine_square_subset_coarse hnm q
    have h5 : f q ∈ (Q.toSet : Set EuclideanPlane) := h4 h1
    have h6 : f q ∈ Metric.closedBall c Δ := hQ_sub h5
    exact Finset.mem_filter.mpr ⟨h3, h6⟩
  have h_fibre_card_le : fibre.card ≤ R_ball.card := by
    have h_image : fibre.image f ⊆ R_ball := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨q, hq, rfl⟩
      exact h_fibre_inj q hq
    have h_fibre_sub : (fibre : Set (DSquare n)) ⊆ (config.P₀ : Set (DSquare n)) := by
      intro z hz; exact (Finset.mem_filter.mp hz).1
    have h_inj_on : Set.InjOn f (fibre : Set (DSquare n)) :=
      hf_inj.mono h_fibre_sub
    have h_card_img : (fibre.image f).card = fibre.card :=
      Finset.card_image_of_injOn h_inj_on
    rw [←h_card_img]
    exact Finset.card_le_card h_image
  have hR_sep : ∀ p ∈ R_ball, ∀ q ∈ R_ball, p ≠ q → δ_n ≤ dist p q := by
    intro p hp q hq hne
    have hp' : p ∈ (Ref_fin : Set EuclideanPlane) := (Finset.mem_filter.mp hp).1
    have hq' : q ∈ (Ref_fin : Set EuclideanPlane) := (Finset.mem_filter.mp hq).1
    exact hRef_sep hp' hq' hne
  have h_card_le_nat : (R_ball.card : ℕ∞) ≤ 81 * Metric.externalCoveringNumber δ_n.toNNReal (R_ball : Set EuclideanPlane) :=
    separated_card_le_ncover hδ_n_pos hR_sep
  have hδ_n_le_Δ : δ_n ≤ Δ := by
    rw [hδ_n_eq2] <;> nlinarith [hΔ_pos, hΔ_lt_one]
  have h_sset_ball : Metric.externalCoveringNumber δ_n.toNNReal ((Ref_fin : Set EuclideanPlane) ∩ Metric.closedBall c Δ) ≤
      ENNReal.ofReal C_Pbar * (ENNReal.ofReal Δ) ^ u * Metric.externalCoveringNumber δ_n.toNNReal (Ref_fin : Set EuclideanPlane) :=
    hRef_sset.2.2.2.2 c Δ hδ_n_le_Δ
  have hRball_sub : (R_ball : Set EuclideanPlane) ⊆ (Ref_fin : Set EuclideanPlane) ∩ Metric.closedBall c Δ := by
    intro x hx
    have h1 : x ∈ (Ref_fin : Set EuclideanPlane) := (Finset.mem_filter.mp hx).1
    have h2 : x ∈ Metric.closedBall c Δ := (Finset.mem_filter.mp hx).2
    exact ⟨h1, h2⟩
  have h_ncover_Rball : Metric.externalCoveringNumber δ_n.toNNReal (R_ball : Set EuclideanPlane) ≤
      Metric.externalCoveringNumber δ_n.toNNReal ((Ref_fin : Set EuclideanPlane) ∩ Metric.closedBall c Δ) :=
    Metric.externalCoveringNumber_mono_set hRball_sub
  have h_ncover_Ref_le_card : Metric.externalCoveringNumber δ_n.toNNReal (Ref_fin : Set EuclideanPlane) ≤ (Ref_fin.card : ENNReal) := by
    have hcover : Metric.IsCover δ_n.toNNReal (Ref_fin : Set EuclideanPlane) (Ref_fin : Set EuclideanPlane) := by
      intro x hx; exact ⟨x, hx, by simp [Metric.mem_closedBall]⟩
    have h : Metric.externalCoveringNumber δ_n.toNNReal (Ref_fin : Set EuclideanPlane) ≤ (Ref_fin : Set EuclideanPlane).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hcover
    have h' : (Ref_fin : Set EuclideanPlane).encard = (Ref_fin.card : ℕ∞) := by simp
    rw [h'] at h
    exact_mod_cast h
  have hC_Pbar_bound' : C_Pbar ≤ Real.rpow Δ (-2 * point_int_run) := by
    rw [hδ_n_eq2] at hC_Pbar_bound
    have h_exp1 : Real.rpow (Δ ^ 2) (-point_int_run) = Real.rpow Δ (2 * -point_int_run) :=
      rpow_delta2 hΔ_pos (-point_int_run)
    have h_exp2 : (2 * -point_int_run : ℝ) = -2 * point_int_run := by ring
    rw [h_exp1, h_exp2] at hC_Pbar_bound
    exact hC_Pbar_bound
  have hRef_card_upper2 : (Ref_fin.card : ℝ) ≤ Real.rpow Δ (-2 * u - ε / 4) := by
    have h1 : (Ref_fin.card : ℝ) ≤ 100 * Real.rpow Δ (-2 * u) := by
      have h2 : (Ref_fin.card : ℝ) ≤ 100 * Real.rpow δ_n (-u) := by
        rw [hRef_card]; exact hPbar_card
      rw [hδ_n_eq2] at h2
      have h_exp1 : Real.rpow (Δ ^ 2) (-u) = Real.rpow Δ (2 * -u) := rpow_delta2 hΔ_pos (-u)
      have h_exp2 : (2 * -u : ℝ) = -2 * u := by ring
      rw [h_exp1, h_exp2] at h2
      exact h2
    have h4 : (100 : ℝ) ≤ Real.rpow Δ (-ε / 4) := by
      have h5 : Real.rpow Δ (ε / 4) ≤ 1 / 100 := h_small
      have h6 : Real.rpow Δ (-ε / 4) = (Real.rpow Δ (ε / 4))⁻¹ := by
        have h7 : -ε / 4 = -(ε / 4) := by ring
        rw [h7]; exact Real.rpow_neg hΔ_pos.le (ε / 4)
      rw [h6]
      have h8 : 0 < Real.rpow Δ (ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
      have h9 : (Real.rpow Δ (ε / 4))⁻¹ ≥ (1 / 100 : ℝ)⁻¹ := by gcongr
      norm_num at h9 ⊢; exact h9
    have h_pos1 : 0 ≤ Real.rpow Δ (-2 * u) := Real.rpow_nonneg hΔ_pos.le _
    calc (Ref_fin.card : ℝ)
      ≤ 100 * Real.rpow Δ (-2 * u) := h1
    _ ≤ Real.rpow Δ (-ε / 4) * Real.rpow Δ (-2 * u) := by gcongr
    _ = Real.rpow Δ (-2 * u - ε / 4) := by
      have h_comm : Real.rpow Δ (-ε / 4) * Real.rpow Δ (-2 * u) =
          Real.rpow Δ (-2 * u) * Real.rpow Δ (-ε / 4) := by ring
      rw [h_comm]
      have h_add : Real.rpow Δ ((-2 * u) + (-ε / 4)) =
          Real.rpow Δ (-2 * u) * Real.rpow Δ (-ε / 4) := Real.rpow_add hΔ_pos (-2 * u) (-ε / 4)
      have h_sum : (-2 * u) + (-ε / 4) = -2 * u - ε / 4 := by ring
      rw [h_sum] at h_add
      exact h_add.symm
  have h_small_gap : Real.rpow Δ (7 * ε / 20 - 2 * point_int_run) ≤ 1 / 81 := by
    have h1 : ε / 4 ≤ 7 * ε / 20 - 2 * point_int_run := by linarith
    have h2 : Real.rpow Δ (7 * ε / 20 - 2 * point_int_run) ≤ Real.rpow Δ (ε / 4) :=
      Real.rpow_le_rpow_of_exponent_ge hΔ_pos (by linarith [hΔ_lt_one]) h1
    have h3 : Real.rpow Δ (ε / 4) ≤ 1 / 100 := h_small
    linarith
  have h_pos_u : 0 ≤ Real.rpow Δ u := Real.rpow_nonneg hΔ_pos.le _
  have h_pos_C : 0 ≤ C_Pbar := by linarith [hRef_sset.2.2.1]
  have h4 : (81 : ℝ) * C_Pbar * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4) ≤ Real.rpow Δ (-u - 3 * ε / 5) := by
    have h5 : C_Pbar ≤ Real.rpow Δ (-2 * point_int_run) := hC_Pbar_bound'
    have h6 : (81 : ℝ) * C_Pbar * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4) ≤
        (81 : ℝ) * Real.rpow Δ (-2 * point_int_run) * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4) := by
      gcongr <;> linarith
    have h8 : Real.rpow Δ (-2 * point_int_run) * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4) =
        Real.rpow Δ ((-2 * point_int_run) + u + (-2 * u - ε / 4)) :=
      rpow_mul_helper hΔ_pos (-2 * point_int_run) u (-2 * u - ε / 4)
    have h9 : (-2 * point_int_run) + u + (-2 * u - ε / 4) = -u - ε / 4 - 2 * point_int_run := by ring
    have h10 : Real.rpow Δ (-2 * point_int_run) * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4) =
        Real.rpow Δ (-u - ε / 4 - 2 * point_int_run) := by
      rw [h8, h9]
    have h_assoc : (81 : ℝ) * Real.rpow Δ (-2 * point_int_run) * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4) =
        (81 : ℝ) * (Real.rpow Δ (-2 * point_int_run) * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4)) := by ring
    have h7 : (81 : ℝ) * Real.rpow Δ (-2 * point_int_run) * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4) =
        (81 : ℝ) * Real.rpow Δ (-u - ε / 4 - 2 * point_int_run) := by
      rw [h_assoc, h10]
    rw [h7] at h6
    have h10 : (81 : ℝ) * Real.rpow Δ (-u - ε / 4 - 2 * point_int_run) ≤ Real.rpow Δ (-u - 3 * ε / 5) := by
      have h11 : -u - ε / 4 - 2 * point_int_run = -u - 3 * ε / 5 + (7 * ε / 20 - 2 * point_int_run) := by ring
      rw [h11]
      have h12 : Real.rpow Δ (-u - 3 * ε / 5 + (7 * ε / 20 - 2 * point_int_run)) =
          Real.rpow Δ (-u - 3 * ε / 5) * Real.rpow Δ (7 * ε / 20 - 2 * point_int_run) := by
        have h_add : Real.rpow Δ ((-u - 3 * ε / 5) + (7 * ε / 20 - 2 * point_int_run)) =
            Real.rpow Δ (-u - 3 * ε / 5) * Real.rpow Δ (7 * ε / 20 - 2 * point_int_run) :=
          Real.rpow_add hΔ_pos (-u - 3 * ε / 5) (7 * ε / 20 - 2 * point_int_run)
        exact h_add
      rw [h12]
      have h13 : 0 ≤ Real.rpow Δ (-u - 3 * ε / 5) := Real.rpow_nonneg hΔ_pos.le _
      have h14 : 81 * Real.rpow Δ (7 * ε / 20 - 2 * point_int_run) ≤ 1 := by
        calc 81 * Real.rpow Δ (7 * ε / 20 - 2 * point_int_run)
          ≤ 81 * (1 / 81 : ℝ) := by gcongr
        _ = 1 := by norm_num
      nlinarith
    exact le_trans h6 h10
  have h_card_le_ennreal : (R_ball.card : ENNReal) ≤
      (81 : ENNReal) * (Metric.externalCoveringNumber δ_n.toNNReal (R_ball : Set EuclideanPlane) : ENNReal) := by
    exact_mod_cast h_card_le_nat
  have h2_ncover : (Metric.externalCoveringNumber δ_n.toNNReal (R_ball : Set EuclideanPlane) : ENNReal) ≤
      (Metric.externalCoveringNumber δ_n.toNNReal ((Ref_fin : Set EuclideanPlane) ∩ Metric.closedBall c Δ) : ENNReal) :=
    by exact_mod_cast h_ncover_Rball
  have h_main_ennreal : (R_ball.card : ENNReal) ≤
      (81 : ENNReal) * ENNReal.ofReal C_Pbar * (ENNReal.ofReal Δ) ^ u * (Ref_fin.card : ENNReal) := by
    calc (R_ball.card : ENNReal)
      ≤ (81 : ENNReal) * (Metric.externalCoveringNumber δ_n.toNNReal (R_ball : Set EuclideanPlane) : ENNReal) :=
        h_card_le_ennreal
    _ ≤ (81 : ENNReal) * (Metric.externalCoveringNumber δ_n.toNNReal ((Ref_fin : Set EuclideanPlane) ∩ Metric.closedBall c Δ) : ENNReal) := by
        gcongr
    _ ≤ (81 : ENNReal) * (ENNReal.ofReal C_Pbar * (ENNReal.ofReal Δ) ^ u * (Metric.externalCoveringNumber δ_n.toNNReal (Ref_fin : Set EuclideanPlane) : ENNReal)) := by
        gcongr
    _ = (81 : ENNReal) * ENNReal.ofReal C_Pbar * (ENNReal.ofReal Δ) ^ u * (Metric.externalCoveringNumber δ_n.toNNReal (Ref_fin : Set EuclideanPlane) : ENNReal) := by ring
    _ ≤ (81 : ENNReal) * ENNReal.ofReal C_Pbar * (ENNReal.ofReal Δ) ^ u * (Ref_fin.card : ENNReal) := by
        gcongr
  have hC_nonneg : 0 ≤ C_Pbar := by linarith [hRef_sset.2.2.1]
  have h_rpow_eq : (ENNReal.ofReal Δ) ^ u = ENNReal.ofReal (Real.rpow Δ u) :=
    ENNReal.ofReal_rpow_of_pos hΔ_pos
  have h_eq : (81 : ENNReal) * ENNReal.ofReal C_Pbar * (ENNReal.ofReal Δ) ^ u * (Ref_fin.card : ENNReal) =
      ENNReal.ofReal ((81 : ℝ) * C_Pbar * Real.rpow Δ u * (Ref_fin.card : ℝ)) := by
    rw [h_rpow_eq]
    have h81 : (81 : ENNReal) = ENNReal.ofReal (81 : ℝ) := by simp
    have hcard : (Ref_fin.card : ENNReal) = ENNReal.ofReal (Ref_fin.card : ℝ) := by
      simp [ENNReal.ofReal_natCast]
    rw [h81, hcard]
    rw [←ENNReal.ofReal_mul (by positivity), ←ENNReal.ofReal_mul (by positivity), ←ENNReal.ofReal_mul (by positivity)]
    <;> ring
  have h_card_eq : (R_ball.card : ENNReal) = ENNReal.ofReal (R_ball.card : ℝ) := by
    simp [ENNReal.ofReal_natCast]
  have h_main_real : (R_ball.card : ℝ) ≤ (81 : ℝ) * C_Pbar * Real.rpow Δ u * (Ref_fin.card : ℝ) := by
    have h_main2 : (R_ball.card : ENNReal) ≤ ENNReal.ofReal ((81 : ℝ) * C_Pbar * Real.rpow Δ u * (Ref_fin.card : ℝ)) := by
      rw [h_eq] at h_main_ennreal
      exact h_main_ennreal
    have h_rhs_fin : ENNReal.ofReal ((81 : ℝ) * C_Pbar * Real.rpow Δ u * (Ref_fin.card : ℝ)) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have h_toReal := ENNReal.toReal_mono h_rhs_fin h_main2
    have h_left : ENNReal.toReal (R_ball.card : ENNReal) = (R_ball.card : ℝ) := by simp
    have h_right : ENNReal.toReal (ENNReal.ofReal ((81 : ℝ) * C_Pbar * Real.rpow Δ u * (Ref_fin.card : ℝ))) =
        (81 : ℝ) * C_Pbar * Real.rpow Δ u * (Ref_fin.card : ℝ) := by
      rw [ENNReal.toReal_ofReal (by positivity)]
    rw [h_left, h_right] at h_toReal
    exact h_toReal
  have h_final : (fibre.card : ℝ) ≤ Real.rpow Δ (-u - 3 * ε / 5) := by
    have h1 : (fibre.card : ℝ) ≤ (R_ball.card : ℝ) := by exact_mod_cast h_fibre_card_le
    have h2 : (R_ball.card : ℝ) ≤ (81 : ℝ) * C_Pbar * Real.rpow Δ u * (Ref_fin.card : ℝ) := h_main_real
    have h3 : (Ref_fin.card : ℝ) ≤ Real.rpow Δ (-2 * u - ε / 4) := hRef_card_upper2
    have h_pos : 0 ≤ (81 : ℝ) * C_Pbar * Real.rpow Δ u := by positivity
    calc (fibre.card : ℝ)
      ≤ (R_ball.card : ℝ) := h1
    _ ≤ (81 : ℝ) * C_Pbar * Real.rpow Δ u * (Ref_fin.card : ℝ) := h2
    _ ≤ (81 : ℝ) * C_Pbar * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4) := by gcongr
    _ ≤ Real.rpow Δ (-u - 3 * ε / 5) := h4
  exact h_final

end DirecretisedFurstenbergEstimate.FrontEndLemmas
