module

/-
  B1 Card Bounds.

  Proves the cardinality bounds required by B1BridgeDecomposition:
  - b1_coarse_card_upper: |coarseP₀| ≤ Δ^{-t-ε/2} (via sqrt covering + doubling)
  - b1_coarse_card_lower: |coarseP₀| ≥ Δ^{-u+ε} (via local S-set density)
  - b1_fine_card_upper: |P₀| ≤ Δ^{-2u-ε/4} (via source cardP, trivial for small Δ)
  - separated_card_le_ncover: generic helper |P| ≤ 81 · Ncover(δ,P)

  Whiteprint node: improved_incidence_general / b1_hard_bounds
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.RegularB1Bounds
public import MyLeanRepo.RobustKaufmanProjection.Basics
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open RobustKaufmanProjection

/-! ### Coarse card upper bound -/

/-- Coarse card upper bound: from sqrt-regularity + doubling. -/
lemma b1_coarse_card_upper
    {m : ℕ} {Δ δ t ε εA : ℝ}
    (hΔ_eq : Δ = dyadicDelta m)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (ht_pos : 0 < t) (hε_pos : 0 < ε) (hεA_pos : 0 < εA)
    (hεA_lt : 2 * εA < ε / 2)
    {P : Set EuclideanPlane} {Pfin : Finset EuclideanPlane}
    {coarseP₀ : Finset (DyadicSquare m)}
    (h_match_backward : ∀ q ∈ Pfin, ∃ p ∈ P, dist q p ≤ δ)
    (h_intersect : ∀ Q ∈ coarseP₀,
      ((Pfin : Set EuclideanPlane) ∩ (Q.toSet : Set EuclideanPlane)).Nonempty)
    (h_sqrt_reg : Metric.externalCoveringNumber Δ.toNNReal P ≤
        ENNReal.ofReal (Real.rpow Δ (-(t + 2 * εA))))
    (hΔ_small : Δ ≤ Real.rpow (1 / 81) (1 / (ε / 2 - 2 * εA))) :
    (coarseP₀.card : ℝ) ≤ Real.rpow Δ (-t - ε / 2) := by
  have h_a_pos : 0 < ε / 2 - 2 * εA := by linarith
  have h1 : (coarseP₀.card : ℕ∞) ≤
      81 * Metric.externalCoveringNumber Δ.toNNReal P :=
    coarse_card_upper hΔ_eq hΔ_pos hδ_pos hδ_le_Δ h_match_backward h_intersect
  have h2 : (coarseP₀.card : ENNReal) ≤
      (81 : ENNReal) * Metric.externalCoveringNumber Δ.toNNReal P := by
    exact_mod_cast h1
  have h3 : (coarseP₀.card : ENNReal) ≤
      (81 : ENNReal) * ENNReal.ofReal (Real.rpow Δ (-(t + 2 * εA))) := by
    calc (coarseP₀.card : ENNReal)
      ≤ (81 : ENNReal) * Metric.externalCoveringNumber Δ.toNNReal P := h2
    _ ≤ (81 : ENNReal) * ENNReal.ofReal (Real.rpow Δ (-(t + 2 * εA))) := by gcongr
  have h_rhs_nonneg : 0 ≤ 81 * Real.rpow Δ (-(t + 2 * εA)) := by
    have h_pos : 0 ≤ Real.rpow Δ (-(t + 2 * εA)) := Real.rpow_nonneg hΔ_pos.le _
    exact mul_nonneg (by norm_num) h_pos
  have h3' : (81 : ENNReal) * ENNReal.ofReal (Real.rpow Δ (-(t + 2 * εA))) =
      ENNReal.ofReal (81 * Real.rpow Δ (-(t + 2 * εA))) := by
    have h_mul : ENNReal.ofReal ((81 : ℝ) * Real.rpow Δ (-(t + 2 * εA))) =
        ENNReal.ofReal (81 : ℝ) * ENNReal.ofReal (Real.rpow Δ (-(t + 2 * εA))) :=
      ENNReal.ofReal_mul (by norm_num)
    have h_coe : (ENNReal.ofReal (81 : ℝ)) = (81 : ENNReal) := by simp
    rw [h_mul, h_coe] <;> rfl
  rw [h3'] at h3
  have h_card_real : (coarseP₀.card : ENNReal) = ENNReal.ofReal (↑(coarseP₀.card : ℝ)) := by simp
  rw [h_card_real] at h3
  have h4 : (↑(coarseP₀.card : ℝ)) ≤ 81 * Real.rpow Δ (-(t + 2 * εA)) :=
    (ENNReal.ofReal_le_ofReal_iff h_rhs_nonneg).mp h3
  have h_pos1 : (0 : ℝ) ≤ 1 / 81 := by norm_num
  have h5 : 81 ≤ Real.rpow Δ (-(ε / 2 - 2 * εA)) := by
    have hδ₀_rpow : Real.rpow Δ (ε / 2 - 2 * εA) ≤ 1 / 81 := by
      have h2 : Real.rpow Δ (ε / 2 - 2 * εA) ≤
          Real.rpow (Real.rpow (1 / 81) (1 / (ε / 2 - 2 * εA))) (ε / 2 - 2 * εA) :=
        Real.rpow_le_rpow (by positivity) hΔ_small (by linarith)
      have h3 : Real.rpow (Real.rpow (1 / 81) (1 / (ε / 2 - 2 * εA))) (ε / 2 - 2 * εA) =
          Real.rpow (1 / 81) ((1 / (ε / 2 - 2 * εA)) * (ε / 2 - 2 * εA)) := by
        exact (Real.rpow_mul h_pos1 (1 / (ε / 2 - 2 * εA)) (ε / 2 - 2 * εA)).symm
      let x := ε / 2 - 2 * εA
      have h_ne : x ≠ 0 := h_a_pos.ne'
      have h4 : (1 / x) * x = 1 := by
        field_simp [h_ne] <;> ring
      rw [h3, h4] at h2
      have h5 : Real.rpow (1 / 81) 1 = 1 / 81 := by simp
      rw [h5] at h2
      exact h2
    have h6 : 0 < Real.rpow Δ (ε / 2 - 2 * εA) := Real.rpow_pos_of_pos hΔ_pos _
    have h7 : Real.rpow Δ (-(ε / 2 - 2 * εA)) = (Real.rpow Δ (ε / 2 - 2 * εA))⁻¹ :=
      Real.rpow_neg (by linarith) _
    rw [h7]
    have h9 : (Real.rpow Δ (ε / 2 - 2 * εA))⁻¹ ≥ (1 / 81 : ℝ)⁻¹ := by gcongr
    have h10 : (1 / 81 : ℝ)⁻¹ = 81 := by norm_num
    rw [h10] at h9
    exact h9
  have h_rpow_add : Real.rpow Δ (-(ε / 2 - 2 * εA)) * Real.rpow Δ (-(t + 2 * εA)) =
      Real.rpow Δ ((-(ε / 2 - 2 * εA)) + (-(t + 2 * εA))) :=
    (Real.rpow_add hΔ_pos _ _).symm
  have h11 : (-(ε / 2 - 2 * εA)) + (-(t + 2 * εA)) = -t - ε / 2 := by ring
  have h_pos2 : 0 ≤ Real.rpow Δ (-(t + 2 * εA)) := Real.rpow_nonneg hΔ_pos.le _
  have h12 : 81 * Real.rpow Δ (-(t + 2 * εA)) ≤
      Real.rpow Δ (-(ε / 2 - 2 * εA)) * Real.rpow Δ (-(t + 2 * εA)) :=
    mul_le_mul_of_nonneg_right h5 h_pos2
  rw [h_rpow_add, h11] at h12
  exact le_trans h4 h12

/-! ### Fine card upper bound -/

/-- A δ-separated finset has cardinality ≤ 81 × its δ-covering number.

    Uses packing number ≤ covering number at quarter scale, plus two doublings. -/
lemma separated_card_le_ncover {δ : ℝ} (hδ_pos : 0 < δ)
    {P : Finset EuclideanPlane}
    (h_sep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → δ ≤ dist p q) :
    (P.card : ℕ∞) ≤ 81 * Metric.externalCoveringNumber δ.toNNReal (P : Set EuclideanPlane) := by
  have h_half_pos : 0 < δ / 2 := by linarith
  have h_quarter_pos : 0 < δ / 4 := by linarith
  have hP_sep : Metric.IsSeparated ((δ / 2).toNNReal) (P : Set EuclideanPlane) := by
    intro p hp q hq hneq
    have h_dist_lt : δ / 2 < dist p q := by
      have h' : δ ≤ dist p q := h_sep p hp q hq hneq
      linarith
    have h_edist : edist p q = ENNReal.ofReal (dist p q) := by rw [edist_dist]
    rw [h_edist]
    have h_coe : (((δ / 2).toNNReal : ENNReal)) = ENNReal.ofReal (δ / 2) := by
      have h_pos : 0 ≤ δ / 2 := by linarith
      have h1 : ((δ / 2).toNNReal : ℝ) = δ / 2 := by exact Real.coe_toNNReal (δ / 2) h_pos
      have h2 : (((δ / 2).toNNReal : ENNReal)) = ENNReal.ofReal (((δ / 2).toNNReal : ℝ)) := by exact Eq.symm ENNReal.ofReal_coe_nnreal
      rw [h2, h1]
    rw [h_coe]
    have h_pos : 0 < dist p q := by linarith
    exact (ENNReal.ofReal_lt_ofReal_iff h_pos).mpr h_dist_lt
  have h1 : (P : Set EuclideanPlane).encard ≤
      Metric.packingNumber ((δ / 2).toNNReal) (P : Set EuclideanPlane) :=
    hP_sep.encard_le_packingNumber (by simp)
  have h1' : (P.card : ℕ∞) = (P : Set EuclideanPlane).encard := by simp
  have h1_final : (P.card : ℕ∞) ≤
      Metric.packingNumber ((δ / 2).toNNReal) (P : Set EuclideanPlane) := by
    rw [h1'] <;> exact h1
  have hq1 : (( (δ / 4).toNNReal : ℝ)) = δ / 4 :=
    Real.coe_toNNReal (δ / 4) h_quarter_pos.le
  have hq2 : (( (δ / 2).toNNReal : ℝ)) = δ / 2 :=
    Real.coe_toNNReal (δ / 2) h_half_pos.le
  have h_two_eq : 2 * (δ / 4).toNNReal = (δ / 2).toNNReal := by
    apply NNReal.coe_injective
    simp [hq1, hq2] <;> ring
  have h2_raw := Metric.packingNumber_two_mul_le_externalCoveringNumber
    ((δ / 4).toNNReal) (P : Set EuclideanPlane)
  have h2 : Metric.packingNumber ((δ / 2).toNNReal) (P : Set EuclideanPlane) ≤
      Metric.externalCoveringNumber ((δ / 4).toNNReal) (P : Set EuclideanPlane) := by
    rw [h_two_eq] at h2_raw
    exact h2_raw
  have h_quarter_eq : ((δ / 2).toNNReal) / 2 = (δ / 4).toNNReal := by
    apply NNReal.coe_injective
    simp [hq1, hq2, NNReal.coe_div] <;> ring
  have h3_raw := RobustKaufmanProjection.externalCoveringNumber_half_le_plane
    (P : Set EuclideanPlane) ((δ / 2).toNNReal)
  have h3 : Metric.externalCoveringNumber ((δ / 4).toNNReal) (P : Set EuclideanPlane) ≤
      9 * Metric.externalCoveringNumber ((δ / 2).toNNReal) (P : Set EuclideanPlane) := by
    rw [h_quarter_eq] at h3_raw
    exact h3_raw
  have hq0 : ((δ.toNNReal : ℝ)) = δ :=
    Real.coe_toNNReal δ hδ_pos.le
  have h_half_eq : δ.toNNReal / 2 = (δ / 2).toNNReal := by
    apply NNReal.coe_injective
    simp [hq0, hq2, NNReal.coe_div] <;> ring
  have h4_raw := RobustKaufmanProjection.externalCoveringNumber_half_le_plane
    (P : Set EuclideanPlane) δ.toNNReal
  have h4 : Metric.externalCoveringNumber ((δ / 2).toNNReal) (P : Set EuclideanPlane) ≤
      9 * Metric.externalCoveringNumber δ.toNNReal (P : Set EuclideanPlane) := by
    rw [h_half_eq] at h4_raw
    exact h4_raw
  calc (P.card : ℕ∞)
    ≤ Metric.packingNumber ((δ / 2).toNNReal) (P : Set EuclideanPlane) := h1_final
  _ ≤ Metric.externalCoveringNumber ((δ / 4).toNNReal) (P : Set EuclideanPlane) := h2
  _ ≤ 9 * Metric.externalCoveringNumber ((δ / 2).toNNReal) (P : Set EuclideanPlane) := h3
  _ ≤ 9 * (9 * Metric.externalCoveringNumber δ.toNNReal (P : Set EuclideanPlane)) := by gcongr
  _ = 81 * Metric.externalCoveringNumber δ.toNNReal (P : Set EuclideanPlane) := by ring

/-- Fine card upper bound: from source cardP hypothesis.

    Given `|P₀| ≤ δ^{-u}` with `δ = Δ²` and `0 < Δ < 1`, proves
    `|P₀| ≤ Δ^{-2u-ε/4}`. This is trivial because `δ^{-u} = Δ^{-2u}`
    and `Δ^{-2u} ≤ Δ^{-2u-ε/4}` for `0 < Δ < 1`, `ε > 0`. -/
lemma b1_fine_card_upper
    {Δ δ u ε : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_eq : δ = Δ^2) (hε_pos : 0 < ε) (hu_pos : 0 < u)
    {P₀ : Finset EuclideanPlane}
    (h_cardP : (P₀.card : ℝ) ≤ Real.rpow δ (-u)) :
    (P₀.card : ℝ) ≤ Real.rpow Δ (-2*u - ε/4) := by
  have h1 : Real.rpow δ (-u) = Real.rpow Δ (-2*u) := by
    rw [hδ_eq]
    have h_base : (Δ^2 : ℝ) = Real.rpow Δ 2 := by
      simp [Real.rpow_two] <;> ring
    have h_mul : Real.rpow (Real.rpow Δ 2) (-u) = Real.rpow Δ (2 * (-u)) :=
      (Real.rpow_mul hΔ_pos.le 2 (-u)).symm
    rw [h_base]
    rw [h_mul]
    have h_eq : 2 * (-u) = -2 * u := by ring
    rw [h_eq]
  have h2 : Real.rpow Δ (-2*u) ≤ Real.rpow Δ (-2*u - ε/4) := by
    have h3 : -2*u - ε/4 ≤ -2*u := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h3
  calc (P₀.card : ℝ)
    ≤ Real.rpow δ (-u) := h_cardP
  _ = Real.rpow Δ (-2*u) := h1
  _ ≤ Real.rpow Δ (-2*u - ε/4) := h2

/-! ### Coarse card lower bound -/

/-- Coarse card lower bound: from local S-set density.

    Each coarse parent square contains at most `81 * Cbar * Δ^u * |Pfin|` points
    (S-set bound + separated-card-to-covering conversion). Summing over all
    parents and cancelling `|Pfin|` gives:

    `|coarseP₀| ≥ 1 / (81 * Cbar * Δ^u)`.

    With `Cbar = δ^{-εA} = Δ^{-2εA}` and `Δ^{ε/4} ≤ 1/100`, the constant
    `1/81` is absorbed into the exponent, yielding `Δ^{-u+ε}`. -/
lemma b1_coarse_card_lower
    {m : ℕ} {Δ δ u ε εA : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_pos : 0 < δ) (hδ_eq2 : δ = Δ^2)
    (hu_pos : 0 < u) (hε_pos : 0 < ε) (hεA_pos : 0 < εA)
    (hεA_lt : 2 * εA < ε / 2)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    {Pfin : Finset EuclideanPlane}
    {coarseP₀ : Finset (DyadicSquare m)}
    {squareOf : EuclideanPlane → DyadicSquare m}
    (h_sep : ∀ p ∈ Pfin, ∀ q ∈ Pfin, p ≠ q → δ ≤ dist p q)
    (h_sset : _root_.IsDeltaSSet δ u (Real.rpow δ (-εA)) (Pfin : Set EuclideanPlane))
    (h_cover : ∀ p ∈ Pfin, squareOf p ∈ coarseP₀)
    (h_ball : ∀ Q ∈ coarseP₀, ∃ c : EuclideanPlane,
        (Pfin.filter (fun p => squareOf p = Q) : Set EuclideanPlane) ⊆ Metric.closedBall c Δ)
    :
    Real.rpow Δ (-u + ε) ≤ (coarseP₀.card : ℝ) := by
  set Cbar := Real.rpow δ (-εA) with hCbar_def
  have hCbar_pos : 0 < Cbar := Real.rpow_pos_of_pos hδ_pos _
  have hδ_le_Δ : δ ≤ Δ := by
    rw [hδ_eq2] <;> nlinarith
  have hΔu_pos : 0 < Real.rpow Δ u := Real.rpow_pos_of_pos hΔ_pos u

  let ncover : Set EuclideanPlane → ENNReal := fun S =>
    (Metric.externalCoveringNumber δ.toNNReal S : ENNReal)

  -- Ncover(δ, Pfin) ≤ ↑|Pfin| (trivial cover by the points themselves)
  have h_ncover_le_card : ncover (Pfin : Set EuclideanPlane) ≤ (Pfin.card : ENNReal) := by
    have hcover : Metric.IsCover δ.toNNReal (Pfin : Set EuclideanPlane) (Pfin : Set EuclideanPlane) := by
      intro x hx
      exact ⟨x, hx, by simp [Metric.mem_closedBall]⟩
    have h : Metric.externalCoveringNumber δ.toNNReal (Pfin : Set EuclideanPlane) ≤ (Pfin : Set EuclideanPlane).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hcover
    have h' : (Pfin : Set EuclideanPlane).encard = (Pfin.card : ℕ∞) := by simp
    rw [h'] at h
    have h_cast : (Metric.externalCoveringNumber δ.toNNReal (Pfin : Set EuclideanPlane) : ENNReal) ≤ (Pfin.card : ENNReal) := by
      exact_mod_cast h
    simpa [ncover] using h_cast

  -- Per-square cardinality bound
  have h_per_square : ∀ Q ∈ coarseP₀,
      ((Pfin.filter (fun p => squareOf p = Q)).card : ℝ) ≤
        81 * Cbar * Real.rpow Δ u * (Pfin.card : ℝ) := by
    intro Q hQ
    rcases h_ball Q hQ with ⟨c, hc⟩
    let P_Q := Pfin.filter (fun p => squareOf p = Q)
    have hP_Q_sub : (P_Q : Set EuclideanPlane) ⊆ (Pfin : Set EuclideanPlane) ∩ Metric.closedBall c Δ := by
      intro x hx
      have hx1 : x ∈ Pfin := (Finset.mem_filter.mp hx).1
      have hx2 : x ∈ Metric.closedBall c Δ := hc hx
      exact ⟨hx1, hx2⟩
    have h_sep_Q : ∀ p ∈ P_Q, ∀ q ∈ P_Q, p ≠ q → δ ≤ dist p q := by
      intro p hp q hq hneq
      have hp' : p ∈ Pfin := (Finset.mem_filter.mp hp).1
      have hq' : q ∈ Pfin := (Finset.mem_filter.mp hq).1
      exact h_sep p hp' q hq' hneq
    -- Card ≤ 81 * Ncover
    have h_card_le : (P_Q.card : ENNReal) ≤ (81 : ENNReal) * ncover (P_Q : Set EuclideanPlane) := by
      have h := separated_card_le_ncover hδ_pos h_sep_Q
      have h_cast : (P_Q.card : ENNReal) ≤ (81 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (P_Q : Set EuclideanPlane) : ENNReal) := by
        exact_mod_cast h
      simpa [ncover] using h_cast
    -- Ncover(P_Q) ≤ Ncover(Pfin ∩ B(c,Δ))
    have h1 : ncover (P_Q : Set EuclideanPlane) ≤ ncover ((Pfin : Set EuclideanPlane) ∩ Metric.closedBall c Δ) := by
      have h_mono : Metric.externalCoveringNumber δ.toNNReal (P_Q : Set EuclideanPlane) ≤
          Metric.externalCoveringNumber δ.toNNReal ((Pfin : Set EuclideanPlane) ∩ Metric.closedBall c Δ) :=
        Metric.externalCoveringNumber_mono_set hP_Q_sub
      have h_cast : (Metric.externalCoveringNumber δ.toNNReal (P_Q : Set EuclideanPlane) : ENNReal) ≤
          (Metric.externalCoveringNumber δ.toNNReal ((Pfin : Set EuclideanPlane) ∩ Metric.closedBall c Δ) : ENNReal) := by
        exact_mod_cast h_mono
      simpa [ncover] using h_cast
    -- S-set bound
    have h2 : ncover ((Pfin : Set EuclideanPlane) ∩ Metric.closedBall c Δ) ≤
        ENNReal.ofReal Cbar * (ENNReal.ofReal Δ) ^ u * ncover (Pfin : Set EuclideanPlane) :=
      h_sset.2.2.2.2 c Δ hδ_le_Δ
    -- Combine
    have h3 : (P_Q.card : ENNReal) ≤
        (81 : ENNReal) * ENNReal.ofReal Cbar * (ENNReal.ofReal Δ) ^ u * (Pfin.card : ENNReal) := by
      calc (P_Q.card : ENNReal)
        ≤ (81 : ENNReal) * ncover (P_Q : Set EuclideanPlane) := h_card_le
      _ ≤ (81 : ENNReal) * ncover ((Pfin : Set EuclideanPlane) ∩ Metric.closedBall c Δ) := by gcongr
      _ ≤ (81 : ENNReal) * (ENNReal.ofReal Cbar * (ENNReal.ofReal Δ) ^ u * ncover (Pfin : Set EuclideanPlane)) := by gcongr
      _ = (81 : ENNReal) * ENNReal.ofReal Cbar * (ENNReal.ofReal Δ) ^ u * ncover (Pfin : Set EuclideanPlane) := by ring
      _ ≤ (81 : ENNReal) * ENNReal.ofReal Cbar * (ENNReal.ofReal Δ) ^ u * (Pfin.card : ENNReal) := by gcongr
    have h_rpow_conv : (ENNReal.ofReal Δ) ^ u = ENNReal.ofReal (Real.rpow Δ u) :=
      ENNReal.ofReal_rpow_of_nonneg hΔ_pos.le hu_pos.le
    rw [h_rpow_conv] at h3
    have h_mul_conv : (81 : ENNReal) * ENNReal.ofReal Cbar * ENNReal.ofReal (Real.rpow Δ u) * (Pfin.card : ENNReal) =
        ENNReal.ofReal (81 * Cbar * Real.rpow Δ u * (Pfin.card : ℝ)) := by
      have hpc : 0 ≤ Cbar := by positivity
      have hpr : 0 ≤ Real.rpow Δ u := by positivity
      have hpn : 0 ≤ (Pfin.card : ℝ) := by positivity
      have h1 : (81 : ENNReal) = ENNReal.ofReal (81 : ℝ) := by simp
      rw [h1]
      have h2 : (Pfin.card : ENNReal) = ENNReal.ofReal (Pfin.card : ℝ) := by simp
      rw [h2]
      have h_combine : ENNReal.ofReal (81 : ℝ) * ENNReal.ofReal Cbar * ENNReal.ofReal (Real.rpow Δ u) * ENNReal.ofReal (Pfin.card : ℝ) =
          ENNReal.ofReal ((81 : ℝ) * Cbar * Real.rpow Δ u * (Pfin.card : ℝ)) := by
        have h_a : ENNReal.ofReal (81 : ℝ) * ENNReal.ofReal Cbar = ENNReal.ofReal ((81 : ℝ) * Cbar) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
        rw [h_a]
        have h_b : ENNReal.ofReal ((81 : ℝ) * Cbar) * ENNReal.ofReal (Real.rpow Δ u) = ENNReal.ofReal (((81 : ℝ) * Cbar) * Real.rpow Δ u) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
        rw [h_b]
        have h_c : ENNReal.ofReal (((81 : ℝ) * Cbar) * Real.rpow Δ u) * ENNReal.ofReal (Pfin.card : ℝ) = ENNReal.ofReal ((((81 : ℝ) * Cbar) * Real.rpow Δ u) * (Pfin.card : ℝ)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
        rw [h_c] <;> ring
      exact h_combine
    rw [h_mul_conv] at h3
    have h_rhs_nonneg : 0 ≤ 81 * Cbar * Real.rpow Δ u * (Pfin.card : ℝ) := by positivity
    have h_final : (P_Q.card : ℝ) ≤ 81 * Cbar * Real.rpow Δ u * (Pfin.card : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff h_rhs_nonneg).mp (by simpa using h3)
    exact h_final

  -- Pfin is the disjoint union of its fibers over coarseP₀
  have h_disj : ∀ Q1 ∈ coarseP₀, ∀ Q2 ∈ coarseP₀, Q1 ≠ Q2 →
      Disjoint (Pfin.filter (fun p => squareOf p = Q1)) (Pfin.filter (fun p => squareOf p = Q2)) := by
    intro Q1 _ Q2 _ hne
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 : squareOf p = Q1 := (Finset.mem_filter.mp hp1).2
    have h2 : squareOf p = Q2 := (Finset.mem_filter.mp hp2).2
    have h3 : Q1 = Q2 := by rw [←h1, h2]
    exact hne h3
  have h_union : Pfin = coarseP₀.biUnion (fun Q => Pfin.filter (fun p => squareOf p = Q)) := by
    ext p
    simp only [Finset.mem_biUnion]
    constructor
    · intro hp
      let Q := squareOf p
      have hQ : Q ∈ coarseP₀ := h_cover p hp
      have h_in : p ∈ Pfin.filter (fun p' => squareOf p' = Q) := by
        apply Finset.mem_filter.mpr
        exact ⟨hp, by simp [Q]⟩
      exact ⟨Q, hQ, h_in⟩
    · rintro ⟨Q, _, hQ⟩
      exact (Finset.mem_filter.mp hQ).1
  have h_card_biUnion : (coarseP₀.biUnion (fun Q => Pfin.filter (fun p => squareOf p = Q))).card =
      ∑ Q ∈ coarseP₀, (Pfin.filter (fun p => squareOf p = Q)).card :=
    Finset.card_biUnion h_disj
  have h_partition : (Pfin.card : ℝ) = ∑ Q ∈ coarseP₀, ((Pfin.filter (fun p => squareOf p = Q)).card : ℝ) := by
    have h_card : Pfin.card = (coarseP₀.biUnion (fun Q => Pfin.filter (fun p => squareOf p = Q))).card := by
      exact congr_arg Finset.card h_union
    rw [h_card, h_card_biUnion]
    <;> norm_cast

  -- Sum the per-square bounds
  have h_sum : (Pfin.card : ℝ) ≤ (coarseP₀.card : ℝ) * (81 * Cbar * Real.rpow Δ u * (Pfin.card : ℝ)) := by
    have h_partition' : (Pfin.card : ℝ) = ∑ Q ∈ coarseP₀, ((Pfin.filter (fun p => squareOf p = Q)).card : ℝ) := h_partition
    have h : ∑ Q ∈ coarseP₀, ((Pfin.filter (fun p => squareOf p = Q)).card : ℝ) ≤
        ∑ Q ∈ coarseP₀, (81 * Cbar * Real.rpow Δ u * (Pfin.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro Q hQ
      exact h_per_square Q hQ
    have h2 : ∑ Q ∈ coarseP₀, (81 * Cbar * Real.rpow Δ u * (Pfin.card : ℝ)) =
        (coarseP₀.card : ℝ) * (81 * Cbar * Real.rpow Δ u * (Pfin.card : ℝ)) := by
      rw [Finset.sum_const] <;> ring
    calc (Pfin.card : ℝ)
      = ∑ Q ∈ coarseP₀, ((Pfin.filter (fun p => squareOf p = Q)).card : ℝ) := h_partition'
    _ ≤ ∑ Q ∈ coarseP₀, (81 * Cbar * Real.rpow Δ u * (Pfin.card : ℝ)) := h
    _ = (coarseP₀.card : ℝ) * (81 * Cbar * Real.rpow Δ u * (Pfin.card : ℝ)) := h2

  -- Pfin is nonempty from S-set hypothesis
  have hPfin_nonempty : Pfin.Nonempty := h_sset.1
  have hPfin_pos : 0 < (Pfin.card : ℝ) := by exact_mod_cast hPfin_nonempty.card_pos

  -- Cancel |Pfin|
  have h_pos : 0 < 81 * Cbar * Real.rpow Δ u := by
    have h1 : 0 < Cbar := hCbar_pos
    positivity
  have h6 : (1 : ℝ) ≤ (coarseP₀.card : ℝ) * (81 * Cbar * Real.rpow Δ u) := by
    have h7 : (Pfin.card : ℝ) ≤ (coarseP₀.card : ℝ) * (81 * Cbar * Real.rpow Δ u * (Pfin.card : ℝ)) := h_sum
    have h8 : (Pfin.card : ℝ) > 0 := hPfin_pos
    nlinarith
  have h7 : (coarseP₀.card : ℝ) ≥ 1 / (81 * Cbar * Real.rpow Δ u) := by
    have h9 : 0 < 81 * Cbar * Real.rpow Δ u := h_pos
    have h10 : 1 / (81 * Cbar * Real.rpow Δ u) ≤ (coarseP₀.card : ℝ) := by
      have h11 : 1 ≤ (coarseP₀.card : ℝ) * (81 * Cbar * Real.rpow Δ u) := h6
      have h12 : 0 < 81 * Cbar * Real.rpow Δ u := h9
      calc 1 / (81 * Cbar * Real.rpow Δ u)
        ≤ ((coarseP₀.card : ℝ) * (81 * Cbar * Real.rpow Δ u)) / (81 * Cbar * Real.rpow Δ u) := by gcongr
      _ = (coarseP₀.card : ℝ) := by
        let b := 81 * Cbar * Real.rpow Δ u
        have hb : b ≠ 0 := h12.ne'
        have h13 : ((coarseP₀.card : ℝ) * b) / b = (coarseP₀.card : ℝ) := by
          rw [mul_div_assoc, div_self hb, mul_one]
        exact h13
    exact h10

  -- Substitute Cbar = δ^{-εA} = Δ^{-2εA}
  have hCbar_eq : Cbar = Real.rpow Δ (-2 * εA) := by
    have h1 : Cbar = Real.rpow δ (-εA) := by rfl
    rw [h1, hδ_eq2]
    have h2 : (Δ ^ 2 : ℝ) = Real.rpow Δ 2 := by
      simp [Real.rpow_two] <;> ring
    rw [h2]
    have h3 : Real.rpow (Real.rpow Δ 2) (-εA) = Real.rpow Δ (2 * (-εA)) :=
      (Real.rpow_mul hΔ_pos.le 2 (-εA)).symm
    rw [h3] <;> ring_nf
  rw [hCbar_eq] at h7

  -- Simplify the lower bound
  set X := Real.rpow Δ (-2 * εA) with hX_def
  set Y := Real.rpow Δ u with hY_def
  have hXY : X * Y = Real.rpow Δ (u - 2 * εA) := by
    have h : Real.rpow Δ (-2 * εA) * Real.rpow Δ u = Real.rpow Δ ((-2 * εA) + u) :=
      (Real.rpow_add hΔ_pos (-2 * εA) u).symm
    have h' : (-2 * εA) + u = u - 2 * εA := by ring
    rw [h'] at h
    simpa [hX_def, hY_def] using h
  set Z := Real.rpow Δ (u - 2 * εA) with hZ_def
  have hZ_pos : 0 < Z := Real.rpow_pos_of_pos hΔ_pos _
  have hZ_ne_zero : Z ≠ 0 := hZ_pos.ne'
  have h_inv : Z⁻¹ = Real.rpow Δ (-u + 2 * εA) := by
    have h1 : Z = Real.rpow Δ (u - 2 * εA) := by simp [hZ_def]
    have h2 : Z⁻¹ = (Real.rpow Δ (u - 2 * εA))⁻¹ := by rw [h1]
    rw [h2]
    have h3 : (Real.rpow Δ (u - 2 * εA))⁻¹ = Real.rpow Δ (-(u - 2 * εA)) := by
      have h4 : Real.rpow Δ (-(u - 2 * εA)) = (Real.rpow Δ (u - 2 * εA))⁻¹ :=
        Real.rpow_neg hΔ_pos.le (u - 2 * εA)
      exact h4.symm
    rw [h3]
    have h4 : -(u - 2 * εA) = -u + 2 * εA := by ring
    rw [h4]
  have h8 : 1 / (81 * X * Y) = (1 / 81 : ℝ) * Real.rpow Δ (-u + 2 * εA) := by
    have h_denom : 81 * X * Y = 81 * Z := by
      have h : X * Y = Z := by rw [hXY, hZ_def]
      rw [show 81 * X * Y = 81 * (X * Y) by ring]
      rw [h] <;> ring
    rw [h_denom]
    calc 1 / (81 * Z)
        = (1 / 81 : ℝ) * Z⁻¹ := by field_simp [hZ_ne_zero] <;> ring
      _ = (1 / 81 : ℝ) * Real.rpow Δ (-u + 2 * εA) := by rw [h_inv]
  rw [h8] at h7

  -- Absorb 1/81 into exponent: show (1/81) * Δ^{-u+2εA} ≥ Δ^{-u+ε}
  -- Equivalent to Δ^{ε-2εA} ≤ 1/81
  have h9 : Real.rpow Δ (ε - 2 * εA) ≤ 1 / 81 := by
    have h10 : ε / 2 < ε - 2 * εA := by linarith
    have h11 : Real.rpow Δ (ε - 2 * εA) ≤ Real.rpow Δ (ε / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le (by linarith)
    have h12 : Real.rpow Δ (ε / 2) = (Real.rpow Δ (ε / 4)) ^ 2 := by
      have h := Real.rpow_add hΔ_pos (ε / 4) (ε / 4)
      have h' : (ε / 4) + (ε / 4) = ε / 2 := by ring
      rw [h'] at h
      simpa [pow_two] using h
    rw [h12] at h11
    have h14 : 0 ≤ Real.rpow Δ (ε / 4) := Real.rpow_nonneg hΔ_pos.le _
    nlinarith [h_small]
  have h15 : (1 / 81 : ℝ) * Real.rpow Δ (-u + 2 * εA) ≥ Real.rpow Δ (-u + ε) := by
    have h16 : Real.rpow Δ (-u + 2 * εA) = Real.rpow Δ (-u + ε) * Real.rpow Δ (2 * εA - ε) := by
      have h17 : (-u + ε) + (2 * εA - ε) = -u + 2 * εA := by ring
      have h := Real.rpow_add hΔ_pos (-u + ε) (2 * εA - ε)
      rw [h17] at h
      exact h
    rw [h16]
    have h18 : Real.rpow Δ (2 * εA - ε) = (Real.rpow Δ (ε - 2 * εA))⁻¹ := by
      have h19 : (2 * εA - ε) = -(ε - 2 * εA) := by ring
      rw [h19]
      exact Real.rpow_neg hΔ_pos.le (ε - 2 * εA)
    rw [h18]
    have h20 : 0 < Real.rpow Δ (ε - 2 * εA) := Real.rpow_pos_of_pos hΔ_pos _
    have h21 : Real.rpow Δ (ε - 2 * εA) ≤ 1 / 81 := h9
    have h22 : (Real.rpow Δ (ε - 2 * εA))⁻¹ ≥ 81 := by
      have h23 : (Real.rpow Δ (ε - 2 * εA))⁻¹ ≥ (1 / 81 : ℝ)⁻¹ := by gcongr
      norm_num at h23 ⊢
      exact h23
    have h24 : 0 ≤ Real.rpow Δ (-u + ε) := Real.rpow_nonneg hΔ_pos.le _
    nlinarith
  exact le_trans h15 h7

/-! ### Per-square upper bound -/

/-- Per-square upper bound: each coarse parent contains at most `Δ^{-u-3ε/5}` fine points.

    Uses S-set bound on Pfin, separated-card-to-covering conversion, and the
    fine card upper bound. Constant 81 is absorbed via `Δ^{31ε/100} ≤ 1/81`. -/
lemma b1_per_square_upper
    {m : ℕ} {Δ δ u ε εA : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_pos : 0 < δ) (hδ_eq2 : δ = Δ^2)
    (hu_nonneg : 0 ≤ u) (hε_pos : 0 < ε) (hεA_pos : 0 < εA)
    (hεA_le : εA ≤ ε / 50)
    (h_small : Real.rpow Δ (31 * ε / 100) ≤ 1 / 81)
    {Pfin : Finset EuclideanPlane}
    {coarseP₀ : Finset (DiscretisedFurstenbergEstimate.DyadicSquare m)}
    {squareOf : EuclideanPlane → DiscretisedFurstenbergEstimate.DyadicSquare m}
    (h_sep : ∀ p ∈ Pfin, ∀ q ∈ Pfin, p ≠ q → δ ≤ dist p q)
    (h_sset : _root_.IsDeltaSSet δ u (Real.rpow δ (-εA)) (Pfin : Set EuclideanPlane))
    (h_ball : ∀ Q ∈ coarseP₀, ∃ c : EuclideanPlane,
        (Pfin.filter (fun p => squareOf p = Q) : Set EuclideanPlane) ⊆ Metric.closedBall c Δ)
    (h_fine_card_upper : (Pfin.card : ℝ) ≤ Real.rpow Δ (-2*u - ε/4)) :
    ∀ Q ∈ coarseP₀,
      ((Pfin.filter (fun p => squareOf p = Q)).card : ℝ) ≤ Real.rpow Δ (-u - 3 * ε / 5) := by
  intro Q hQ
  rcases h_ball Q hQ with ⟨c, hc⟩
  let P_Q := Pfin.filter (fun p => squareOf p = Q)
  have hP_Q_sub : (P_Q : Set EuclideanPlane) ⊆ (Pfin : Set EuclideanPlane) ∩ Metric.closedBall c Δ := by
    intro x hx
    have hx1 : x ∈ Pfin := (Finset.mem_filter.mp hx).1
    have hx2 : x ∈ Metric.closedBall c Δ := hc hx
    exact ⟨hx1, hx2⟩
  have h_sep_Q : ∀ p ∈ P_Q, ∀ q ∈ P_Q, p ≠ q → δ ≤ dist p q := by
    intro p hp q hq hneq
    have hp' : p ∈ Pfin := (Finset.mem_filter.mp hp).1
    have hq' : q ∈ Pfin := (Finset.mem_filter.mp hq).1
    exact h_sep p hp' q hq' hneq
  have hδ_le_Δ : δ ≤ Δ := by
    rw [hδ_eq2] <;> nlinarith
  set Cbar := Real.rpow δ (-εA) with hCbar_def
  have hCbar_pos : 0 < Cbar := Real.rpow_pos_of_pos hδ_pos _
  have h_card_le : (P_Q.card : ENNReal) ≤ (81 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal (P_Q : Set EuclideanPlane) := by
    have h := separated_card_le_ncover hδ_pos h_sep_Q
    exact_mod_cast h
  have h1 : Metric.externalCoveringNumber δ.toNNReal (P_Q : Set EuclideanPlane) ≤
      Metric.externalCoveringNumber δ.toNNReal ((Pfin : Set EuclideanPlane) ∩ Metric.closedBall c Δ) :=
    Metric.externalCoveringNumber_mono_set hP_Q_sub
  have h2 : Metric.externalCoveringNumber δ.toNNReal ((Pfin : Set EuclideanPlane) ∩ Metric.closedBall c Δ) ≤
      ENNReal.ofReal Cbar * (ENNReal.ofReal Δ) ^ u * Metric.externalCoveringNumber δ.toNNReal (Pfin : Set EuclideanPlane) :=
    h_sset.2.2.2.2 c Δ hδ_le_Δ
  have h3 : Metric.externalCoveringNumber δ.toNNReal (Pfin : Set EuclideanPlane) ≤ (Pfin.card : ENNReal) := by
    have hcover : Metric.IsCover δ.toNNReal (Pfin : Set EuclideanPlane) (Pfin : Set EuclideanPlane) := by
      intro x hx
      exact ⟨x, hx, by simp [Metric.mem_closedBall]⟩
    have h : Metric.externalCoveringNumber δ.toNNReal (Pfin : Set EuclideanPlane) ≤ (Pfin : Set EuclideanPlane).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hcover
    have h' : (Pfin : Set EuclideanPlane).encard = (Pfin.card : ℕ∞) := by simp
    rw [h'] at h
    exact_mod_cast h
  have h4 : (P_Q.card : ENNReal) ≤
      (81 : ENNReal) * ENNReal.ofReal Cbar * (ENNReal.ofReal Δ) ^ u * (Pfin.card : ENNReal) := by
    calc (P_Q.card : ENNReal)
      ≤ (81 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal (P_Q : Set EuclideanPlane) := h_card_le
    _ ≤ (81 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal ((Pfin : Set EuclideanPlane) ∩ Metric.closedBall c Δ) := by gcongr
    _ ≤ (81 : ENNReal) * (ENNReal.ofReal Cbar * (ENNReal.ofReal Δ) ^ u * Metric.externalCoveringNumber δ.toNNReal (Pfin : Set EuclideanPlane)) := by gcongr
    _ = (81 : ENNReal) * ENNReal.ofReal Cbar * (ENNReal.ofReal Δ) ^ u * Metric.externalCoveringNumber δ.toNNReal (Pfin : Set EuclideanPlane) := by ring
    _ ≤ (81 : ENNReal) * ENNReal.ofReal Cbar * (ENNReal.ofReal Δ) ^ u * (Pfin.card : ENNReal) := by gcongr
  have h_rpow_conv : (ENNReal.ofReal Δ) ^ u = ENNReal.ofReal (Real.rpow Δ u) :=
    ENNReal.ofReal_rpow_of_nonneg hΔ_pos.le hu_nonneg
  rw [h_rpow_conv] at h4
  have hCbar_eq : Cbar = Real.rpow Δ (-2 * εA) := by
    rw [hCbar_def, hδ_eq2]
    have h1 : (Δ ^ 2 : ℝ) = Real.rpow Δ 2 := by simp [Real.rpow_two] <;> ring
    rw [h1]
    have h2 : Real.rpow (Real.rpow Δ 2) (-εA) = Real.rpow Δ (2 * (-εA)) :=
      (Real.rpow_mul hΔ_pos.le 2 (-εA)).symm
    rw [h2] <;> ring_nf
  rw [hCbar_eq] at h4
  have h_pos1 : 0 ≤ Real.rpow Δ (-2 * εA) := Real.rpow_nonneg hΔ_pos.le _
  have h_pos2 : 0 ≤ Real.rpow Δ u := Real.rpow_nonneg hΔ_pos.le _
  have h_pos3 : 0 ≤ (Pfin.card : ℝ) := by positivity
  have h_mul_conv : (81 : ENNReal) * ENNReal.ofReal (Real.rpow Δ (-2 * εA)) * ENNReal.ofReal (Real.rpow Δ u) * (Pfin.card : ENNReal) =
      ENNReal.ofReal ((81 : ℝ) * Real.rpow Δ (-2 * εA) * Real.rpow Δ u * (Pfin.card : ℝ)) := by
    have h1 : (81 : ENNReal) = ENNReal.ofReal (81 : ℝ) := by simp
    have h2 : (Pfin.card : ENNReal) = ENNReal.ofReal (Pfin.card : ℝ) := by simp
    rw [h1, h2]
    have h3 : ENNReal.ofReal (81 : ℝ) * ENNReal.ofReal (Real.rpow Δ (-2 * εA)) = ENNReal.ofReal ((81 : ℝ) * Real.rpow Δ (-2 * εA)) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
    rw [h3]
    have h4 : ENNReal.ofReal ((81 : ℝ) * Real.rpow Δ (-2 * εA)) * ENNReal.ofReal (Real.rpow Δ u) = ENNReal.ofReal (((81 : ℝ) * Real.rpow Δ (-2 * εA)) * Real.rpow Δ u) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [h4]
    have h5 : ENNReal.ofReal (((81 : ℝ) * Real.rpow Δ (-2 * εA)) * Real.rpow Δ u) * ENNReal.ofReal (Pfin.card : ℝ) = ENNReal.ofReal ((((81 : ℝ) * Real.rpow Δ (-2 * εA)) * Real.rpow Δ u) * (Pfin.card : ℝ)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [h5] <;> ring
  rw [h_mul_conv] at h4
  have h_rhs_nonneg : 0 ≤ (81 : ℝ) * Real.rpow Δ (-2 * εA) * Real.rpow Δ u * (Pfin.card : ℝ) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h_pos1) h_pos2) h_pos3
  have h5 : (P_Q.card : ℝ) ≤ (81 : ℝ) * Real.rpow Δ (-2 * εA) * Real.rpow Δ u * (Pfin.card : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff h_rhs_nonneg).mp (by simpa using h4)
  have h_pos4 : 0 ≤ Real.rpow Δ (-2 * u - ε / 4) := Real.rpow_nonneg hΔ_pos.le _
  have h6 : (81 : ℝ) * Real.rpow Δ (-2 * εA) * Real.rpow Δ u * (Pfin.card : ℝ) ≤
      (81 : ℝ) * Real.rpow Δ (-2 * εA) * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4) := by
    gcongr <;> exact h_pos4
  have h71 : Real.rpow Δ (-2 * εA) * Real.rpow Δ u = Real.rpow Δ (-2 * εA + u) :=
    (Real.rpow_add hΔ_pos (-2 * εA) u).symm
  have h72 : Real.rpow Δ (-2 * εA + u) * Real.rpow Δ (-2 * u - ε / 4) =
      Real.rpow Δ ((-2 * εA + u) + (-2 * u - ε / 4)) :=
    (Real.rpow_add hΔ_pos (-2 * εA + u) (-2 * u - ε / 4)).symm
  have h7 : Real.rpow Δ (-2 * εA) * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4) =
      Real.rpow Δ (-u - 2 * εA - ε / 4) := by
    rw [h71, h72] <;> ring_nf
  have h6' : (81 : ℝ) * Real.rpow Δ (-2 * εA) * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4) =
      (81 : ℝ) * Real.rpow Δ (-u - 2 * εA - ε / 4) := by
    have h_assoc : (81 : ℝ) * Real.rpow Δ (-2 * εA) * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4) =
        (81 : ℝ) * (Real.rpow Δ (-2 * εA) * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4)) := by ring
    rw [h_assoc, h7]
  have h8 : -u - 2 * εA - ε / 4 ≥ -u - 29 * ε / 100 := by linarith [hεA_le]
  have h9 : Real.rpow Δ (-u - 2 * εA - ε / 4) ≤ Real.rpow Δ (-u - 29 * ε / 100) :=
    Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h8
  have h10 : (81 : ℝ) * Real.rpow Δ (-u - 2 * εA - ε / 4) ≤
      (81 : ℝ) * Real.rpow Δ (-u - 29 * ε / 100) := by gcongr
  have h11 : (81 : ℝ) ≤ Real.rpow Δ (-(31 * ε / 100)) := by
    have h12 : Real.rpow Δ (31 * ε / 100) ≤ 1 / 81 := h_small
    have h13 : Real.rpow Δ (-(31 * ε / 100)) = (Real.rpow Δ (31 * ε / 100))⁻¹ :=
      Real.rpow_neg hΔ_pos.le (31 * ε / 100)
    rw [h13]
    have h14 : 0 < Real.rpow Δ (31 * ε / 100) := Real.rpow_pos_of_pos hΔ_pos _
    have h15 : (Real.rpow Δ (31 * ε / 100))⁻¹ ≥ (1 / 81 : ℝ)⁻¹ := by gcongr
    norm_num at h15 ⊢; exact h15
  have h_pos5 : 0 ≤ Real.rpow Δ (-u - 29 * ε / 100) := Real.rpow_nonneg hΔ_pos.le _
  have h16 : (81 : ℝ) * Real.rpow Δ (-u - 29 * ε / 100) ≤
      Real.rpow Δ (-(31 * ε / 100)) * Real.rpow Δ (-u - 29 * ε / 100) :=
    mul_le_mul_of_nonneg_right h11 h_pos5
  have h17 : Real.rpow Δ (-(31 * ε / 100)) * Real.rpow Δ (-u - 29 * ε / 100) =
      Real.rpow Δ (-u - 3 * ε / 5) := by
    have h18 : Real.rpow Δ (-(31 * ε / 100)) * Real.rpow Δ (-u - 29 * ε / 100) =
        Real.rpow Δ ((-(31 * ε / 100)) + (-u - 29 * ε / 100)) :=
      (Real.rpow_add hΔ_pos (-(31 * ε / 100)) (-u - 29 * ε / 100)).symm
    rw [h18]
    have h19 : (-(31 * ε / 100)) + (-u - 29 * ε / 100) = -u - 3 * ε / 5 := by ring
    rw [h19]
  calc (P_Q.card : ℝ)
    ≤ (81 : ℝ) * Real.rpow Δ (-2 * εA) * Real.rpow Δ u * (Pfin.card : ℝ) := h5
  _ ≤ (81 : ℝ) * Real.rpow Δ (-2 * εA) * Real.rpow Δ u * Real.rpow Δ (-2 * u - ε / 4) := h6
  _ = (81 : ℝ) * Real.rpow Δ (-u - 2 * εA - ε / 4) := h6'
  _ ≤ (81 : ℝ) * Real.rpow Δ (-u - 29 * ε / 100) := h10
  _ ≤ Real.rpow Δ (-(31 * ε / 100)) * Real.rpow Δ (-u - 29 * ε / 100) := h16
  _ = Real.rpow Δ (-u - 3 * ε / 5) := h17

end DirecretisedFurstenbergEstimate.FrontEndLemmas
