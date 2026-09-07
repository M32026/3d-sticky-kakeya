module

/-
  MainProof_B1.lean

  B1 pivot bootstrapping proof using G-intersection bad tubes.
  Extends MainProof_G with bootstrapping_one_direction.
-/

public import MyLeanRepo.RadialBootstrapping.MainProof_G
public import MyLeanRepo.RadialBootstrapping.MeasureHelpers
public import MyLeanRepo.RadialBootstrapping.NegationHelpers
public import MyLeanRepo.RadialBootstrapping.Constants
public import MyLeanRepo.RadialBootstrapping.TubeFamilies
public import MyLeanRepo.RadialBootstrapping.FurstenbergCaller
public import MyLeanRepo.RadialBootstrapping.NonConcentratedCase
public import MyLeanRepo.RadialBootstrapping.GeneralizedOverlap
public import MyLeanRepo.RadialBootstrapping.ExtractNonConcDeltaSet
public import MyLeanRepo.RadialBootstrapping.MultiTubeStepBFromSnon
public import MyLeanRepo.RadialBootstrapping.GridMap
public import MyLeanRepo.RadialBootstrapping.CBBound
public import MyLeanRepo.RadialBootstrapping.ConcentratedBridge
public import MyLeanRepo.RadialBootstrapping.TubeLine
public import MyLeanRepo.RadialBootstrapping.DirectionGridExtraction
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset
open scoped ENNReal NNReal Classical

set_option maxHeartbeats 1000000

noncomputable section

namespace RadialBootstrapping
namespace B1

/-- X: points x where fiber H_r|_x has mass ≥ r^τ. -/
def XSet (H_r : Set (Point × Point)) (ν₂ : Measure Point)
    (r τ : ℝ) : Set Point :=
  {x | ν₂ {b₂ | (x, b₂) ∈ H_r} ≥ ENNReal.ofReal (Real.rpow r τ)}

/-! ==========================================================================
   Helper lemmas
   ========================================================================== -/

/-- Swap coordinates of a set in Point × Point. -/
def swapSet (S : Set (Point × Point)) : Set (Point × Point) :=
  {p | (p.2, p.1) ∈ S}

/-- If μ(A) ≥ 1 - c and μ(B) ≥ 1 - c for a probability measure μ,
    then μ(A ∩ B) ≥ 1 - 2c. -/
lemma intersection_measure_lower_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {A B : Set α} (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B)
    {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2)
    (hA : μ A ≥ ENNReal.ofReal (1 - c))
    (hB : μ B ≥ ENNReal.ofReal (1 - c)) :
    μ (A ∩ B) ≥ ENNReal.ofReal (1 - 2 * c) := by
  have h_eq : μ (A ∪ B) + μ (A ∩ B) = μ A + μ B :=
    measure_union_add_inter' hA_meas B
  have h_union_le : μ (A ∪ B) ≤ 1 := by
    have h : μ (A ∪ B) ≤ μ Set.univ := measure_mono (subset_univ _)
    have h_univ : μ Set.univ = 1 := measure_univ
    rw [h_univ] at h
    exact h
  have h1 : μ A + μ B ≤ 1 + μ (A ∩ B) := by
    calc μ A + μ B = μ (A ∪ B) + μ (A ∩ B) := h_eq.symm
      _ ≤ 1 + μ (A ∩ B) := by gcongr
  have h2 : ENNReal.ofReal (1 - c) + ENNReal.ofReal (1 - c) ≤ μ A + μ B := by gcongr
  have h3 : ENNReal.ofReal (1 - c) + ENNReal.ofReal (1 - c) = ENNReal.ofReal (2 - 2 * c) := by
    have hpos1 : 0 ≤ 1 - c := by linarith
    have hpos2 : 0 ≤ 1 - c := by linarith
    rw [← ENNReal.ofReal_add hpos1 hpos2] <;> ring_nf
  rw [h3] at h2
  have h4 : ENNReal.ofReal (2 - 2 * c) ≤ 1 + μ (A ∩ B) := le_trans h2 h1
  have h5 : 0 ≤ 1 - 2 * c := by linarith
  have h6 : ENNReal.ofReal (2 - 2 * c) = 1 + ENNReal.ofReal (1 - 2 * c) := by
    have h7 : ENNReal.ofReal (2 - 2 * c) = ENNReal.ofReal (1 + (1 - 2 * c)) := by ring_nf
    rw [h7]
    rw [ENNReal.ofReal_add (by norm_num) h5] <;> simp
  rw [h6] at h4
  have h8 : (1 : ENNReal) ≠ ⊤ := by simp
  have h9 : ENNReal.ofReal (1 - 2 * c) ≤ μ (A ∩ B) :=
    (ENNReal.add_le_add_iff_left h8).mp h4
  exact h9

/-- Swapping coordinates preserves product measure. -/
lemma swapSet_measure
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν₁ : ProbabilityMeasure α) (ν₂ : ProbabilityMeasure β)
    {E : Set (β × α)} (hE_meas : MeasurableSet E) :
    (ν₁.prod ν₂) {p : α × β | (p.2, p.1) ∈ E} = (ν₂.prod ν₁) E := by
  classical
  let g : β × α → ENNReal := Set.indicator E (fun _ => (1 : ENNReal))
  have hg : Measurable g := measurable_const.indicator hE_meas
  let f : α × β → ENNReal := fun p => g (p.2, p.1)
  let S : Set (α × β) := {p | (p.2, p.1) ∈ E}
  have hS_meas : MeasurableSet S := hE_meas.preimage (by fun_prop)
  have h_main : ∫⁻ (z : β × α), f z.swap ∂(ν₂.prod ν₁) = ∫⁻ (z : α × β), f z ∂(ν₁.prod ν₂) :=
    MeasureTheory.lintegral_prod_swap f
  have h1 : ∫⁻ (z : β × α), f z.swap ∂(ν₂.prod ν₁) = ∫⁻ (z : β × α), g z ∂(ν₂.prod ν₁) := by
    congr with z <;> simp [f, g, Prod.swap] <;> rfl
  have h2 : ∫⁻ (z : β × α), g z ∂(ν₂.prod ν₁) = (ν₂.prod ν₁ : Measure (β × α)) E := by
    have h21 : g = Set.indicator E (fun _ => (1 : ENNReal)) := by rfl
    rw [h21, lintegral_indicator hE_meas] <;> simp
  have h3 : ∫⁻ (z : α × β), f z ∂(ν₁.prod ν₂) = (ν₁.prod ν₂ : Measure (α × β)) S := by
    have h31 : f = Set.indicator S (fun _ => (1 : ENNReal)) := by
      funext z
      simp [f, g, S, Set.indicator] <;> aesop
    rw [h31, lintegral_indicator hS_meas] <;> simp
  have h4 : (ν₁.prod ν₂ : Measure (α × β)) S = (ν₂.prod ν₁ : Measure (β × α)) E := by
    calc (ν₁.prod ν₂ : Measure (α × β)) S
      = ∫⁻ (z : α × β), f z ∂(ν₁.prod ν₂) := h3.symm
    _ = ∫⁻ (z : β × α), f z.swap ∂(ν₂.prod ν₁) := h_main.symm
    _ = ∫⁻ (z : β × α), g z ∂(ν₂.prod ν₁) := h1
    _ = (ν₂.prod ν₁ : Measure (β × α)) E := h2
  have h_coe1 : ((ν₁.prod ν₂) S : ENNReal) = (ν₁.prod ν₂ : Measure (α × β)) S :=
    ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (ν₁.prod ν₂) S
  have h_coe2 : ((ν₂.prod ν₁) E : ENNReal) = (ν₂.prod ν₁ : Measure (β × α)) E :=
    ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (ν₂.prod ν₁) E
  have h6 : ((ν₁.prod ν₂) S : ENNReal) = ((ν₂.prod ν₁) E : ENNReal) := by
    rw [h_coe1, h_coe2]
    exact h4
  exact_mod_cast h6

/-- ν₁(X) ≥ r^τ from (ν₁×ν₂)(H_r) ≥ 2r^τ. -/
lemma fiber_lower_bound
    (ν₁ ν₂ : ProbabilityMeasure Point)
    (H_r : Set (Point × Point)) (hH_r_meas : MeasurableSet H_r)
    (r τ : ℝ) (hτ : 0 < τ) (hr : 0 < r)
    (hH_r_measure : (ν₁.prod ν₂) H_r ≥ ENNReal.ofReal (2 * Real.rpow r τ)) :
    ν₁ (XSet H_r ν₂ r τ) ≥ ENNReal.ofReal (Real.rpow r τ) := by
  let μ : Measure Point := ν₁
  let ν : Measure Point := ν₂
  let c : ℝ := 2 * Real.rpow r τ
  have hc_pos : 0 < c := by
    have h1 : 0 < Real.rpow r τ := Real.rpow_pos_of_pos hr τ
    have h2 : 0 < 2 * Real.rpow r τ := by positivity
    exact h2
  have h_main' : (μ.prod ν) H_r ≥ ENNReal.ofReal c := by
    have h_eq2 : ENNReal.ofReal c = ENNReal.ofReal (2 * Real.rpow r τ) := by
      congr <;> dsimp only [c] <;> ring
    rw [h_eq2]
    have h_coe : (μ.prod ν) H_r = (ν₁.prod ν₂) H_r := by
      simp [μ, ν, ProbabilityMeasure.prod] <;> rfl
    rw [h_coe]
    exact hH_r_measure
  have hc_le_one : c ≤ 1 := by
    have h1 : (μ.prod ν) H_r ≤ 1 := prob_le_one
    have h3 : ENNReal.ofReal c ≤ 1 := le_trans h_main' h1
    by_contra h4
    have h5 : (1 : ℝ) < c := by linarith
    have h6 : (1 : ENNReal) < ENNReal.ofReal c := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr h5
    have h7 : ¬(ENNReal.ofReal c ≤ 1) := not_le.mpr h6
    exact h7 h3
  rcases fubini_fiber_lowerBound hH_r_meas hc_pos hc_le_one h_main'
    with ⟨A, hA_meas, hA_measure, hA_fibers⟩
  have hA_sub : A ⊆ XSet H_r ν r τ := by
    intro x hx
    have h5 : ν (Prod.mk x ⁻¹' H_r) ≥ ENNReal.ofReal (c / 2) := hA_fibers x hx
    have h6 : c / 2 = Real.rpow r τ := by dsimp only [c] <;> ring
    have h7 : ν (Prod.mk x ⁻¹' H_r) ≥ ENNReal.ofReal (Real.rpow r τ) := by
      rw [h6] at h5; exact h5
    have h8 : {b₂ | (x, b₂) ∈ H_r} = Prod.mk x ⁻¹' H_r := by
      ext y; simp
    have h9 : ν {b₂ | (x, b₂) ∈ H_r} ≥ ENNReal.ofReal (Real.rpow r τ) := by
      rw [h8]; exact h7
    exact h9
  have h7 : μ A ≤ μ (XSet H_r ν r τ) := measure_mono hA_sub
  have h8 : ENNReal.ofReal (c / 2) ≤ μ (XSet H_r ν r τ) := by
    calc ENNReal.ofReal (c / 2)
      ≤ μ A := hA_measure
    _ ≤ μ (XSet H_r ν r τ) := h7
  have h9 : c / 2 = Real.rpow r τ := by dsimp only [c] <;> ring
  rw [h9] at h8
  have h_set_eq : XSet H_r ν r τ = XSet H_r ν₂ r τ := by
    rfl
  rw [h_set_eq] at h8
  have h_coe : (↑(ν₁ (XSet H_r ν₂ r τ)) : ENNReal) = μ (XSet H_r ν₂ r τ) :=
    ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₁ (XSet H_r ν₂ r τ)
  rw [h_coe]
  exact h8

lemma dyadic_le_r0_eq_nat (r r₀ : ℝ) (hr : r ∈ Dyadic) (hle : r ≤ r₀) (hlt : r₀ < 1) :
    ∃ (n : ℕ), r = (2 : ℝ) ^ (-(n : ℝ)) := by
  rcases hr with ⟨k : ℤ, hk⟩
  have h_r_eq : r = (2 : ℝ) ^ (k : ℝ) := by simpa using hk
  have hk_neg : k < 0 := by
    by_contra h
    have h' : 0 ≤ k := by linarith
    have h1 : r ≥ 1 := by
      rw [h_r_eq]
      have h2 : (k : ℝ) ≥ 0 := by exact_mod_cast h'
      have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
        apply Real.one_le_rpow <;> norm_num <;> linarith
      exact h3
    linarith [hle, hlt]
  let n : ℕ := (-k).toNat
  have hn : (n : ℤ) = -k := by
    simp [n, Int.toNat_of_nonneg (show 0 ≤ -k by linarith)] <;> omega
  have hr_eq2 : r = (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [h_r_eq]
    have h9 : k = -((n : ℤ)) := by omega
    rw [h9] <;> norm_cast
  exact ⟨n, hr_eq2⟩

/-! ==========================================================================
   Direction extraction + cardinality dichotomy
   ========================================================================== -/

/-- Given T_x, Y_x from well_behaved_tubes, extract direction-separated S
    and do cardinality dichotomy into concentrated/non-concentrated.

    Uses R_high for direction extraction (separation r/(4*R_high)).
    NOTE: R_low would require dist x y ≤ 2*R_low + r^κ = 1 + r^κ,
    but Y_x points can be at distance up to R_high = 2. -/
theorem concentrated_case_contradiction_G
    (ν₁ ν₂ : ProbabilityMeasure Point)
    (G : Set (Point × Point))
    (K K' C σ τ r c κ : ℝ)
    (hσ : 0 ≤ σ) (hσ_lt_one : σ < 1) (hτ : 0 < τ) (hr : 0 < r) (hr_small : r < 1)
    (hκ : κ = 14 * τ / (1 - σ)) (hκ_lt_one : κ < 1)
    (hC : 1 ≤ C) (hK : 1 ≤ K) (hc_pos : 0 < c)
    (hν₂_growth : ∀ (x : Point) (ρ : ℝ), 0 < ρ →
      ν₂ (Metric.ball x ρ) ≤ Real.toNNReal (C * ρ))
    (hν₁_growth : ∀ (x : Point) (ρ : ℝ), 0 < ρ →
      ν₁ (Metric.ball x ρ) ≤ Real.toNNReal (C * ρ))
    (hG_forward : ∀ x ∈ (ν₁ : Measure Point).support,
      ∀ ℓ : AffineSubspace ℝ Point, x ∈ (ℓ : Set Point) →
        Module.finrank ℝ ℓ.direction = 1 → ∀ r' : ℝ, 0 < r' →
          ν₂ {b₂ | b₂ ∈ tubeLine r' ℓ ∧ (x, b₂) ∈ G} ≤
            ENNReal.ofReal (K * Real.rpow r' σ))
    (hG_reverse : ∀ y ∈ (ν₂ : Measure Point).support,
      ∀ ℓ : AffineSubspace ℝ Point, y ∈ (ℓ : Set Point) →
        Module.finrank ℝ ℓ.direction = 1 → ∀ r' : ℝ, 0 < r' →
          ν₁ {b₁ | b₁ ∈ tubeLine r' ℓ ∧ (b₁, y) ∈ G} ≤
            ENNReal.ofReal (K * Real.rpow r' σ))
    (hG_meas : MeasurableSet G)
    (hG_subset : G ⊆ (ν₁ : Measure Point).support ×ˢ (ν₂ : Measure Point).support)
    (h_support_dist : 1 / 2 ≤ sInf {d : ℝ |
      ∃ x ∈ (ν₁ : Measure Point).support,
        ∃ y ∈ (ν₂ : Measure Point).support, dist x y = d})
    (h_supp1 : (ν₁ : Measure Point).support ⊆ Metric.closedBall (0 : Point) 1)
    (h_supp2 : (ν₂ : Measure Point).support ⊆ Metric.closedBall (0 : Point) 1)
    (R_low R_high : ℝ)
    (hR_low_pos : 0 < R_low) (hR_high_pos : 0 < R_high)
    (hR_le : R_low ≤ R_high)
    (hr_tube_small : r ≤ R_low / 4)
    (h_rκ_le_R : Real.rpow r κ ≤ R_high)
    (N : ℕ)
    (hN_pos : 0 < N)
    (hR : 2 * R_high + r ≤ r * (2 : ℝ)^N)
    (h_log_absorb : Real.rpow r (σ + 3 * τ) ≥ C * r + 792 * (N : ℝ) * Real.rpow r (σ + 4 * τ))
    (h_param_strengthened : Real.rpow r τ * ((Nat.floor (16 * Real.pi * R_high / R_low) + 1 : ℝ)) * K * (2 : ℝ)^σ ≤ 66)
    (h_card_strong : (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2) + 1 : ℝ) ≤
        (1 / 1584 : ℝ) * Real.rpow r (-τ))
    (h_count_small : Real.rpow r (-2 * τ) >
        (10^7 : ℝ) * K * C * Real.rpow ((R_high + r) / 4) σ)
    (hσ3τ_gt_κ : σ + 3 * τ > κ)
    (h_r_log_small : Real.rpow r τ * Real.log (1 / r) ≤ 1 / 100)
    (h_r_final : 20 * C * Real.rpow r τ < 1)
    (h_inner_cond : 18 * C * r ≤ Real.rpow r (σ + 3 * τ))
    (X_conc : Set Point)
    (hX_conc_subset : X_conc ⊆ (ν₁ : Measure Point).support)
    (hX_conc_meas : (ν₁ : Measure Point) X_conc ≥ ENNReal.ofReal (Real.rpow r τ / 2))
    (hX_conc_prop : ∀ x ∈ X_conc,
      ∃ (T_x S T_conc : Finset (AffineSubspace ℝ Point)) (Y_x : Set Point),
        MeasurableSet Y_x ∧
        (∀ ℓ ∈ T_x, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1) ∧
        Y_x ⊆ {b₂ | (x, b₂) ∈ G} ∧
        Y_x ⊆ ⋃ ℓ ∈ T_x, tubeLine r ℓ ∧
        (∀ y ∈ Y_x, R_low ≤ dist x y ∧ dist x y ≤ R_high) ∧
        ν₂ Y_x ≥ ENNReal.ofReal (Real.rpow r (2 * τ)) ∧
        (∀ ℓ ∈ T_x,
          ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) ≤ ν₂ (tubeLine r ℓ ∩ Y_x) ∧
          ν₂ (tubeLine r ℓ ∩ Y_x) ≤ ENNReal.ofReal (Real.rpow r (σ - τ))) ∧
        S ⊆ T_x ∧
        (∀ ℓ1 ∈ S, ∀ ℓ2 ∈ S, ℓ1 ≠ ℓ2 →
          submoduleDirDist ℓ1.direction ℓ2.direction ≥ r / (4 * R_high)) ∧
        T_conc ⊆ S ∧
        (∀ ℓ ∈ T_conc, IsConcentrated (ν₂ : Measure Point) Y_x (tubeLine r ℓ) r κ) ∧
        2 * T_conc.card ≥ S.card ∧
        (S.card : ℝ) ≥ Real.rpow r (2 * τ - σ) / (K * (2 : ℝ)^σ)) :
    False :=
  concentrated_case_contradiction_G_with_sep
    ν₁ ν₂ G K K' C σ τ r c κ
    hσ hσ_lt_one hτ hr hr_small hκ hκ_lt_one hC hK hc_pos
    hν₂_growth hν₁_growth hG_forward hG_reverse hG_meas hG_subset h_support_dist
    h_supp1 h_supp2 R_low R_high hR_low_pos hR_high_pos hR_le hr_tube_small h_rκ_le_R
    N hN_pos hR h_log_absorb h_param_strengthened h_card_strong h_count_small
    hσ3τ_gt_κ h_r_log_small h_r_final h_inner_cond
    X_conc hX_conc_subset hX_conc_meas hX_conc_prop

/-- Non-concentrated case leads to contradiction.

    Full signature matching non_concentrated_case_contradiction_G_proof.
    Includes Furstenberg parameters, P extraction, and per-x Step B data. -/
theorem non_concentrated_case_contradiction_G
    (ν₁ ν₂ : ProbabilityMeasure Point)
    (G : Set (Point × Point))
    (K K' C σ τ r c κ : ℝ)
    (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1) (hτ : 0 < τ) (hr : 0 < r) (hr_small : r < 1)
    (hr2_small : 2 * r < 1)
    (hκ : κ = 14 * τ / (1 - σ)) (hκ_lt_one : κ < 1)
    (hC : 1 ≤ C) (hc_pos : 0 < c)
    (hν₂_growth : ∀ (x : Point) (ρ : ℝ), 0 < ρ →
      ν₂ (Metric.ball x ρ) ≤ Real.toNNReal (C * ρ))
    (hν₁_growth : ∀ (x : Point) (ρ : ℝ), 0 < ρ →
      ν₁ (Metric.ball x ρ) ≤ Real.toNNReal (C * ρ))
    (hG_forward : ∀ x ∈ (ν₁ : Measure Point).support,
      ∀ ℓ : AffineSubspace ℝ Point, x ∈ (ℓ : Set Point) →
        Module.finrank ℝ ℓ.direction = 1 → ∀ r' : ℝ, 0 < r' →
          ν₂ {b₂ | b₂ ∈ tubeLine r' ℓ ∧ (x, b₂) ∈ G} ≤
            ENNReal.ofReal (K * Real.rpow r' σ))
    (X_nonconc : Set Point)
    (hX_nonconc_meas : (ν₁ : Measure Point) X_nonconc ≥
        ENNReal.ofReal (Real.rpow r τ / 2))
    -- Furstenberg parameters
    (ε_F δ₀ : ℝ) (hε_F_pos : 0 < ε_F) (hδ₀_pos : 0 < δ₀)
    (hF_estimate : ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ δ₀ →
      ∀ (X : Set Point) (T : Point → Set Line2),
        X.Nonempty → X ⊆ closedBall 0 1 →
        IsDeltaSet δ 1 (Real.rpow δ (-ε_F)) hδ (by norm_num) (Real.rpow_nonneg hδ.le _) X →
        (∀ x ∈ X, (T x).Nonempty ∧
          IsDeltaSet δ σ (Real.rpow δ (-ε_F)) hδ hσ_pos.le (Real.rpow_nonneg hδ.le _) (T x) ∧
          ∀ ℓ ∈ T x, x ∈ tube δ ℓ) →
        Set.Finite (⋃ x ∈ X, T x) →
        (⋃ x ∈ X, T x).ncard ≥ Nat.ceil (Real.rpow δ (-2 * σ - ε_F)))
    -- Parameter selection bounds
    (hεF_large : 8 * τ + 3 * κ < ε_F)
    (hδ_le : 2 * r ≤ δ₀)
    (hr_small3 : Real.rpow 2 (-(2 * σ + ε_F)) * Real.rpow r (-(ε_F - 8 * τ - 2 * κ)) >
        80000 * Real.rpow r (-κ))
    (hr_mass : Real.rpow r τ ≤ 1 / 6)
    (hr_width2 : 2 * r ≤ (Real.sqrt 3 / 2) * Real.rpow r κ)
    (hr_small4 : 4 * r / (Real.rpow r κ / 4) ≤ 1)
    -- P extraction
    (P : Set Point) (C_X : ℝ) (hC_X_nonneg : 0 ≤ C_X)
    (hP_sub : P ⊆ X_nonconc) (hP_nonempty : P.Nonempty) (hP_finite : P.Finite)
    (hP_ball : P ⊆ closedBall 0 1)
    (hP_delta : IsDeltaSet r 1 C_X hr (by norm_num) hC_X_nonneg P)
    (hC_X_bound : C_X * (Point_exists_doubling.choose : ℝ) ≤ Real.rpow (2 * r) (-ε_F))
    -- Localized Step B data
    (h_step_B_data : ∀ (x : Point), x ∈ P →
      ∃ (S_x : Finset Line2) (A_x : Line2 → Set Point) (C_B : ℝ) (hC_B : 0 ≤ C_B),
        S_x.Nonempty ∧
        (∀ L ∈ S_x, L ∈ (tubeFamily r : Set Line2) ∧ x ∈ tube (2 * r) L) ∧
        IsDeltaSet r σ C_B hr hσ_pos.le hC_B (S_x : Set Line2) ∧
        C_B * (Line2_exists_doubling.choose : ℝ) ≤ Real.rpow (2 * r) (-ε_F) ∧
        (∀ L ∈ S_x, MeasurableSet (A_x L) ∧ A_x L ⊆ tube (2 * r) L ∧
          (ν₂ : Measure Point) (A_x L) ≥ ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) ∧
          (∀ (z : Point), (ν₂ : Measure Point) (A_x L ∩ Metric.ball z (Real.rpow r κ)) ≤
            (ν₂ : Measure Point) (A_x L) / 3)))
    : False := by
  classical
  have hσ : 0 ≤ σ := le_of_lt hσ_pos
  have h1m_pos : 0 < 1 - σ := by linarith
  have hκ_pos : 0 < κ := by
    rw [hκ] <;> positivity
  /- Step 1: Furstenberg parameters provided by wrapper -/
  let εF : ℝ := ε_F
  let K_overlap : ℝ := 80000 * Real.rpow r (-κ)
  have hK_overlap_pos : 0 < K_overlap := by
    have h1 : 0 < Real.rpow r (-κ) := Real.rpow_pos_of_pos hr (-κ)
    positivity

  /- Step 3: P provided by hypothesis (localization + Frostman extraction) -/

  /- Step 4: Doubling constants -/
  let D_X : ℕ := Point_exists_doubling.choose
  have hD_X_pos : 0 < D_X := Point_exists_doubling.choose_spec.1
  have h_double_X : ∀ (x : Point) (ε : ℝ), 0 < ε →
      ∃ (S : Finset Point), Metric.closedBall x (2 * ε) ⊆ ⋃ y ∈ S, Metric.closedBall y ε ∧ S.card ≤ D_X :=
    Point_exists_doubling.choose_spec.2
  rcases Line2_exists_doubling with ⟨D_T, hD_T_pos, h_double_T⟩
  have hC_X_bound' : C_X * (D_X : ℝ) ≤ Real.rpow (2 * r) (-εF) := hC_X_bound

  /- Step 5: T_r = tubeFamily r with overlap bound -/
  let T_r : Finset Line2 := tubeFamily r
  have hT_r_overlap : ∀ (y1 y2 : Point),
      Real.rpow r κ / 4 ≤ dist y1 y2 →
        (T_r.filter (fun L => y1 ∈ tube (2 * r) L ∧ y2 ∈ tube (2 * r) L)).card ≤ K_overlap := by
    intro y1 y2 hsep
    let ξ : ℝ := Real.rpow r κ / 4
    have hξ_pos : 0 < ξ := by
      have h1 : 0 < Real.rpow r κ := Real.rpow_pos_of_pos hr κ
      positivity
    have hξ_le_one : ξ ≤ 1 := by
      have h1 : Real.rpow r κ < 1 := Real.rpow_lt_one (le_of_lt hr) hr_small hκ_pos
      have h2 : ξ = Real.rpow r κ / 4 := by rfl
      rw [h2]
      have h3 : Real.rpow r κ / 4 ≤ 1 := by
        have h4 : Real.rpow r κ ≤ 1 := h1.le
        linarith
      exact h3
    have h_small : 4 * r / ξ ≤ 1 := by
      simpa [ξ] using hr_small4
    have h_main : ((T_r.filter (fun L => y1 ∈ tube (2 * r) L ∧ y2 ∈ tube (2 * r) L)).card : ℝ) ≤
        20000 / ξ :=
      tubeFamily_overlap_bound_general r hr (le_of_lt hr_small) hξ_pos hξ_le_one h_small y1 y2 hsep
    have h_K_eq : (K_overlap : ℝ) = 20000 / ξ := by
      have h1 : K_overlap = 80000 * Real.rpow r (-κ) := by rfl
      have h2 : ξ = Real.rpow r κ / 4 := by rfl
      rw [h1, h2]
      have h3 : Real.rpow r (-κ) = (Real.rpow r κ)⁻¹ :=
        Real.rpow_neg (le_of_lt hr) κ
      rw [h3]
      <;> field_simp <;> ring
    rw [h_K_eq]
    exact_mod_cast h_main

  /- Step 6: Step B construction -/
  have h_step_B : ∃ (T'_x : Point → Set Line2) (A : Line2 → Set Point) (D_T : ℕ),
          (0 < D_T) ∧
          (∀ (L : Line2) (ε : ℝ), 0 < ε →
            ∃ (S : Finset Line2), Metric.closedBall L (2 * ε) ⊆ ⋃ M ∈ S, Metric.closedBall M ε ∧ S.card ≤ D_T) ∧
          (∀ x ∈ P, Set.Finite (T'_x x)) ∧
          (∀ x ∈ P, (T'_x x).Nonempty) ∧
          (∀ x ∈ P, ∃ (C_B : ℝ) (hC_B : 0 ≤ C_B),
            IsDeltaSet r σ C_B hr hσ hC_B (T'_x x) ∧
            C_B * (D_T : ℝ) ≤ Real.rpow (2 * r) (-εF)) ∧
          (∀ x ∈ P, ∀ L ∈ T'_x x, x ∈ tube (2 * r) L) ∧
          (∀ L ∈ (⋃ x ∈ P, T'_x x), L ∈ (T_r : Set Line2)) ∧
          (∀ L ∈ (⋃ x ∈ P, T'_x x), MeasurableSet (A L)) ∧
          (∀ L ∈ (⋃ x ∈ P, T'_x x), A L ⊆ tube (2 * r) L) ∧
          (∀ L ∈ (⋃ x ∈ P, T'_x x),
            (ν₂ : Measure Point) (A L) ≥ ENNReal.ofReal (Real.rpow r (σ + 3 * τ))) ∧
          (∀ L ∈ (⋃ x ∈ P, T'_x x), ∀ (x : Point),
            (ν₂ : Measure Point) (A L ∩ Metric.ball x (Real.rpow r κ)) ≤
              (ν₂ : Measure Point) (A L) / 3) := by
    classical
    choose S_x A_x C_B hC_B hSx_nonempty hSx_grid hSx_delta hSx_bound hSx_A
      using h_step_B_data
    let T'_x : Point → Set Line2 := fun x =>
      if hx : x ∈ P then (S_x x hx : Set Line2) else ∅
    let T' : Set Line2 := ⋃ x ∈ P, T'_x x
    have hT'_finite : Set.Finite T' := by
      apply Set.Finite.biUnion hP_finite
      intro x hx
      have h4 : T'_x x = (S_x x hx : Set Line2) := by simp [T'_x, hx]
      rw [h4]
      exact (S_x x hx).finite_toSet
    have h_pick : ∀ (L : Line2), L ∈ T' → ∃ (x : Point) (hx : x ∈ P), L ∈ (S_x x hx : Set Line2) := by
      intro L hL
      rcases Set.mem_iUnion₂.mp hL with ⟨x, hx, hL2⟩
      have h3 : L ∈ (S_x x hx : Set Line2) := by
        simpa [T'_x, hx] using hL2
      exact ⟨x, hx, h3⟩
    choose x_L hx_L_P hx_L_S using h_pick
    let A : Line2 → Set Point := fun L =>
      if hL : L ∈ T' then A_x (x_L L hL) (hx_L_P L hL) L else ∅
    let D_T : ℕ := Line2_exists_doubling.choose
    have hD_T_pos : 0 < D_T := Line2_exists_doubling.choose_spec.1
    have h_double_T : ∀ (L : Line2) (ε : ℝ), 0 < ε →
        ∃ (S : Finset Line2), Metric.closedBall L (2 * ε) ⊆ ⋃ M ∈ S, Metric.closedBall M ε ∧ S.card ≤ D_T :=
      Line2_exists_doubling.choose_spec.2
    refine ⟨T'_x, A, D_T, hD_T_pos, h_double_T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- T'_x finite
      intro x hx
      by_cases h : x ∈ P
      · have h4 : T'_x x = (S_x x h : Set Line2) := by simp [T'_x, h]
        rw [h4]
        exact_mod_cast (S_x x h).finite_toSet
      · have h5 : T'_x x = ∅ := by simp [T'_x, h]
        rw [h5]
        exact Set.finite_empty
    · -- T'_x nonempty
      intro x hx
      have h4 : T'_x x = (S_x x hx : Set Line2) := by simp [T'_x, hx]
      rw [h4]
      exact hSx_nonempty x hx
    · -- IsDeltaSet + bound
      intro x hx
      have h4 : T'_x x = (S_x x hx : Set Line2) := by simp [T'_x, hx]
      refine ⟨C_B x hx, hC_B x hx, ?_, ?_⟩
      · rw [h4]
        exact hSx_delta x hx
      · have h5 : (D_T : ℝ) = (Line2_exists_doubling.choose : ℝ) := by rfl
        rw [h5]
        exact hSx_bound x hx
    · -- x ∈ tube
      intro x hx L hL
      have h4 : L ∈ (S_x x hx : Set Line2) := by simpa [T'_x, hx] using hL
      exact (hSx_grid x hx L h4).2
    · -- L ∈ T_r
      intro L hL
      have h5 : L ∈ T' := hL
      have h6 : L ∈ (S_x (x_L L h5) (hx_L_P L h5) : Set Line2) := hx_L_S L h5
      exact (hSx_grid (x_L L h5) (hx_L_P L h5) L h6).1
    · -- A measurable
      intro L hL
      have h5 : L ∈ T' := hL
      have h6 : A L = A_x (x_L L h5) (hx_L_P L h5) L := by simp [A, h5]
      rw [h6]
      exact (hSx_A (x_L L h5) (hx_L_P L h5) L (hx_L_S L h5)).1
    · -- A subset
      intro L hL
      have h5 : L ∈ T' := hL
      have h6 : A L = A_x (x_L L h5) (hx_L_P L h5) L := by simp [A, h5]
      rw [h6]
      exact (hSx_A (x_L L h5) (hx_L_P L h5) L (hx_L_S L h5)).2.1
    · -- A mass
      intro L hL
      have h5 : L ∈ T' := hL
      have h6 : A L = A_x (x_L L h5) (hx_L_P L h5) L := by simp [A, h5]
      rw [h6]
      exact (hSx_A (x_L L h5) (hx_L_P L h5) L (hx_L_S L h5)).2.2.1
    · -- A non-concentration
      intro L hL z
      have h5 : L ∈ T' := hL
      have h6 : A L = A_x (x_L L h5) (hx_L_P L h5) L := by simp [A, h5]
      rw [h6]
      exact (hSx_A (x_L L h5) (hx_L_P L h5) L (hx_L_S L h5)).2.2.2 z

  /- Step 7: Call bridge -/
  let ν₁' : Measure Point := ν₁
  let ν₂' : Measure Point := ν₂
  haveI : IsProbabilityMeasure ν₁' := by exact ProbabilityMeasure.instIsProbabilityMeasureToMeasure ν₁
  haveI : IsProbabilityMeasure ν₂' := by exact ProbabilityMeasure.instIsProbabilityMeasureToMeasure ν₂
  exact non_concentrated_bridge_direct (ν₁ := ν₁') (ν₂ := ν₂')
    (hσ := hσ_pos) (hσ_lt_one := hσ_lt_one) (hτ := hτ) (hr := hr) (hr_small := hr_small)
    (hr2_small := hr2_small) (hκ := hκ) (hκ_lt_one := hκ_lt_one)
    (hεF_pos := hε_F_pos) (hεF_large := by
      have h : 8 * τ + 2 * κ < 8 * τ + 3 * κ := by linarith [hκ_pos]
      linarith [hεF_large])
    (hK_overlap_pos := hK_overlap_pos) (hr_small3 := hr_small3)
    (hr_mass := hr_mass) (hr_width2 := hr_width2)
    (P := P) (hP_finite := hP_finite) (hP_nonempty := hP_nonempty) (hP_ball := hP_ball)
    (C_X := C_X) (hC_X_nonneg := hC_X_nonneg) (hP_delta := hP_delta)
    (T_r := T_r) (hT_r_overlap := hT_r_overlap)
    (h_step_B := h_step_B)
    (ε_F := ε_F) (δ₀ := δ₀) (hε_F_pos := hε_F_pos) (hδ₀_pos := hδ₀_pos)
    (hF := hF_estimate) (hεF_le := by rfl) (hδ_le := hδ_le)
    (D_X := D_X) (hD_X_pos := hD_X_pos) (h_double_X := h_double_X)
    (hC_X_bound := hC_X_bound')

/-! ==========================================================================
   Single non-concentrated tube → Step B data
   ========================================================================== -/

/-- Given a single IsNonConcentrated tube with positive mass, produce Step B data
    by mapping it to a grid line. This avoids needing HalfMassNonConcentrated. -/
lemma bootstrapping_one_direction_G
    (β ε σ c K C : ℝ)
    (hβ : 0 < β) (hε : 0 < ε)
    (hσ : σ ∈ Set.Icc β (1 - ε))
    (hc : c ∈ Set.Ioo (0 : ℝ) (1 / 10))
    (hK : 1 ≤ K) (hC : 1 ≤ C)
    (ν₁ ν₂ : ProbabilityMeasure Point)
    (h_dist : 1 / 2 ≤ sInf {d | ∃ x ∈ (ν₁ : Measure Point).support,
      ∃ y ∈ (ν₂ : Measure Point).support, dist x y = d})
    (h_supp1 : (ν₁ : Measure Point).support ⊆ closedBall (0 : Point) 1)
    (h_supp2 : (ν₂ : Measure Point).support ⊆ closedBall (0 : Point) 1)
    (hν₁_growth : ∀ (x : Point) (r : ℝ), 0 < r →
      ν₁ (Metric.ball x r) ≤ Real.toNNReal (C * r))
    (hν₂_growth : ∀ (x : Point) (r : ℝ), 0 < r →
      ν₂ (Metric.ball x r) ≤ Real.toNNReal (C * r))
    (h_thin12 : HasMeasureThinTubes σ K c ν₁ ν₂)
    (h_thin21 : HasMeasureThinTubes σ K c ν₂ ν₁)
    (τ : ℝ) (hτ : 0 < τ)
    (hτ_small : τ < (1 - σ) / 14)
    (hτ_small2 : τ < σ * (1 - σ) / (11 + 3 * σ))
    (M : ℝ) (hM : 1 ≤ M)
    (K' : ℝ) (hK'_def : K' = Real.rpow (max K (C ^ 2 * M / c)) M)
    (r2 : ℝ) (N : ℕ)
    (hr2_eq : r2 = (2 : ℝ)^(-(N : ℝ)))
    (h_geom_sum : ∑' (n : ℕ), ENNReal.ofReal (2 * ((2:ℝ)^(-(n+N:ℝ)))^τ) < ENNReal.ofReal c)
    (hK'_r0_large : (2 : ℝ) ^ (σ + τ) < K' * (chooseR0 K τ r2 hK hτ) ^ (σ + τ))
    (hK'_r0_lower : K' / (2 : ℝ) ^ (σ + τ) ≥ 2 * (chooseR0 K τ r2 hK hτ) ^ (2 * τ))
    (r0 : ℝ)
    (hr0_eq : r0 = chooseR0 K τ r2 hK hτ)
    (κ : ℝ)
    (hκ : κ = 14 * τ / (1 - σ))
    (hκ_lt_one : κ < 1)
    (ε_F δ₀ : ℝ)
    (hε_F_pos : 0 < ε_F)
    (hδ₀_pos : 0 < δ₀)
    (hF_estimate : ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ δ₀ →
      ∀ (X : Set Point) (T : Point → Set Line2),
        X.Nonempty → X ⊆ closedBall 0 1 →
        IsDeltaSet δ 1 (Real.rpow δ (-ε_F)) hδ (by norm_num) (Real.rpow_nonneg hδ.le _) X →
        (∀ x ∈ X, (T x).Nonempty ∧
          IsDeltaSet δ σ (Real.rpow δ (-ε_F)) hδ (by linarith [hσ.1, hβ]) (Real.rpow_nonneg hδ.le _) (T x) ∧
          ∀ ℓ ∈ T x, x ∈ tube δ ℓ) →
        Set.Finite (⋃ x ∈ X, T x) →
        (⋃ x ∈ X, T x).ncard ≥ Nat.ceil (Real.rpow δ (-2 * σ - ε_F)))
    (hεF_large3 : 8 * τ + 3 * κ < ε_F)
    (hC_B_r0 : ∀ (r : ℝ), 0 < r → r ≤ r0 →
      r ≤ Real.rpow (60000 * K^2 * (34 : ℝ)^σ * (Line2_exists_doubling.choose : ℝ)^7 / Real.rpow (2 : ℝ) (-ε_F))
        (-1 / (ε_F - κ - 5 * τ)))
    (hδ_le_r0 : 2 * r0 ≤ δ₀)
    (h_scale_r0 : ∀ (r : ℝ), 0 < r → r ≤ r0 →
      (Real.rpow 2 (-(2 * σ + ε_F)) * Real.rpow r (-(ε_F - 8 * τ - 2 * κ)) >
        80000 * Real.rpow r (-κ)) ∧
      (Real.rpow r τ ≤ 1 / 6) ∧
      (2 * r ≤ (Real.sqrt 3 / 2) * Real.rpow r κ) ∧
      (4 * r / (Real.rpow r κ / 4) ≤ 1))
    (C_X_const : ℝ)
    (hC_X_const_nonneg : 0 ≤ C_X_const)
    (hC_X_bound_r0 : C_X_const * (Point_exists_doubling.choose : ℝ) ≤ Real.rpow (2 * r0) (-ε_F))
    (hC_X_extraction_bound : ∀ (r : ℝ), 0 < r → r ≤ r0 →
      let m := Real.rpow r τ / 2
      let L := max 0 (Real.log (2000 * C / (m * r))) + 1
      let C_X := 100 * C * L / m
      C_X * (Point_exists_doubling.choose : ℝ) ≤ Real.rpow (2 * r) (-ε_F))
    (h_conc_r0 : ∀ (r : ℝ), 0 < r → r ≤ r0 →
      r ≤ 1 / 8 ∧
      ∃ (N : ℕ), 0 < N ∧
        2 * (2 : ℝ) + r ≤ r * (2 : ℝ)^N ∧
        Real.rpow r (σ + 3 * τ) ≥ C * r + 792 * (N : ℝ) * Real.rpow r (σ + 4 * τ) ∧
        Real.rpow r τ * (((Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) + 1 : ℕ) : ℝ)) * K * (2 : ℝ)^σ ≤ 396 ∧
        Real.rpow r τ * (((Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) + 1 : ℕ) : ℝ)) * K * (2 : ℝ)^σ ≤ 66 ∧
        (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2) + 1 : ℝ) ≤
          (1 / 1584 : ℝ) * Real.rpow r (-τ) ∧
        Real.rpow r (-2 * τ) > (10^7 : ℝ) * K * C * Real.rpow ((2 + r) / 4) σ ∧
        Real.rpow r τ * Real.log (1 / r) ≤ (1 / 100 : ℝ) ∧
        20 * C * Real.rpow r τ < 1 ∧
        18 * C * r ≤ Real.rpow r (σ + 3 * τ)) :
    HasMeasureThinTubes (σ + τ) K' (3 * c) ν₁ ν₂ := by
  -- Step 1: Unpack thin-tube hypotheses
  rcases h_thin12 with ⟨hβ12, hK12, hc12, E₁, hE₁_meas, hE₁_sub, hE₁_measure, hE₁_bound⟩
  rcases h_thin21 with ⟨hβ21, hK21, hc21, E₂, hE₂_meas, hE₂_sub, hE₂_measure, hE₂_bound⟩

  -- Step 2: Define G = E₁ ∩ E₂_swapped
  let E₂_swapped : Set (Point × Point) := swapSet E₂
  have hE₂_swapped_meas : MeasurableSet E₂_swapped :=
    hE₂_meas.preimage (by fun_prop)
  let G : Set (Point × Point) := E₁ ∩ E₂_swapped
  have hG_meas : MeasurableSet G := hE₁_meas.inter hE₂_swapped_meas

  have hG_measure : (ν₁.prod ν₂) G ≥ ENNReal.ofReal (1 - 2 * c) := by
    let μ : Measure (Point × Point) := (ν₁.prod ν₂ : Measure (Point × Point))
    have hc_nonneg : 0 ≤ c := le_of_lt hc.1
    have hc_le_half : c ≤ 1 / 2 := by
      have h : c < 1 / 10 := hc.2
      have h2 : (1 : ℝ) / 10 ≤ 1 / 2 := by norm_num
      exact h.le.trans h2
    have h_sub_conv : (1 - ENNReal.ofReal c) = ENNReal.ofReal (1 - c) := by
      rw [ENNReal.ofReal_sub] <;> norm_num <;> linarith
    have hE1_conv : μ E₁ ≥ ENNReal.ofReal (1 - c) := by
      have h_coe1 : μ E₁ = ↑((ν₁.prod ν₂) E₁) :=
        (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (ν₁.prod ν₂) E₁).symm
      have h1 : ↑((ν₁.prod ν₂) E₁) ≥ 1 - ENNReal.ofReal c := hE₁_measure
      have h2 : ↑((ν₁.prod ν₂) E₁) ≥ ENNReal.ofReal (1 - c) := by
        have h3 : (1 - ENNReal.ofReal c) = ENNReal.ofReal (1 - c) := h_sub_conv
        rw [h3] at h1; exact h1
      rw [h_coe1]; exact h2
    have h_swap : (ν₁.prod ν₂) E₂_swapped = (ν₂.prod ν₁) E₂ :=
      swapSet_measure ν₁ ν₂ hE₂_meas
    have hE2_conv : μ E₂_swapped ≥ ENNReal.ofReal (1 - c) := by
      have h_coe2 : μ E₂_swapped = ↑((ν₁.prod ν₂) E₂_swapped) :=
        (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (ν₁.prod ν₂) E₂_swapped).symm
      have h4 : ↑((ν₂.prod ν₁) E₂) ≥ 1 - ENNReal.ofReal c := by exact le_of_le_of_eq hE₂_measure rfl
      have h1 : ↑((ν₁.prod ν₂) E₂_swapped) ≥ 1 - ENNReal.ofReal c := by
        rw [h_swap]; exact h4
      have h2 : ↑((ν₁.prod ν₂) E₂_swapped) ≥ ENNReal.ofReal (1 - c) := by
        have h3 : (1 - ENNReal.ofReal c) = ENNReal.ofReal (1 - c) := h_sub_conv
        rw [h3] at h1; exact h1
      rw [h_coe2]; exact h2
    have hG_enn : μ G ≥ ENNReal.ofReal (1 - 2 * c) :=
      intersection_measure_lower_bound hE₁_meas hE₂_swapped_meas
        hc_nonneg hc_le_half hE1_conv hE2_conv
    have h_coe : μ G = ↑((ν₁.prod ν₂) G) := by simp [μ] <;> rfl
    rw [h_coe] at hG_enn
    exact hG_enn

  have hσ_pos : 0 < σ := by
    have h1 : β ≤ σ := hσ.1
    linarith [hβ]
  have hστ_pos : 0 < σ + τ := by linarith [hσ_pos]
  have hK'_one : 1 ≤ K' := by
    have h1 : 1 ≤ max K (C ^ 2 * M / c) := by
      apply le_max_of_le_left
      exact hK
    have h2 : 0 ≤ M := by linarith
    have h3 : 1 ≤ Real.rpow (max K (C ^ 2 * M / c)) M :=
      Real.one_le_rpow h1 h2
    rw [hK'_def]
    exact h3
  have hK'_pos : 0 < K' := by linarith
  have h3c_lt_one : 3 * c < 1 := by linarith [hc.2]

  -- Step 3: By contradiction, assume not thin tubes
  by_contra h_not_thin

  -- Step 4 (B1): G ∩ HBarG_dyadic(K'') has measure ≥ c
  let K'' : ℝ := K' / (2 : ℝ) ^ (σ + τ)
  have hK''_pos : 0 < K'' := by positivity
  have hK''_nonneg : 0 ≤ K'' := by positivity
  have hστ_nonneg : 0 ≤ σ + τ := by linarith

  have hHBarG_dyadic : (ν₁.prod ν₂) (G ∩ HBarG_dyadic ν₂ G K'' σ τ) ≥ ENNReal.ofReal c :=
    bad_set_measure_G ν₁ ν₂ G hG_meas K' σ τ c hK'_one hστ_pos hc.1 h3c_lt_one
      hG_measure h_not_thin

  -- Step 5: Define H_r' = G ∩ HBarG_r_strict
  let H_r' : ℝ → Set (Point × Point) := fun r => G ∩ HBarG_r_strict ν₂ G K'' σ τ r

  have hH_union_eq : (G ∩ HBarG_dyadic ν₂ G K'' σ τ) = ⋃ r ∈ (Dyadic : Set ℝ), H_r' r := by
    have h1 : HBarG_dyadic ν₂ G K'' σ τ = ⋃ r ∈ (Dyadic : Set ℝ), HBarG_r_strict ν₂ G K'' σ τ r := by
      ext p; simp [HBarG_dyadic, H_r', Set.mem_iUnion₂] <;> tauto
    rw [h1]
    ext p
    simp [H_r', Set.mem_iUnion₂] <;> tauto

  have hHBarG_r_meas : ∀ (r : ℝ), 0 < r → MeasurableSet (HBarG_r_strict ν₂ G K'' σ τ r) :=
    fun r hr => HBarG_r_strict_measurable ν₂ G hG_meas K'' σ τ r hr hK''_nonneg hστ_nonneg

  have hHBarG_empty_nonpos : ∀ (r : ℝ), r ≤ 0 → HBarG_r_strict ν₂ G K'' σ τ r = ∅ := by
    intro r hr
    ext p
    simp only [HBarG_r_strict, Set.mem_empty_iff_false, iff_false]
    intro h
    rcases h with ⟨ℓ, _, hytube⟩
    have h_tube_empty : Metric.thickening r (ℓ : Set Point) = ∅ := by
      rw [Metric.thickening_eq_empty_iff]
      exact Or.inl hr
    rw [h_tube_empty] at hytube
    simpa using hytube
  have hH_r'_meas : ∀ (r : ℝ), MeasurableSet (H_r' r) := by
    intro r
    by_cases hr : 0 < r
    · exact hG_meas.inter (hHBarG_r_meas r hr)
    · have hle : r ≤ 0 := by linarith
      have h : HBarG_r_strict ν₂ G K'' σ τ r = ∅ := hHBarG_empty_nonpos r hle
      rw [show H_r' r = G ∩ HBarG_r_strict ν₂ G K'' σ τ r from rfl, h]
      <;> simp <;> exact hG_meas

  -- Step 6: Set up scale pigeonhole parameters
  have hr0_eq' : r0 = chooseR0 K τ r2 hK hτ := by
    exact hr0_eq
  have hN_pos : 1 ≤ N := by
    by_contra h
    have h0 : N = 0 := by omega
    have h_sum : ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ) < ENNReal.ofReal c :=
      h_geom_sum
    have h_eq : ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ) =
               ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n : ℝ))) ^ τ) := by
      congr with n
      rw [h0] <;> simp
    rw [h_eq] at h_sum
    let f : ℕ → ENNReal := fun n => ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n : ℝ))) ^ τ)
    have h_sum0 : ∑' n : ℕ, f n < ENNReal.ofReal c := h_sum
    have h_first : f 0 ≤ ∑' n : ℕ, f n := ENNReal.le_tsum (a := 0)
    have h_f0 : f 0 = ENNReal.ofReal 2 := by
      simp [f] <;> norm_num
    have h_cont : ENNReal.ofReal 2 ≤ ENNReal.ofReal c := by
      rw [h_f0] at h_first
      exact le_trans h_first h_sum0.le
    have h_c_lt_2 : c < 2 := by linarith [hc.2]
    have h : ENNReal.ofReal c < ENNReal.ofReal 2 := ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.mpr h_c_lt_2
    exact not_le.mpr h h_cont
  have hr2_eq' : r2 = (2 : ℝ) ^ (-(N : ℝ)) := hr2_eq
  have hr2_pos : 0 < r2 := by
    rw [hr2_eq] <;> positivity
  have hr2_lt_one : r2 < 1 := by
    rw [hr2_eq]
    have h2 : (N : ℝ) ≥ 1 := by exact_mod_cast hN_pos
    have h3 : (2 : ℝ) ^ (-(N : ℝ)) < (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    simpa using h3
  have hr0_pos : 0 < r0 := by
    rw [hr0_eq']
    have h2 : 0 < K ^ (-(1 / τ)) := by positivity
    exact lt_min h2 hr2_pos
  have hr0_lt_one : r0 < 1 := by
    have h1 : r0 ≤ r2 := by
      rw [hr0_eq']
      exact min_le_right _ _
    exact lt_of_le_of_lt h1 hr2_lt_one
  have hr0_le_r2 : r0 ≤ r2 := by
    rw [hr0_eq']
    exact min_le_right _ _
  have hr0_le : r0 ≤ (2 : ℝ) ^ (-(N : ℝ)) := by
    calc r0 ≤ r2 := hr0_le_r2
         _ = (2 : ℝ) ^ (-(N : ℝ)) := hr2_eq

  -- h_empty: for r > r0, H_r' = ∅ because K'' * r^(σ+τ) > 1
  have hK''_r0 : K'' * r0 ^ (σ + τ) ≥ 1 := by
    have h1 : K'' * r0 ^ (σ + τ) = K' * r0 ^ (σ + τ) / (2 : ℝ) ^ (σ + τ) := by
      dsimp only [K''] <;> ring
    rw [h1]
    have h2 : (2 : ℝ) ^ (σ + τ) < K' * r0 ^ (σ + τ) := by
      have h21 : r0 = chooseR0 K τ r2 hK hτ := hr0_eq'
      rw [h21] at *
      exact hK'_r0_large
    have h3 : 0 < (2 : ℝ) ^ (σ + τ) := by positivity
    have h4 : 1 < K' * r0 ^ (σ + τ) / (2 : ℝ) ^ (σ + τ) := by
      exact (one_lt_div h3).mpr h2
    exact le_of_lt h4
  have h_empty : ∀ (r : ℝ), r > r0 → H_r' r = ∅ := by
    intro r hr
    have h4 : K'' * r ^ (σ + τ) > 1 := by
      have h5 : r0 < r := hr
      have h6 : r0 ^ (σ + τ) < r ^ (σ + τ) := by
        exact Real.rpow_lt_rpow (by linarith [hr0_pos]) (by linarith) (by linarith [hστ_pos])
      have h7 : K'' * r ^ (σ + τ) > K'' * r0 ^ (σ + τ) := by gcongr
      exact lt_of_le_of_lt hK''_r0 h7
    have h8 : HBarG_r_strict ν₂ G K'' σ τ r = ∅ := by
      ext p
      simp only [HBarG_r_strict, Set.mem_empty_iff_false, iff_false]
      intro h
      rcases h with ⟨ℓ, hℓ_bad, hytube⟩
      let G_x : Set Point := {b₂ | (p.1, b₂) ∈ G}
      have h9 : (ν₂ : Measure Point) (tubeLine r ℓ ∩ G_x) >
          ENNReal.ofReal (K'' * r ^ (σ + τ)) := by
        have h10 : (ν₂ : Measure Point) (tubeLine r ℓ ∩ G_x) >
            ENNReal.ofReal (K'' * Real.rpow r (σ + τ)) := hℓ_bad.2.2
        have h11 : K'' * Real.rpow r (σ + τ) = K'' * r ^ (σ + τ) := by rfl
        rw [h11] at h10
        exact h10
      have h10 : (ν₂ : Measure Point) (tubeLine r ℓ ∩ G_x) ≤ 1 := by
        have h_univ : (ν₂ : Measure Point) Set.univ = 1 := measure_univ
        have h : (ν₂ : Measure Point) (tubeLine r ℓ ∩ G_x) ≤ (ν₂ : Measure Point) Set.univ :=
          measure_mono (subset_univ _)
        rw [h_univ] at h
        exact h
      have h11 : ENNReal.ofReal (K'' * r ^ (σ + τ)) > 1 := by
        have h12 : 1 < K'' * r ^ (σ + τ) := h4
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr h12
      have h13 : 1 < (ν₂ : Measure Point) (tubeLine r ℓ ∩ G_x) :=
        calc (1 : ENNReal) < ENNReal.ofReal (K'' * r ^ (σ + τ)) := h11
             _ < (ν₂ : Measure Point) (tubeLine r ℓ ∩ G_x) := h9
      exact not_le.mpr h13 h10
    have h13 : H_r' r = G ∩ HBarG_r_strict ν₂ G K'' σ τ r := by rfl
    rw [h13, h8] <;> simp

  have h_sum_small : ∑' n : ℕ, ENNReal.ofReal (2 * Real.rpow ((2 : ℝ) ^ (-(n + N : ℝ))) τ) < ENNReal.ofReal c := by
    have h_eq : ∀ (n : ℕ), ENNReal.ofReal (2 * Real.rpow ((2 : ℝ) ^ (-(n + N : ℝ))) τ) =
        ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ) := by
      intro n; rfl
    have h_main : ∑' n : ℕ, ENNReal.ofReal (2 * Real.rpow ((2 : ℝ) ^ (-(n + N : ℝ))) τ) =
        ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ) := by
      apply tsum_congr
      intro n
      exact h_eq n
    rw [h_main]
    exact h_geom_sum

  have hH_union : (ν₁.prod ν₂) (⋃ r ∈ (Dyadic : Set ℝ), H_r' r) ≥ ENNReal.ofReal c := by
    rw [←hH_union_eq]
    exact hHBarG_dyadic

  -- Step 7: Apply scale_selection
  let μ : Measure Point := ν₁
  let ν : Measure Point := ν₂
  have hH_meas' : ∀ r, MeasurableSet (H_r' r) := hH_r'_meas
  have hH_union' : (μ.prod ν) (⋃ r ∈ (Dyadic : Set ℝ), H_r' r) ≥ ENNReal.ofReal c := by
    have h_coe : (μ.prod ν) (⋃ r ∈ (Dyadic : Set ℝ), H_r' r) = (ν₁.prod ν₂) (⋃ r ∈ (Dyadic : Set ℝ), H_r' r) := by
      simp [μ, ν, ProbabilityMeasure.prod] <;> rfl
    rw [h_coe]
    exact hH_union
  have h_sum_small' : ∑' n : ℕ, ENNReal.ofReal (2 * ((2 : ℝ) ^ (-(n + N : ℝ))) ^ τ) < ENNReal.ofReal c := by
    simpa using h_sum_small
  rcases scale_selection (μ := μ) (ν := ν) τ c r0 N hτ hc.1 hr0_pos hr0_le H_r' hH_meas' hH_union' h_empty h_sum_small'
    with ⟨r, hdyad, hr_pos, hr_le, h_measure⟩
  rcases dyadic_le_r0_eq_nat r r0 hdyad hr_le hr0_lt_one with ⟨n, hr_eq⟩
  let r_sel : ℝ := r
  have hr_sel_eq : r_sel = (2 : ℝ) ^ (-(n : ℝ)) := by
    exact hr_eq
  have hr_sel_pos : 0 < r_sel := hr_pos
  have hr_sel_le : r_sel ≤ r0 := hr_le
  have hr_sel_small : r_sel < 1 := by
    have h1 : r_sel ≤ r0 := hr_sel_le
    have h2 : r0 < 1 := hr0_lt_one
    linarith
  have hH_r_measure : (ν₁.prod ν₂) (H_r' r_sel) ≥ ENNReal.ofReal (2 * Real.rpow r_sel τ) := by
    have h_coe : (μ.prod ν) (H_r' r_sel) = (ν₁.prod ν₂) (H_r' r_sel) := by
      simp [μ, ν, ProbabilityMeasure.prod] <;> rfl
    rw [h_coe] at h_measure
    have h_eq : ENNReal.ofReal (2 * r_sel ^ τ) = ENNReal.ofReal (2 * Real.rpow r_sel τ) := by rfl
    rw [h_eq] at h_measure
    exact h_measure

  -- Step 8: Define X and show ν₁(X) ≥ r^τ
  let X : Set Point := XSet (H_r' r_sel) ν₂ r_sel τ
  have hH_r_meas_set : MeasurableSet (H_r' r_sel) := hH_r'_meas r_sel
  have hX_measure_nn : ν₁ X ≥ ENNReal.ofReal (Real.rpow r_sel τ) :=
    fiber_lower_bound ν₁ ν₂ (H_r' r_sel) hH_r_meas_set r_sel τ hτ hr_sel_pos hH_r_measure
  have hX_measure : (ν₁ : Measure Point) X ≥ ENNReal.ofReal (Real.rpow r_sel τ) := by
    have h_coe : (ν₁ : Measure Point) X = ↑(ν₁ X) :=
      (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₁ X).symm
    rw [h_coe]
    exact hX_measure_nn

  -- Step 9: X ⊆ support
  have h_X_sub_support : X ⊆ (ν₁ : Measure Point).support := by
    intro x hx
    have h_fiber : (ν₂ : Measure Point) {b₂ | (x, b₂) ∈ H_r' r_sel} ≥ ENNReal.ofReal (Real.rpow r_sel τ) := by
      simpa [X, XSet] using hx
    have h2 : 0 < Real.rpow r_sel τ := Real.rpow_pos_of_pos hr_sel_pos τ
    have h3 : 0 < (ν₂ : Measure Point) {b₂ | (x, b₂) ∈ H_r' r_sel} :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr h2) h_fiber
    have h4 : Set.Nonempty {b₂ | (x, b₂) ∈ H_r' r_sel} := by
      by_contra h5
      have h6 : {b₂ | (x, b₂) ∈ H_r' r_sel} = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp h5
      rw [h6] at h3
      simp at h3
    rcases h4 with ⟨b₂, hb₂⟩
    have h5 : (x, b₂) ∈ H_r' r_sel := hb₂
    have h6 : (x, b₂) ∈ G := h5.1
    have h7 : (x, b₂) ∈ E₁ := h6.1
    have h8 : (x, b₂) ∈ (ν₁ : Measure Point).support ×ˢ (ν₂ : Measure Point).support := hE₁_sub h7
    exact h8.1

  -- Step 10: Helper: convert thin-tube bounds to ENNReal form with G restriction
  let hG_forward : ∀ (x : Point), x ∈ (ν₁ : Measure Point).support →
      ∀ (ℓ : AffineSubspace ℝ Point), x ∈ (ℓ : Set Point) →
        Module.finrank ℝ ℓ.direction = 1 → ∀ (r' : ℝ), 0 < r' →
          (↑(ν₂ {b₂ | b₂ ∈ tubeLine r' ℓ ∧ (x, b₂) ∈ G}) : ENNReal) ≤
            ENNReal.ofReal (K * Real.rpow r' σ) := by
    intro x hx_supp ℓ hxℓ hfin r' hr'
    let S_G := {b₂ | b₂ ∈ tubeLine r' ℓ ∧ (x, b₂) ∈ G}
    let S_E1 := {b₂ | b₂ ∈ tubeLine r' ℓ ∧ (x, b₂) ∈ E₁}
    have h_sub : S_G ⊆ S_E1 := by intro b₂ hb₂; exact ⟨hb₂.1, hb₂.2.1⟩
    have h1 : (ν₂ : Measure Point) S_G ≤ (ν₂ : Measure Point) S_E1 := measure_mono h_sub
    have h2 : ν₂ S_E1 ≤ Real.toNNReal (K * r' ^ σ) := hE₁_bound x hx_supp ℓ hxℓ hfin r' hr'
    have hK_nonneg : 0 ≤ K * r' ^ σ := by positivity
    have h3 : (↑(ν₂ S_E1) : ENNReal) ≤ ENNReal.ofReal (K * Real.rpow r' σ) := by
      have h4 : (ν₂ S_E1 : ℝ) ≤ K * r' ^ σ := by
        have h5 : (ν₂ S_E1 : ℝ) ≤ (Real.toNNReal (K * r' ^ σ) : ℝ) := by exact_mod_cast h2
        rw [Real.toNNReal_of_nonneg hK_nonneg] at h5
        exact h5
      have h6 : ENNReal.ofReal (↑(ν₂ S_E1 : ℝ)) ≤ ENNReal.ofReal (K * r' ^ σ) :=
        ENNReal.ofReal_le_ofReal h4
      have h7 : (↑(ν₂ S_E1) : ENNReal) = ENNReal.ofReal (↑(ν₂ S_E1 : ℝ)) := by simp
      rw [h7]
      have h8 : K * r' ^ σ = K * Real.rpow r' σ := by rfl
      rw [h8] at h6
      exact h6
    have h_eq1 : (ν₂ : Measure Point) S_E1 = ↑(ν₂ S_E1) := by exact Eq.symm (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₂ S_E1)
    calc (↑(ν₂ S_G) : ENNReal)
      = (ν₂ : Measure Point) S_G := by exact ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₂ S_G
    _ ≤ (ν₂ : Measure Point) S_E1 := h1
    _ = ↑(ν₂ S_E1) := h_eq1
    _ ≤ ENNReal.ofReal (K * Real.rpow r' σ) := h3

  let hG_reverse : ∀ (y : Point), y ∈ (ν₂ : Measure Point).support →
      ∀ (ℓ : AffineSubspace ℝ Point), y ∈ (ℓ : Set Point) →
        Module.finrank ℝ ℓ.direction = 1 → ∀ (r' : ℝ), 0 < r' →
          (↑(ν₁ {b₁ | b₁ ∈ tubeLine r' ℓ ∧ (b₁, y) ∈ G}) : ENNReal) ≤
            ENNReal.ofReal (K * Real.rpow r' σ) := by
    intro y hy_supp ℓ hyℓ hfin r' hr'
    let S_G := {b₁ | b₁ ∈ tubeLine r' ℓ ∧ (b₁, y) ∈ G}
    let S_E2 := {b₁ | b₁ ∈ tubeLine r' ℓ ∧ (y, b₁) ∈ E₂}
    have h_sub : S_G ⊆ S_E2 := by
      intro b₁ hb₁
      have hG : (b₁, y) ∈ G := hb₁.2
      have hE2_swapped : (b₁, y) ∈ E₂_swapped := hG.2
      have hE2 : (y, b₁) ∈ E₂ := by
        simpa [E₂_swapped, swapSet] using hE2_swapped
      exact ⟨hb₁.1, hE2⟩
    have h1 : (ν₁ : Measure Point) S_G ≤ (ν₁ : Measure Point) S_E2 := measure_mono h_sub
    have h2 : ν₁ S_E2 ≤ Real.toNNReal (K * r' ^ σ) := hE₂_bound y hy_supp ℓ hyℓ hfin r' hr'
    have hK_nonneg2 : 0 ≤ K * r' ^ σ := by positivity
    have h3 : (↑(ν₁ S_E2) : ENNReal) ≤ ENNReal.ofReal (K * Real.rpow r' σ) := by
      have h4 : (ν₁ S_E2 : ℝ) ≤ K * r' ^ σ := by
        have h5 : (ν₁ S_E2 : ℝ) ≤ (Real.toNNReal (K * r' ^ σ) : ℝ) := by exact_mod_cast h2
        rw [Real.toNNReal_of_nonneg hK_nonneg2] at h5
        exact h5
      have h6 : ENNReal.ofReal (↑(ν₁ S_E2 : ℝ)) ≤ ENNReal.ofReal (K * r' ^ σ) :=
        ENNReal.ofReal_le_ofReal h4
      have h7 : (↑(ν₁ S_E2) : ENNReal) = ENNReal.ofReal (↑(ν₁ S_E2 : ℝ)) := by simp
      rw [h7]
      have h8 : K * r' ^ σ = K * Real.rpow r' σ := by rfl
      rw [h8] at h6
      exact h6
    have h_eq1 : (ν₁ : Measure Point) S_E2 = ↑(ν₁ S_E2) := by exact Eq.symm (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₁ S_E2)
    calc (↑(ν₁ S_G) : ENNReal)
      = (ν₁ : Measure Point) S_G := by exact ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₁ S_G
    _ ≤ (ν₁ : Measure Point) S_E2 := h1
    _ = ↑(ν₁ S_E2) := h_eq1
    _ ≤ ENNReal.ofReal (K * Real.rpow r' σ) := h3

  -- Step 11: Well-behaved tubes for each x ∈ X using well_behaved_tubes_G
  have h_tubes : ∀ (x : Point), x ∈ X →
      ∃ (T_x : Finset (AffineSubspace ℝ Point)) (Y_x : Set Point),
        MeasurableSet Y_x ∧
        (∀ ℓ ∈ T_x, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1) ∧
        Y_x ⊆ {b₂ | (x, b₂) ∈ G} ∧
        Y_x ⊆ ⋃ ℓ ∈ T_x, tubeLine r_sel ℓ ∧
        ν₂ Y_x ≥ ENNReal.ofReal (Real.rpow r_sel (2 * τ)) ∧
        (∀ ℓ ∈ T_x,
          ENNReal.ofReal (Real.rpow r_sel (σ + 3 * τ)) ≤ ν₂ (tubeLine r_sel ℓ ∩ Y_x) ∧
          ν₂ (tubeLine r_sel ℓ ∩ Y_x) ≤ ENNReal.ofReal (Real.rpow r_sel (σ - τ))) := by
    intro x hx
    have hK_small : K * Real.rpow r_sel τ ≤ 1 := by
      have h2 : r_sel ≤ r0 := hr_sel_le
      have h3 : r0 ≤ K ^ (-(1 / τ)) := by
        rw [hr0_eq']
        exact min_le_left _ _
      have h4 : r_sel ≤ K ^ (-(1 / τ)) := le_trans h2 h3
      have h5 : 0 < K := by linarith
      have h6 : Real.rpow r_sel τ ≤ Real.rpow (K ^ (-(1 / τ))) τ :=
        Real.rpow_le_rpow hr_sel_pos.le h4 hτ.le
      have h7 : Real.rpow (K ^ (-(1 / τ))) τ = K ^ (-1 : ℝ) := by
        have h71 : Real.rpow (K ^ (-(1 / τ))) τ = K ^ ((-(1 / τ)) * τ) :=
          (Real.rpow_mul h5.le (-(1 / τ)) τ).symm
        rw [h71]
        have h72 : (-(1 / τ)) * τ = -1 := by field_simp [hτ.ne'] <;> ring
        rw [h72]
      have h8 : K ^ (-1 : ℝ) = 1 / K := by
        have h81 : K ^ (-1 : ℝ) = (K ^ (1 : ℝ))⁻¹ := Real.rpow_neg h5.le (1 : ℝ)
        have h82 : K ^ (1 : ℝ) = K := by simp
        rw [h81, h82]
        exact inv_eq_one_div K
      have h9 : Real.rpow r_sel τ ≤ 1 / K := by
        rw [h7, h8] at h6; exact h6
      calc K * Real.rpow r_sel τ ≤ K * (1 / K) := by gcongr
        _ = 1 := by field_simp [h5.ne'] <;> ring
    have hK''_lower : K'' ≥ Real.rpow r_sel (2 * τ) := by
      have h2 : K' / (2 : ℝ) ^ (σ + τ) ≥ 2 * r0 ^ (2 * τ) := by
        have h21 : r0 = chooseR0 K τ r2 hK hτ := hr0_eq'
        rw [h21] at *
        exact hK'_r0_lower
      have h3 : r_sel ≤ r0 := hr_sel_le
      have h4 : Real.rpow r_sel (2 * τ) ≤ Real.rpow r0 (2 * τ) :=
        Real.rpow_le_rpow hr_sel_pos.le h3 (by linarith [hτ])
      have h5 : Real.rpow r0 (2 * τ) = r0 ^ (2 * τ) := by rfl
      have h_pos : 0 ≤ Real.rpow r_sel (2 * τ) := Real.rpow_nonneg hr_sel_pos.le _
      calc K' / (2 : ℝ) ^ (σ + τ)
        ≥ 2 * r0 ^ (2 * τ) := h2
      _ ≥ 2 * Real.rpow r_sel (2 * τ) := by
        have h7 : Real.rpow r_sel (2 * τ) ≤ r0 ^ (2 * τ) := by
          rw [←h5]; exact h4
        gcongr
      _ ≥ Real.rpow r_sel (2 * τ) := by
        exact le_mul_of_one_le_left h_pos (by norm_num)
    have hxs : x ∈ (ν₁ : Measure Point).support := h_X_sub_support hx
    -- Show XSet matches WBTG.XSet
    have hx' : x ∈ WBTG.XSet (WBTG.HG_r G ν₂ K'' σ τ r_sel) ν₂ r_sel τ := by
      simpa [X, XSet, WBTG.XSet, WBTG.HG_r, WBTG.HBarG_r, H_r', HBarG_r_strict, BadTubesG_strict, WBTG.BadTubesG, WBTG.tubeLine, tubeLine] using hx
    rcases well_behaved_tubes_G ν₁ ν₂ G K K'' σ τ r_sel c
      (by linarith [hσ_pos]) hτ hr_sel_pos hr_sel_small
      hK_small hK''_lower hG_meas hG_forward
      x hxs hx' with ⟨T_x, Y_x, hYx_meas, h_lines, hY_HG, hY_sub, hY_mass, h_bounds⟩
    have hY_G : Y_x ⊆ {b₂ | (x, b₂) ∈ G} := by
      intro b₂ hb₂
      have h : (x, b₂) ∈ WBTG.HG_r G ν₂ K'' σ τ r_sel := hY_HG hb₂
      exact h.1
    exact ⟨T_x, Y_x, hYx_meas, h_lines, hY_G, hY_sub, hY_mass, h_bounds⟩

  -- Step 12: Direction extraction + cardinality dichotomy
  have hκ_pos : 0 < κ := by
    rw [hκ]
    have h1 : 0 < 1 - σ := by linarith [hσ.2, hε]
    positivity
  have hκ_eq : κ = 14 * τ / (1 - σ) := hκ

  let R_low : ℝ := 1 / 2
  let R_high : ℝ := 2
  have hR_low_pos : 0 < R_low := by norm_num
  have hR_high_pos : 0 < R_high := by norm_num
  have hR_le : R_low ≤ R_high := by norm_num
  have hR_high_ge_one : (1 : ℝ) ≤ R_high := by norm_num
  have h_rκ_le_R : Real.rpow r_sel κ ≤ R_high := by
    have h1 : Real.rpow r_sel κ ≤ 1 := Real.rpow_le_one hr_sel_pos.le hr_sel_small.le (by positivity)
    linarith
  have hK_pos : 0 < K := by linarith
  have hσ' : 0 ≤ σ := le_of_lt hσ_pos

  let X_conc : Set Point :=
    {x ∈ X | ∃ (T_x S T_conc : Finset (AffineSubspace ℝ Point)) (Y_x : Set Point),
      MeasurableSet Y_x ∧
      (∀ ℓ ∈ T_x, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1) ∧
      Y_x ⊆ {b₂ | (x, b₂) ∈ G} ∧
      Y_x ⊆ ⋃ ℓ ∈ T_x, tubeLine r_sel ℓ ∧
      ν₂ Y_x ≥ ENNReal.ofReal (Real.rpow r_sel (2 * τ)) ∧
      (∀ ℓ ∈ T_x,
        ENNReal.ofReal (Real.rpow r_sel (σ + 3 * τ)) ≤ ν₂ (tubeLine r_sel ℓ ∩ Y_x) ∧
        ν₂ (tubeLine r_sel ℓ ∩ Y_x) ≤ ENNReal.ofReal (Real.rpow r_sel (σ - τ))) ∧
      S ⊆ T_x ∧
      (∀ ℓ1 ∈ S, ∀ ℓ2 ∈ S, ℓ1 ≠ ℓ2 →
        submoduleDirDist ℓ1.direction ℓ2.direction ≥ r_sel / (4 * R_high)) ∧
      T_conc ⊆ S ∧
      (∀ ℓ ∈ T_conc, IsConcentrated (ν₂ : Measure Point) Y_x (tubeLine r_sel ℓ) r_sel κ) ∧
      S.Nonempty ∧
      2 * T_conc.card ≥ S.card ∧
      (S.card : ℝ) ≥ Real.rpow r_sel (2 * τ - σ) / (K * (2 : ℝ)^σ)}

  let X_nonconc : Set Point :=
    {x ∈ X | ∃ (T_x S S_non : Finset (AffineSubspace ℝ Point)) (Y_x : Set Point),
      MeasurableSet Y_x ∧
      (∀ ℓ ∈ T_x, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1) ∧
      Y_x ⊆ {b₂ | (x, b₂) ∈ G} ∧
      Y_x ⊆ ⋃ ℓ ∈ T_x, tubeLine r_sel ℓ ∧
      ν₂ Y_x ≥ ENNReal.ofReal (Real.rpow r_sel (2 * τ)) ∧
      (∀ ℓ ∈ T_x,
        ENNReal.ofReal (Real.rpow r_sel (σ + 3 * τ)) ≤ ν₂ (tubeLine r_sel ℓ ∩ Y_x) ∧
        ν₂ (tubeLine r_sel ℓ ∩ Y_x) ≤ ENNReal.ofReal (Real.rpow r_sel (σ - τ))) ∧
      S ⊆ T_x ∧
      (∀ ℓ1 ∈ S, ∀ ℓ2 ∈ S, ℓ1 ≠ ℓ2 →
        submoduleDirDist ℓ1.direction ℓ2.direction ≥ r_sel / (4 * R_high)) ∧
      S_non ⊆ S ∧
      (∀ ℓ ∈ S_non, IsNonConcentrated (ν₂ : Measure Point) Y_x (tubeLine r_sel ℓ) r_sel κ) ∧
      S.Nonempty ∧
      2 * S_non.card ≥ S.card ∧
      (S.card : ℝ) ≥ Real.rpow r_sel (2 * τ - σ) / (K * (2 : ℝ)^σ)}

  have h_partition : X ⊆ X_conc ∪ X_nonconc := by
    intro x hx
    rcases h_tubes x hx with ⟨T_x, Y_x, hYx_meas, h_lines, hY_G, hY_sub, hY_mass, h_bounds⟩
    have hG_subset : G ⊆ (ν₁ : Measure Point).support ×ˢ (ν₂ : Measure Point).support := by
      intro p hp; have h1 : p ∈ E₁ := hp.1; exact hE₁_sub h1
    have hY_supp : Y_x ⊆ (ν₂ : Measure Point).support := by
      intro b₂ hb₂; have hG : (x, b₂) ∈ G := hY_G hb₂; exact (hG_subset hG).2
    have h_x_supp : x ∈ (ν₁ : Measure Point).support := h_X_sub_support hx
    have h_dist_upper : ∀ y ∈ Y_x, dist x y ≤ R_high := by
      intro y hy
      have h_y_supp : y ∈ (ν₂ : Measure Point).support := hY_supp hy
      have hx1 : dist x 0 ≤ 1 := h_supp1 h_x_supp
      have hy1 : dist y 0 ≤ 1 := h_supp2 h_y_supp
      calc dist x y ≤ dist x 0 + dist 0 y := dist_triangle x 0 y
           _ = dist x 0 + dist y 0 := by rw [dist_comm y 0]
           _ ≤ 1 + 1 := by gcongr <;> linarith
           _ = 2 := by norm_num
    -- Wrapper for direction_grid_extraction: restrict hG_forward to Y_x
    have h_forward' : ∀ (ℓ : AffineSubspace ℝ Point),
        x ∈ (ℓ : Set Point) → Module.finrank ℝ ℓ.direction = 1 →
        ∀ (r' : ℝ), 0 < r' →
          (ν₂ : Measure Point) (Metric.thickening r' (ℓ : Set Point) ∩ Y_x) ≤
            ENNReal.ofReal (K * Real.rpow r' σ) := by
      intro ℓ hxℓ hfin r' hr'
      have h_sub : Metric.thickening r' (ℓ : Set Point) ∩ Y_x ⊆
          {b₂ | b₂ ∈ tubeLine r' ℓ ∧ (x, b₂) ∈ G} := by
        intro b₂ hb₂
        exact ⟨hb₂.1, hY_G hb₂.2⟩
      have h1 : (ν₂ : Measure Point) (Metric.thickening r' (ℓ : Set Point) ∩ Y_x) ≤
          (ν₂ : Measure Point) {b₂ | b₂ ∈ tubeLine r' ℓ ∧ (x, b₂) ∈ G} :=
        measure_mono h_sub
      have h_coe : (ν₂ : Measure Point) {b₂ | b₂ ∈ tubeLine r' ℓ ∧ (x, b₂) ∈ G} =
          (↑(ν₂ {b₂ | b₂ ∈ tubeLine r' ℓ ∧ (x, b₂) ∈ G}) : ENNReal) :=
        (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₂ _).symm
      rw [h_coe] at h1
      exact le_trans h1 (hG_forward x h_x_supp ℓ hxℓ hfin r' hr')
    let P : AffineSubspace ℝ Point → Set Point := fun ℓ => tubeLine r_sel ℓ ∩ Y_x
    have hR_ge_r : r_sel ≤ R_high := by linarith [hR_high_ge_one, hr_sel_small]
    have hP_sub_tube : ∀ ℓ ∈ T_x, P ℓ ⊆ Metric.thickening r_sel (ℓ : Set Point) := by
      intro ℓ _ z hz; exact hz.1
    have hP_sub_Gx : ∀ ℓ ∈ T_x, P ℓ ⊆ Y_x := by intro ℓ _ z hz; exact hz.2
    have hP_meas : ∀ ℓ ∈ T_x, MeasurableSet (P ℓ) := by
      intro ℓ hℓ; have h1 : P ℓ = tubeLine r_sel ℓ ∩ Y_x := by rfl
      rw [h1]; exact (Metric.isOpen_thickening.measurableSet).inter hYx_meas
    have hP_bounded : ∀ ℓ ∈ T_x, ∀ y ∈ P ℓ, dist x y ≤ 2 * R_high + Real.rpow r_sel κ := by
      intro ℓ _ y hy; have h : dist x y ≤ R_high := h_dist_upper y hy.2
      have h2 : 0 ≤ Real.rpow r_sel κ := Real.rpow_nonneg hr_sel_pos.le κ; linarith
    rcases direction_grid_extraction_card x T_x P Y_x r_sel R_high κ K σ
      hr_sel_pos hr_sel_small hR_high_pos hR_ge_r hκ_pos hκ_lt_one h_rκ_le_R
      hK_pos hσ' h_lines hP_sub_tube hP_sub_Gx hP_meas hP_bounded h_forward'
      with ⟨S, hS_sub, hS_sep, hS_card⟩
    have hS_sep' : ∀ ℓ1 ∈ S, ∀ ℓ2 ∈ S, ℓ1 ≠ ℓ2 →
        submoduleDirDist ℓ1.direction ℓ2.direction ≥ r_sel / (4 * R_high) := by
      intro ℓ1 h1 ℓ2 h2 hne; exact le_of_lt (hS_sep ℓ1 h1 ℓ2 h2 hne)
    let T_conc : Finset _ := S.filter (fun ℓ => IsConcentrated (ν₂ : Measure Point) Y_x (tubeLine r_sel ℓ) r_sel κ)
    let S_non : Finset _ := S \ T_conc
    have hT_conc_sub : T_conc ⊆ S := filter_subset _ _
    have hS_non_sub : S_non ⊆ S := by intro ℓ hℓ; exact (Finset.mem_sdiff.mp hℓ).1
    have h_conc_prop : ∀ ℓ ∈ T_conc, IsConcentrated (ν₂ : Measure Point) Y_x (tubeLine r_sel ℓ) r_sel κ :=
      fun ℓ hℓ => (Finset.mem_filter.mp hℓ).2
    have h_non_prop : ∀ ℓ ∈ S_non, IsNonConcentrated (ν₂ : Measure Point) Y_x (tubeLine r_sel ℓ) r_sel κ := by
      intro ℓ hℓ
      have h_not_conc : ℓ ∉ T_conc := (Finset.mem_sdiff.mp hℓ).2
      have h_in_S : ℓ ∈ S := (Finset.mem_sdiff.mp hℓ).1
      have h1 : ¬ IsConcentrated (ν₂ : Measure Point) Y_x (tubeLine r_sel ℓ) r_sel κ := by
        simpa [T_conc, Finset.mem_filter, h_in_S] using h_not_conc
      exact not_concentrated_imp_nonconcentrated h1
    have h_lines_S : ∀ ℓ ∈ S, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1 :=
      fun ℓ hℓ => h_lines ℓ (hS_sub hℓ)
    have h_bounds_S : ∀ ℓ ∈ S,
        ENNReal.ofReal (Real.rpow r_sel (σ + 3 * τ)) ≤ ν₂ (tubeLine r_sel ℓ ∩ Y_x) ∧
        ν₂ (tubeLine r_sel ℓ ∩ Y_x) ≤ ENNReal.ofReal (Real.rpow r_sel (σ - τ)) :=
      fun ℓ hℓ => h_bounds ℓ (hS_sub hℓ)
    have hK_rpos : 0 < K * Real.rpow (2 * r_sel) σ := by
      have h1 : 0 < Real.rpow (2 * r_sel) σ := Real.rpow_pos_of_pos (by positivity) σ
      positivity
    have h_denom_pos : 0 < ENNReal.ofReal (K * Real.rpow (2 * r_sel) σ) :=
      ENNReal.ofReal_pos.mpr hK_rpos
    have h_denom_ne_zero : ENNReal.ofReal (K * Real.rpow (2 * r_sel) σ) ≠ 0 := h_denom_pos.ne'
    have h_union_Y : Y_x ⊆ ⋃ ℓ ∈ T_x, P ℓ := by
      intro y hy
      have h1 : y ∈ ⋃ ℓ ∈ T_x, tubeLine r_sel ℓ := hY_sub hy
      have h2 : ∃ (ℓ : AffineSubspace ℝ Point), ℓ ∈ T_x ∧ y ∈ tubeLine r_sel ℓ := by
        simpa [Finset.mem_biUnion] using h1
      rcases h2 with ⟨ℓ, hℓ, h3⟩
      simpa [Finset.mem_biUnion] using ⟨ℓ, hℓ, ⟨h3, hy⟩⟩
    have h_union_mass : (ν₂ : Measure Point) (⋃ ℓ ∈ T_x, P ℓ) ≥
        ENNReal.ofReal (Real.rpow r_sel (2 * τ)) := by
      have hY_pos' : (ν₂ : Measure Point) Y_x ≥ ENNReal.ofReal (Real.rpow r_sel (2 * τ)) :=
        by simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hY_mass
      exact le_trans hY_pos' (measure_mono h_union_Y)
    have hS_card_lower_ennreal : (S.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow r_sel (2 * τ) / (K * Real.rpow (2 * r_sel) σ)) := by
      set C : ENNReal := ENNReal.ofReal (K * Real.rpow (2 * r_sel) σ) with hC_def
      have h_div : (ν₂ : Measure Point) (⋃ ℓ ∈ T_x, P ℓ) ≤ (S.card : ENNReal) * C := hS_card
      have h_div2 : (ν₂ : Measure Point) (⋃ ℓ ∈ T_x, P ℓ) / C ≤ (S.card : ENNReal) := by
        have h9 : (ν₂ : Measure Point) (⋃ ℓ ∈ T_x, P ℓ) / C ≤ ((S.card : ENNReal) * C) / C := by gcongr
        have hC_ne_top : C ≠ ⊤ := by
          simp [hC_def, ENNReal.ofReal_ne_top]
        have h10 : ((S.card : ENNReal) * C) / C = (S.card : ENNReal) := by
          rw [div_eq_mul_inv, mul_assoc]
          have h11 : C * C⁻¹ = 1 := by
            apply ENNReal.mul_inv_cancel
            · exact h_denom_ne_zero
            · exact hC_ne_top
          rw [h11, mul_one]
        rw [h10] at h9
        exact h9
      have h_rpos2τ : 0 < Real.rpow r_sel (2 * τ) := Real.rpow_pos_of_pos hr_sel_pos _
      have h_pos_div : 0 ≤ Real.rpow r_sel (2 * τ) / (K * Real.rpow (2 * r_sel) σ) := by
        apply div_nonneg
        · exact Real.rpow_nonneg hr_sel_pos.le _
        · exact hK_rpos.le
      have h_div_real : ENNReal.ofReal (Real.rpow r_sel (2 * τ)) / C =
          ENNReal.ofReal (Real.rpow r_sel (2 * τ) / (K * Real.rpow (2 * r_sel) σ)) := by
        simp only [hC_def]
        rw [ENNReal.ofReal_div_of_pos hK_rpos] <;> rfl
      calc (S.card : ENNReal)
        ≥ (ν₂ : Measure Point) (⋃ ℓ ∈ T_x, P ℓ) / C := h_div2
      _ ≥ ENNReal.ofReal (Real.rpow r_sel (2 * τ)) / C := by gcongr <;> exact h_union_mass
      _ = ENNReal.ofReal (Real.rpow r_sel (2 * τ) / (K * Real.rpow (2 * r_sel) σ)) := h_div_real
    have hS_nonempty : S.Nonempty := by
      have h_union_pos : 0 < (ν₂ : Measure Point) (⋃ ℓ ∈ T_x, P ℓ) :=
        have h_rpos : 0 < Real.rpow r_sel (2 * τ) := Real.rpow_pos_of_pos hr_sel_pos _
        have hpos : 0 < ENNReal.ofReal (Real.rpow r_sel (2 * τ)) := ENNReal.ofReal_pos.mpr h_rpos
        lt_of_lt_of_le hpos h_union_mass
      by_contra h
      have h' : S = ∅ := by simpa using h
      rw [h'] at hS_card
      simp at hS_card
      exact h_union_pos.ne' hS_card
    have h_rpow_div : Real.rpow (2 * r_sel) σ = (2 : ℝ)^σ * Real.rpow r_sel σ := by
      have h : Real.rpow (2 * r_sel) σ = Real.rpow 2 σ * Real.rpow r_sel σ :=
        Real.mul_rpow (by positivity) (by positivity)
      have h2 : Real.rpow 2 σ = (2 : ℝ)^σ := by simp
      rw [h, h2] <;> ring
    have hS_card_lower_real : (S.card : ℝ) ≥
        Real.rpow r_sel (2 * τ - σ) / (K * (2 : ℝ)^σ) := by
      have h_pos_expr : 0 ≤ Real.rpow r_sel (2 * τ) / (K * Real.rpow (2 * r_sel) σ) := by
        apply div_nonneg
        · exact Real.rpow_nonneg hr_sel_pos.le _
        · exact hK_rpos.le
      have h1 : (S.card : ENNReal) ≥ ENNReal.ofReal (Real.rpow r_sel (2 * τ) / (K * Real.rpow (2 * r_sel) σ)) :=
        hS_card_lower_ennreal
      have h2 : ((S.card : ENNReal)).toReal ≥ (ENNReal.ofReal (Real.rpow r_sel (2 * τ) / (K * Real.rpow (2 * r_sel) σ))).toReal :=
        ENNReal.toReal_le_toReal (by simp) (by simp) |>.mpr h1
      have h3 : ((S.card : ENNReal)).toReal = (S.card : ℝ) := by simp
      have h4 : (ENNReal.ofReal (Real.rpow r_sel (2 * τ) / (K * Real.rpow (2 * r_sel) σ))).toReal =
          Real.rpow r_sel (2 * τ) / (K * Real.rpow (2 * r_sel) σ) := by
        rw [ENNReal.toReal_ofReal h_pos_expr]
      rw [h3, h4] at h2
      have h5 : Real.rpow r_sel (2 * τ) / (K * Real.rpow (2 * r_sel) σ) =
          Real.rpow r_sel (2 * τ - σ) / (K * (2 : ℝ)^σ) := by
        rw [h_rpow_div]
        have h6 : Real.rpow r_sel ((2 * τ - σ) + σ) = Real.rpow r_sel (2 * τ - σ) * Real.rpow r_sel σ :=
          Real.rpow_add hr_sel_pos (2 * τ - σ) σ
        have h7 : (2 * τ - σ) + σ = 2 * τ := by ring
        rw [h7] at h6
        have h8 : Real.rpow r_sel (2 * τ) = Real.rpow r_sel (2 * τ - σ) * Real.rpow r_sel σ := h6
        have h_rpow_sig_pos : 0 < Real.rpow r_sel σ := Real.rpow_pos_of_pos hr_sel_pos σ
        rw [h8]
        field_simp [hK_pos.ne', h_rpow_sig_pos.ne'] <;> ring
      rw [h5] at h2
      exact h2
    have h_card_sum : T_conc.card + S_non.card = S.card := by
      have h_union : T_conc ∪ S_non = S := by
        ext ℓ; simp only [T_conc, S_non, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter] <;> tauto
      have h_disj2 : Disjoint T_conc S_non := by
        rw [Finset.disjoint_left]; intro ℓ h1 h2; exact (Finset.mem_sdiff.mp h2).2 h1
      rw [← Finset.card_union_of_disjoint h_disj2, h_union]
    have h_card_dichotomy : 2 * T_conc.card ≥ S.card ∨ 2 * S_non.card ≥ S.card := by
      have h : T_conc.card + S_non.card = S.card := h_card_sum
      by_cases h' : T_conc.card ≥ S_non.card
      · have h_goal : 2 * T_conc.card ≥ S.card := by
          linarith
        exact Or.inl h_goal
      · have h'' : S_non.card > T_conc.card := by omega
        have h_goal : 2 * S_non.card ≥ S.card := by linarith
        exact Or.inr h_goal
    cases h_card_dichotomy with
    | inl h_card_conc =>
      left
      refine' ⟨hx, T_x, S, T_conc, Y_x, hYx_meas, h_lines, hY_G, hY_sub, hY_mass, h_bounds,
        hS_sub, hS_sep', hT_conc_sub, h_conc_prop, hS_nonempty, h_card_conc, hS_card_lower_real⟩
    | inr h_card_non =>
      right
      refine' ⟨hx, T_x, S, S_non, Y_x, hYx_meas, h_lines, hY_G, hY_sub, hY_mass, h_bounds,
        hS_sub, hS_sep', hS_non_sub, h_non_prop, hS_nonempty, h_card_non, hS_card_lower_real⟩
  have hX_split : (ν₁ : Measure Point) X_conc ≥ ENNReal.ofReal (Real.rpow r_sel τ / 2) ∨
      (ν₁ : Measure Point) X_nonconc ≥ ENNReal.ofReal (Real.rpow r_sel τ / 2) := by
    have h1 : (ν₁ : Measure Point) X ≤ (ν₁ : Measure Point) (X_conc ∪ X_nonconc) :=
      measure_mono h_partition
    have h2 : (ν₁ : Measure Point) (X_conc ∪ X_nonconc) ≤
        (ν₁ : Measure Point) X_conc + (ν₁ : Measure Point) X_nonconc :=
      measure_union_le _ _
    have h3 : (ν₁ : Measure Point) X ≥ ENNReal.ofReal (Real.rpow r_sel τ) := hX_measure
    have h4 : ENNReal.ofReal (Real.rpow r_sel τ) ≤
        (ν₁ : Measure Point) X_conc + (ν₁ : Measure Point) X_nonconc :=
      le_trans h3 (le_trans h1 h2)
    by_contra h5
    push Not at h5
    rcases h5 with ⟨h51, h52⟩
    have h6 : (ν₁ : Measure Point) X_conc + (ν₁ : Measure Point) X_nonconc <
        ENNReal.ofReal (Real.rpow r_sel τ / 2) + ENNReal.ofReal (Real.rpow r_sel τ / 2) :=
      ENNReal.add_lt_add h51 h52
    have hpos : 0 ≤ Real.rpow r_sel τ / 2 := by
      have h : 0 ≤ Real.rpow r_sel τ := Real.rpow_nonneg hr_sel_pos.le τ
      linarith
    have h7 : ENNReal.ofReal (Real.rpow r_sel τ / 2) + ENNReal.ofReal (Real.rpow r_sel τ / 2) =
        ENNReal.ofReal (Real.rpow r_sel τ) := by
      have h_sum : Real.rpow r_sel τ / 2 + Real.rpow r_sel τ / 2 = Real.rpow r_sel τ := by ring
      rw [← ENNReal.ofReal_add hpos hpos, h_sum]
    rw [h7] at h6
    exact not_le.mpr h6 h4

  -- Step 13: Case split
  cases hX_split with
  | inl hX_conc_meas =>
    have hG_subset : G ⊆ (ν₁ : Measure Point).support ×ˢ (ν₂ : Measure Point).support := by
      intro p hp
      have h1 : p ∈ E₁ := hp.1
      exact hE₁_sub h1
    have hX_conc_subset : X_conc ⊆ (ν₁ : Measure Point).support := by
      have h1 : X_conc ⊆ X := by
        intro x hx
        exact hx.1
      exact Set.Subset.trans h1 h_X_sub_support
    -- Get concentrated parameters for r_sel
    have h_conc_sel := h_conc_r0 r_sel hr_sel_pos hr_sel_le
    have hr_sel_le_18 : r_sel ≤ 1 / 8 := h_conc_sel.1
    rcases h_conc_sel.2 with ⟨N_conc, hN_conc_pos, hR_conc, h_log_absorb, h_param, h_param_strengthened, h_card_strong, h_count_small, h_r_log_small, h_r_final, h_inner_cond⟩

    -- Prove hσ3τ_gt_κ from hτ_small2
    have hσ3τ_gt_κ : σ + 3 * τ > κ := by
      rw [hκ]
      have h1 : 0 < 1 - σ := by linarith [hσ.2, hε]
      have h2 : (σ + 3 * τ) * (1 - σ) > 14 * τ := by
        have h3 : σ * (1 - σ) > τ * (11 + 3 * σ) := by
          have h4 : τ < σ * (1 - σ) / (11 + 3 * σ) := hτ_small2
          have h5 : 0 < 11 + 3 * σ := by linarith [hσ.1, hβ]
          have h6 : τ * (11 + 3 * σ) < σ * (1 - σ) := by
            calc τ * (11 + 3 * σ)
              < (σ * (1 - σ) / (11 + 3 * σ)) * (11 + 3 * σ) := by gcongr
            _ = σ * (1 - σ) := by
              field_simp [h5.ne'] <;> ring
          linarith
        have h4 : (σ + 3 * τ) * (1 - σ) = σ * (1 - σ) + 3 * τ * (1 - σ) := by ring
        rw [h4]
        have h5 : σ * (1 - σ) + 3 * τ * (1 - σ) > τ * (11 + 3 * σ) + 3 * τ * (1 - σ) := by linarith
        have h6 : τ * (11 + 3 * σ) + 3 * τ * (1 - σ) = 14 * τ := by ring
        rw [h6] at h5
        exact h5
      have h4 : σ + 3 * τ > (14 * τ) / (1 - σ) := by
        calc σ + 3 * τ
          = ((σ + 3 * τ) * (1 - σ)) / (1 - σ) := by field_simp [h1.ne'] <;> ring
        _ > (14 * τ) / (1 - σ) := by gcongr
      simpa using h4

    -- Distance bounds are automatic from bounded support + mutual distance
    have hν1_ne_zero : (ν₁ : Measure Point) ≠ 0 := by
      intro h
      have h_univ : (ν₁ : Measure Point) Set.univ = 0 := by rw [h] <;> simp
      have h_univ1 : (ν₁ : Measure Point) Set.univ = 1 := measure_univ
      rw [h_univ1] at h_univ <;> norm_num at h_univ
    have hν2_ne_zero : (ν₂ : Measure Point) ≠ 0 := by
      intro h
      have h_univ : (ν₂ : Measure Point) Set.univ = 0 := by rw [h] <;> simp
      have h_univ1 : (ν₂ : Measure Point) Set.univ = 1 := measure_univ
      rw [h_univ1] at h_univ <;> norm_num at h_univ
    have h_supp_nonempty1 : (ν₁ : Measure Point).support.Nonempty :=
      Measure.nonempty_support_iff.mpr hν1_ne_zero
    have h_supp_nonempty2 : (ν₂ : Measure Point).support.Nonempty :=
      Measure.nonempty_support_iff.mpr hν2_ne_zero
    have h_dist_set_nonempty : Set.Nonempty {d : ℝ | ∃ x ∈ (ν₁ : Measure Point).support,
        ∃ y ∈ (ν₂ : Measure Point).support, dist x y = d} := by
      rcases h_supp_nonempty1 with ⟨x, hx⟩
      rcases h_supp_nonempty2 with ⟨y, hy⟩
      exact ⟨dist x y, x, hx, y, hy, rfl⟩
    have h_dist_lower : ∀ (x : Point), x ∈ (ν₁ : Measure Point).support →
        ∀ (y : Point), y ∈ (ν₂ : Measure Point).support → 1 / 2 ≤ dist x y := by
      intro x hx y hy
      let S : Set ℝ := {d | ∃ x ∈ (ν₁ : Measure Point).support,
          ∃ y ∈ (ν₂ : Measure Point).support, dist x y = d}
      have h_bdd : BddBelow S := by
        refine' ⟨0, _⟩
        intro d hd
        rcases hd with ⟨x, _, y, _, rfl⟩
        exact dist_nonneg
      have h_in : dist x y ∈ S := ⟨x, hx, y, hy, rfl⟩
      have h1 : sInf S ≤ dist x y := csInf_le h_bdd h_in
      have h2 : (1 / 2 : ℝ) ≤ sInf S := h_dist
      linarith
    have h_dist_upper : ∀ (x : Point), x ∈ (ν₁ : Measure Point).support →
        ∀ (y : Point), y ∈ (ν₂ : Measure Point).support → dist x y ≤ 2 := by
      intro x hx y hy
      have hx1 : dist x 0 ≤ 1 := h_supp1 hx
      have hy1 : dist y 0 ≤ 1 := h_supp2 hy
      calc dist x y ≤ dist x 0 + dist 0 y := dist_triangle x 0 y
           _ = dist x 0 + dist y 0 := by rw [dist_comm y 0]
           _ ≤ 1 + 1 := by gcongr <;> linarith
           _ = 2 := by norm_num

    let R_low : ℝ := 1 / 2
    let R_high : ℝ := 2

    -- Build X_conc property with distance bounds and direction-separated concentrated family
    have hX_conc_prop' : ∀ x ∈ X_conc,
        ∃ (T_x S T_conc : Finset (AffineSubspace ℝ Point)) (Y_x : Set Point),
          MeasurableSet Y_x ∧
          (∀ ℓ ∈ T_x, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1) ∧
          Y_x ⊆ {b₂ | (x, b₂) ∈ G} ∧
          Y_x ⊆ ⋃ ℓ ∈ T_x, tubeLine r_sel ℓ ∧
          (∀ y ∈ Y_x, (1 / 2 : ℝ) ≤ dist x y ∧ dist x y ≤ (2 : ℝ)) ∧
          ν₂ Y_x ≥ ENNReal.ofReal (Real.rpow r_sel (2 * τ)) ∧
          (∀ ℓ ∈ T_x,
            ENNReal.ofReal (Real.rpow r_sel (σ + 3 * τ)) ≤ ν₂ (tubeLine r_sel ℓ ∩ Y_x) ∧
            ν₂ (tubeLine r_sel ℓ ∩ Y_x) ≤ ENNReal.ofReal (Real.rpow r_sel (σ - τ))) ∧
          S ⊆ T_x ∧
          (∀ ℓ1 ∈ S, ∀ ℓ2 ∈ S, ℓ1 ≠ ℓ2 →
            submoduleDirDist ℓ1.direction ℓ2.direction ≥ r_sel / (4 * R_high)) ∧
          T_conc ⊆ S ∧
          (∀ ℓ ∈ T_conc, IsConcentrated (ν₂ : Measure Point) Y_x (tubeLine r_sel ℓ) r_sel κ) ∧
          2 * T_conc.card ≥ S.card ∧
          (S.card : ℝ) ≥ Real.rpow r_sel (2 * τ - σ) / (K * (2 : ℝ)^σ) := by
      intro x hx
      have h_x_in : x ∈ X_conc := hx
      rcases hx.2 with ⟨T_x, S, T_conc, Y_x, hYx_meas, h_lines, hY_G, hY_sub, hY_mass, h_bounds,
        hS_sub, hS_sep, hT_conc_sub, h_conc_prop, hS_nonempty, h_card_conc, hS_card_lower_real⟩
      have hY_supp : Y_x ⊆ (ν₂ : Measure Point).support := by
        intro b₂ hb₂
        have hG : (x, b₂) ∈ G := hY_G hb₂
        exact (hG_subset hG).2
      have h_x_supp : x ∈ (ν₁ : Measure Point).support := hX_conc_subset h_x_in
      have h_dist_bounds : ∀ y ∈ Y_x, (1 / 2 : ℝ) ≤ dist x y ∧ dist x y ≤ 2 := by
        intro y hy
        have h_y_supp : y ∈ (ν₂ : Measure Point).support := hY_supp hy
        exact ⟨h_dist_lower x h_x_supp y h_y_supp, h_dist_upper x h_x_supp y h_y_supp⟩
      exact ⟨T_x, S, T_conc, Y_x, hYx_meas, h_lines, hY_G, hY_sub, h_dist_bounds, hY_mass, h_bounds,
        hS_sub, hS_sep, hT_conc_sub, h_conc_prop, h_card_conc, hS_card_lower_real⟩

    have hσ_lt_one' : σ < 1 := by
      have h1 : σ ≤ 1 - ε := hσ.2
      have h2 : 1 - ε < 1 := by linarith [hε]
      linarith

    have hR_low_pos : 0 < R_low := by norm_num
    have hR_high_pos : 0 < R_high := by norm_num
    have hR_le : R_low ≤ R_high := by norm_num
    have hr_tube_small : r_sel ≤ R_low / 4 := by
      dsimp only [R_low]
      have h_eq : (1 / 2 : ℝ) / 4 = 1 / 8 := by norm_num
      rw [h_eq]
      exact hr_sel_le_18
    have h_rκ_le_R : Real.rpow r_sel κ ≤ R_high := by
      dsimp only [R_high]
      have h1 : Real.rpow r_sel κ ≤ 1 := Real.rpow_le_one hr_sel_pos.le hr_sel_small.le (by positivity)
      linarith
    have h_param' : Real.rpow r_sel τ * (((Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) : ℝ) + 1)) * K * (2 : ℝ)^σ ≤ 396 := by
      have h_coe : (((Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) + 1 : ℕ) : ℝ)) =
          ((Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) : ℝ) + 1) := by
        simp
      rw [h_coe] at h_param
      exact h_param

    have h_param_strengthened' : Real.rpow r_sel τ * (((Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) : ℝ) + 1)) * K * (2 : ℝ)^σ ≤ 66 := by
      have h_coe : (((Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) + 1 : ℕ) : ℝ)) =
          ((Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) : ℝ) + 1) := by simp
      rw [h_coe] at h_param_strengthened
      exact h_param_strengthened

    exact concentrated_case_contradiction_G ν₁ ν₂ G K K'' C σ τ r_sel c κ
      (by linarith [hσ_pos]) hσ_lt_one' hτ hr_sel_pos hr_sel_small
      hκ hκ_lt_one hC hK hc.1
      hν₂_growth hν₁_growth
      hG_forward hG_reverse
      hG_meas hG_subset h_dist
      h_supp1 h_supp2
      R_low R_high
      hR_low_pos hR_high_pos hR_le
      hr_tube_small h_rκ_le_R
      N_conc hN_conc_pos hR_conc h_log_absorb h_param_strengthened'
      h_card_strong h_count_small hσ3τ_gt_κ
      h_r_log_small h_r_final h_inner_cond
      X_conc hX_conc_subset hX_conc_meas hX_conc_prop'
  | inr hX_nonconc_meas =>
    have hσ_lt_one' : σ < 1 := by
      have h1 : σ ≤ 1 - ε := hσ.2
      have h2 : 1 - ε < 1 := by linarith [hε]
      linarith
    -- Derive scale conditions for r_sel from h_scale_r0
    have h_scale_sel := h_scale_r0 r_sel hr_sel_pos hr_sel_le
    have hr_small3 := h_scale_sel.1
    have hr_mass := h_scale_sel.2.1
    have hr_width2 := h_scale_sel.2.2.1
    have hr_small4 := h_scale_sel.2.2.2
    have hεF_large : 8 * τ + 2 * κ < ε_F := by linarith [hεF_large3]
    have hδ_le : 2 * r_sel ≤ δ₀ := by
      have h : 2 * r_sel ≤ 2 * r0 := by gcongr
      exact le_trans h hδ_le_r0
    have hr2_small : 2 * r_sel < 1 := by
      have h1 : 2 * r_sel ≤ (Real.sqrt 3 / 2) * Real.rpow r_sel κ := hr_width2
      have h2 : Real.rpow r_sel κ < 1 := Real.rpow_lt_one hr_sel_pos.le hr_sel_small hκ_pos
      have h4 : Real.sqrt 3 / 2 < 1 := by
        have h5 : Real.sqrt 3 < 2 := by
          rw [Real.sqrt_lt] <;> norm_num
        linarith
      have h3 : (Real.sqrt 3 / 2) * Real.rpow r_sel κ < 1 := by
        calc (Real.sqrt 3 / 2) * Real.rpow r_sel κ
          < (Real.sqrt 3 / 2) * 1 := by gcongr <;> linarith
        _ = Real.sqrt 3 / 2 := by ring
        _ < 1 := h4
      linarith
    -- Derive C_X bound for r_sel from r0 bound (monotone)
    have hC_X_bound : C_X_const * (Point_exists_doubling.choose : ℝ) ≤ Real.rpow (2 * r_sel) (-ε_F) := by
      have h1 : C_X_const * (Point_exists_doubling.choose : ℝ) ≤ Real.rpow (2 * r0) (-ε_F) := hC_X_bound_r0
      have h2r_sel_pos : 0 < 2 * r_sel := by positivity
      have h2r0_pos : 0 < 2 * r0 := by positivity
      have h2r_sel_le : 2 * r_sel ≤ 2 * r0 := by gcongr
      have h_neg : -ε_F < 0 := by linarith [hε_F_pos]
      have h_strict_anti : StrictAntiOn (fun x : ℝ => x ^ (-ε_F)) (Set.Ioi 0) :=
        Real.strictAntiOn_rpow_Ioi_of_exponent_neg h_neg
      have h2 : Real.rpow (2 * r0) (-ε_F) ≤ Real.rpow (2 * r_sel) (-ε_F) := by
        by_cases h : 2 * r_sel < 2 * r0
        · have h_strict : Real.rpow (2 * r0) (-ε_F) < Real.rpow (2 * r_sel) (-ε_F) :=
            h_strict_anti (Set.mem_Ioi.mpr h2r_sel_pos) (Set.mem_Ioi.mpr h2r0_pos) h
          exact h_strict.le
        · have h' : 2 * r_sel = 2 * r0 := by linarith
          rw [h']
      exact le_trans h1 h2
    -- P extraction: use extract_nonconc_delta_set
    have hX_nonconc_ball : X_nonconc ⊆ closedBall (0 : Point) 1 := by
      have h1 : X_nonconc ⊆ X := by
        intro x hx
        exact hx.1
      have h2 : X ⊆ (ν₁ : Measure Point).support := h_X_sub_support
      exact Set.Subset.trans (Set.Subset.trans h1 h2) h_supp1
    have hC_X_bound_goal :
        let m := Real.rpow r_sel τ / 2
        let L := max 0 (Real.log (2000 * C / (m * r_sel))) + 1
        let C_X := 100 * C * L / m
        C_X * (Point_exists_doubling.choose : ℝ) ≤ Real.rpow (2 * r_sel) (-ε_F) :=
      hC_X_extraction_bound r_sel hr_sel_pos hr_sel_le
    have hν_frostman : ∀ (x : Point) (ρ : ℝ), 0 < ρ →
        (ν₁ : Measure Point) (Metric.ball x ρ) ≤ ENNReal.ofReal (C * ρ) := by
      intro x ρ hρ
      have hpos : 0 ≤ C * ρ := by positivity
      have h_nnreal : ν₁ (Metric.ball x ρ) ≤ Real.toNNReal (C * ρ) := hν₁_growth x ρ hρ
      have h_coe : (ν₁ : Measure Point) (Metric.ball x ρ) = ↑(ν₁ (Metric.ball x ρ)) :=
        (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₁ (Metric.ball x ρ)).symm
      rw [h_coe]
      have h_ennreal : (↑(ν₁ (Metric.ball x ρ)) : ENNReal) ≤ ↑(Real.toNNReal (C * ρ)) :=
        ENNReal.coe_le_coe.mpr h_nnreal
      have h6 : (↑(Real.toNNReal (C * ρ)) : ENNReal) = ENNReal.ofReal (C * ρ) := by
        have h7 : 0 ≤ C * ρ := hpos
        simp [ENNReal.ofReal, Real.toNNReal_of_nonneg h7]
        <;> norm_cast
      rw [h6] at h_ennreal
      exact h_ennreal
    rcases extract_nonconc_delta_set X_nonconc hX_nonconc_ball
        r_sel τ C ε_F hr_sel_pos hr_sel_small hτ (by linarith [hC]) hε_F_pos
        hX_nonconc_meas hν_frostman hC_X_bound_goal
      with ⟨P, C_X, hC_X_nonneg, hP_sub, hP_nonempty, hP_finite, hP_ball, hP_delta, hC_X_bound'⟩
    -- Step B data: multi-tube wrapper using direction-separated S_non
    have h_step_B_data : ∀ (x : Point), x ∈ P →
        ∃ (S_x : Finset Line2) (A_x : Line2 → Set Point) (C_B : ℝ) (hC_B : 0 ≤ C_B),
          S_x.Nonempty ∧
          (∀ L ∈ S_x, L ∈ (tubeFamily r_sel : Set Line2) ∧ x ∈ tube (2 * r_sel) L) ∧
          IsDeltaSet r_sel σ C_B hr_sel_pos hσ_pos.le hC_B (S_x : Set Line2) ∧
          C_B * (Line2_exists_doubling.choose : ℝ) ≤ Real.rpow (2 * r_sel) (-ε_F) ∧
          (∀ L ∈ S_x, MeasurableSet (A_x L) ∧ A_x L ⊆ tube (2 * r_sel) L ∧
            (ν₂ : Measure Point) (A_x L) ≥ ENNReal.ofReal (Real.rpow r_sel (σ + 3 * τ)) ∧
            (∀ (z : Point), (ν₂ : Measure Point) (A_x L ∩ Metric.ball z (Real.rpow r_sel κ)) ≤
              (ν₂ : Measure Point) (A_x L) / 3)) := by
      intro x hx
      have hx_P : x ∈ P := hx
      have hx_X : x ∈ X_nonconc := hP_sub hx_P
      rcases hx_X.2 with ⟨T_x, S, S_non, Y_x, hYx_meas, h_lines, hY_G, hY_sub, hY_mass, h_bounds,
        hS_sub, hS_sep, hS_non_sub, h_non_prop, hS_nonempty, h_card_non, hS_card_lower⟩
      have hS_nonempty' : S_non.Nonempty := by
        have h1 : 0 < S.card := Finset.card_pos.mpr hS_nonempty
        have h2 : 0 < S_non.card := by
          by_contra h3
          have h4 : S_non.card = 0 := by omega
          rw [h4] at h_card_non
          omega
        exact Finset.card_pos.mp h2
      have hx_ball : x ∈ closedBall (0 : Point) 1 := hP_ball hx_P
      have hY_sub1 : Y_x ⊆ closedBall (0 : Point) 1 := by
        intro y hy
        have h_y_supp : y ∈ (ν₂ : Measure Point).support := by
          have hG : (x, y) ∈ G := hY_G hy
          have hG_subset : G ⊆ (ν₁ : Measure Point).support ×ˢ (ν₂ : Measure Point).support := by
            intro p hp; have h1 : p ∈ E₁ := hp.1; exact hE₁_sub h1
          exact (hG_subset hG).2
        exact h_supp2 h_y_supp
      let h_finrank_all : ∀ ℓ ∈ S_non, Module.finrank ℝ ℓ.direction = 1 :=
        fun ℓ hℓ => (h_lines ℓ (hS_sub (hS_non_sub hℓ))).2
      let S_non_L2 : Finset Line2 := finsetAffineToLine2 S_non h_finrank_all
      have hS_non_L2_nonempty : S_non_L2.Nonempty := by
        have h_pos : 0 < S_non.card := Finset.card_pos.mpr hS_nonempty'
        have h : S_non_L2.card = S_non.card := finsetAffineToLine2_card S_non h_finrank_all
        have h2 : 0 < S_non_L2.card := by rw [h]; exact h_pos
        exact Finset.card_pos.mp h2
      have hS_non_card : (S_non_L2.card : ℝ) ≥
          Real.rpow r_sel (2 * τ - σ) / (2 * K * (2 : ℝ)^σ) := by
        have h1 : (S_non_L2.card : ℝ) = (S_non.card : ℝ) := by
          exact_mod_cast finsetAffineToLine2_card S_non h_finrank_all
        rw [h1]
        have h2 : (2 : ℝ) * (S_non.card : ℝ) ≥ (S.card : ℝ) := by exact_mod_cast h_card_non
        have h4 : (S.card : ℝ) ≥ Real.rpow r_sel (2 * τ - σ) / (K * (2 : ℝ)^σ) := hS_card_lower
        have h5 : (S_non.card : ℝ) ≥ Real.rpow r_sel (2 * τ - σ) / (2 * K * (2 : ℝ)^σ) := by
          calc (S_non.card : ℝ)
            ≥ (S.card : ℝ) / 2 := by linarith
          _ ≥ (Real.rpow r_sel (2 * τ - σ) / (K * (2 : ℝ)^σ)) / 2 := by gcongr
          _ = Real.rpow r_sel (2 * τ - σ) / (2 * K * (2 : ℝ)^σ) := by ring
        exact h5
      have h_mass_lower : ∀ (L : Line2), L ∈ S_non_L2 →
          ENNReal.ofReal (Real.rpow r_sel (σ + 3 * τ)) ≤
          (ν₂ : Measure Point) (tubeLine r_sel L.toAffine ∩ Y_x) := by
        intro L hL
        rcases Finset.mem_image.mp hL with ⟨⟨ℓ, hℓ⟩, _, rfl⟩
        simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, Line2.ofAffine_toAffine]
          using (h_bounds ℓ (hS_sub (hS_non_sub hℓ))).1
      have h_mass_upper : ∀ (L : Line2), L ∈ S_non_L2 →
          (ν₂ : Measure Point) (tubeLine r_sel L.toAffine ∩ Y_x) ≤
          ENNReal.ofReal (Real.rpow r_sel (σ - τ)) := by
        intro L hL
        rcases Finset.mem_image.mp hL with ⟨⟨ℓ, hℓ⟩, _, rfl⟩
        simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, Line2.ofAffine_toAffine]
          using (h_bounds ℓ (hS_sub (hS_non_sub hℓ))).2
      have h_nonconc_L2 : ∀ (L : Line2), L ∈ S_non_L2 →
          IsNonConcentrated (ν₂ : Measure Point) Y_x (tubeLine r_sel L.toAffine) r_sel κ := by
        intro L hL
        rcases Finset.mem_image.mp hL with ⟨⟨ℓ, hℓ⟩, _, rfl⟩
        simpa [Line2.ofAffine_toAffine] using h_non_prop ℓ hℓ
      have h_thin' : ∀ (l : AffineSubspace ℝ Point), x ∈ (l : Set Point) →
          Module.finrank ℝ l.direction = 1 → ∀ ρ : ℝ, 0 < ρ →
            (ν₂ : Measure Point) (tubeLine ρ l ∩ Y_x) ≤ ENNReal.ofReal (K * Real.rpow ρ σ) := by
        intro l hxl hfin ρ hρ
        let S_G := {b₂ : Point | b₂ ∈ tubeLine ρ l ∧ (x, b₂) ∈ G}
        have h_sub : tubeLine ρ l ∩ Y_x ⊆ S_G := by
          intro b₂ hb₂
          exact ⟨hb₂.1, hY_G hb₂.2⟩
        have h1 : (ν₂ : Measure Point) (tubeLine ρ l ∩ Y_x) ≤ (ν₂ : Measure Point) S_G :=
          measure_mono h_sub
        have h_x_supp : x ∈ (ν₁ : Measure Point).support := by
          have h1 : x ∈ X_nonconc := hx_X
          have h2 : X_nonconc ⊆ X := by intro y hy; exact hy.1
          exact h_X_sub_support (h2 h1)
        have h_eq : (ν₂ : Measure Point) S_G = ↑(ν₂ S_G) := by exact Eq.symm (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₂ S_G)
        have h2 : (ν₂ : Measure Point) S_G ≤ ENNReal.ofReal (K * Real.rpow ρ σ) := by
          rw [h_eq]
          exact hG_forward x h_x_supp l hxl hfin ρ hρ
        exact le_trans h1 h2
      let D_T : ℕ := Line2_exists_doubling.choose
      have hD_T_pos : 0 < D_T := Line2_exists_doubling.choose_spec.1
      have h_double_T : ∀ (L : Line2) (ε : ℝ), 0 < ε →
          ∃ (S : Finset Line2), Metric.closedBall L (2 * ε) ⊆ ⋃ M ∈ S, Metric.closedBall M ε ∧ S.card ≤ D_T :=
        Line2_exists_doubling.choose_spec.2
      have h_x_on_line : ∀ (L : Line2), L ∈ S_non_L2 → x ∈ tube r_sel L := by
        intro L hL
        rcases Finset.mem_image.mp hL with ⟨⟨ℓ, hℓ⟩, _, h_eq⟩
        have hxl : x ∈ (ℓ : Set Point) := (h_lines ℓ (hS_sub (hS_non_sub hℓ))).1
        have hthick : x ∈ Metric.thickening r_sel (ℓ : Set Point) := by
          simp only [Metric.mem_thickening_iff]
          exact ⟨x, hxl, by rw [dist_self]; linarith [hr_sel_pos]⟩
        have h_tube : x ∈ tube r_sel (Line2.ofAffine ℓ (h_finrank_all ℓ hℓ)) :=
          finsetAffineToLine2_tube r_sel S_non h_finrank_all ℓ hℓ x hthick
        rw [← h_eq]
        exact h_tube
      let gm : Line2 → Line2 := fun L =>
        if h : L ∈ S_non_L2 then
          gridMap r_sel hr_sel_pos (by linarith) x hx_ball L (h_x_on_line L h)
        else L
      have hgm_def : ∀ (L : Line2) (hL : L ∈ S_non_L2),
          gm L = gridMap r_sel hr_sel_pos (by linarith) x hx_ball L (h_x_on_line L hL) := by
        intro L hL
        dsimp only [gm]
        rw [dif_pos hL]
      have hGridMap_mem : ∀ L ∈ S_non_L2, gm L ∈ tubeFamily r_sel := by
        intro L hL
        rw [hgm_def L hL]
        exact gridMap_mem r_sel hr_sel_pos (by linarith) x hx_ball L (h_x_on_line L hL)
      have hGridMap_2r : ∀ L ∈ S_non_L2, x ∈ tube (2 * r_sel) (gm L) := by
        intro L hL
        rw [hgm_def L hL]
        exact gridMap_2r r_sel hr_sel_pos (by linarith) x hx_ball L (h_x_on_line L hL)
      have hGridMap_contain : ∀ L ∈ S_non_L2,
          tube r_sel L ∩ closedBall (0 : Point) 1 ⊆ tube (2 * r_sel) (gm L) := by
        intro L hL
        rw [hgm_def L hL]
        exact gridMap_containment r_sel hr_sel_pos (by linarith) x hx_ball L (h_x_on_line L hL)
      have hS_non_sep : ∀ ℓ1 ∈ S_non, ∀ ℓ2 ∈ S_non, ℓ1 ≠ ℓ2 →
          submoduleDirDist ℓ1.direction ℓ2.direction ≥ r_sel / 8 := by
        intro ℓ1 hℓ1 ℓ2 hℓ2 hne
        have h1 : ℓ1 ∈ S := hS_non_sub hℓ1
        have h2 : ℓ2 ∈ S := hS_non_sub hℓ2
        have h_sep : submoduleDirDist ℓ1.direction ℓ2.direction ≥ r_sel / (4 * (2 : ℝ)) :=
          hS_sep ℓ1 h1 ℓ2 h2 hne
        have h_eq : r_sel / (4 * (2 : ℝ)) = r_sel / 8 := by ring
        rw [h_eq] at h_sep
        exact h_sep
      have h_dir_sep : ∀ (L1 L2 : Line2), L1 ∈ S_non_L2 → L2 ∈ S_non_L2 → L1 ≠ L2 →
          r_sel / 8 ≤ lineDirDist L1 L2 := by
        intro L1 L2 hL1 hL2 hne
        have h : lineDirDist L1 L2 ≥ r_sel / 8 :=
          finsetAffineToLine2_sep r_sel 8 S_non h_finrank_all hS_non_sep L1 hL1 L2 hL2 hne
        exact h
      have hGridMap_inj : Set.InjOn gm (S_non_L2 : Set Line2) := by
        intro L1 hL1 L2 hL2 h_eq
        by_cases h : L1 = L2
        · exact h
        · exfalso
          have h_sep : r_sel / 8 ≤ lineDirDist L1 L2 := h_dir_sep L1 L2 hL1 hL2 h
          have hif1 : gm L1 = gridMap r_sel hr_sel_pos (by linarith) x hx_ball L1 (h_x_on_line L1 hL1) :=
            hgm_def L1 hL1
          have hif2 : gm L2 = gridMap r_sel hr_sel_pos (by linarith) x hx_ball L2 (h_x_on_line L2 hL2) :=
            hgm_def L2 hL2
          rw [hif1, hif2] at h_eq
          exact gridMap_injective r_sel hr_sel_pos (by linarith) x hx_ball L1 L2
            (h_x_on_line L1 hL1) (h_x_on_line L2 hL2) h_sep h_eq
      have hC_B_bound : (max (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 *
          Real.rpow r_sel (-(κ + 5 * τ))) 1) * (D_T : ℝ) ≤
          Real.rpow (2 * r_sel) (-ε_F) :=
        CBBound.C_B_bound_from_r0 hK hσ_pos hε_F_pos hεF_large3 hκ_pos hτ
          hr_sel_pos hr_sel_le hr_sel_small hD_T_pos hC_B_r0
      have hr_small4' : 4 * Real.rpow r_sel (1 - κ) ≤ 1 := by
        have h_rpow_div : Real.rpow r_sel (1 - κ) = r_sel / Real.rpow r_sel κ := by
          have h2 : Real.rpow r_sel (1 - κ) = Real.rpow r_sel 1 / Real.rpow r_sel κ :=
            Real.rpow_sub hr_sel_pos (1 : ℝ) κ
          have h3 : Real.rpow r_sel 1 = r_sel := by simp
          rw [h2, h3]
        have h_eq : 4 * r_sel / (Real.rpow r_sel κ / 4) = 16 * (r_sel / Real.rpow r_sel κ) := by ring
        rw [h_eq] at hr_small4
        rw [h_rpow_div] at * <;> linarith
      have hY_mass' : (ν₂ : Measure Point) Y_x ≥ ENNReal.ofReal (Real.rpow r_sel (2 * τ)) := by
        have h_eq : (ν₂ : Measure Point) Y_x = ↑(ν₂ Y_x) := by exact Eq.symm (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₂ Y_x)
        rw [h_eq]
        exact hY_mass
      exact multi_tube_step_B_from_Snon
        hr_sel_pos (by linarith) hr_sel_small (by linarith)
        hσ_pos hσ_lt_one' hτ hκ_pos hκ_lt_one
        hr_small4'
        hK x hx_ball
        S_non_L2 hS_non_L2_nonempty hS_non_card
        gm hGridMap_mem hGridMap_2r hGridMap_contain hGridMap_inj
        Y_x hYx_meas hY_sub1 hY_mass'
        h_mass_lower h_mass_upper h_nonconc_L2
        h_thin'
        D_T hD_T_pos h_double_T
        hC_B_bound
    have h_false : False := non_concentrated_case_contradiction_G ν₁ ν₂ G K K'' C σ τ r_sel c κ
      hσ_pos hσ_lt_one' hτ hr_sel_pos hr_sel_small
      hr2_small
      hκ hκ_lt_one hC hc.1
      hν₂_growth hν₁_growth
      hG_forward
      X_nonconc hX_nonconc_meas
      ε_F δ₀ hε_F_pos hδ₀_pos
      hF_estimate
      hεF_large3
      hδ_le
      hr_small3
      hr_mass
      hr_width2
      hr_small4
      P C_X hC_X_nonneg
      hP_sub hP_nonempty hP_finite
      hP_ball
      hP_delta
      hC_X_bound'
      h_step_B_data
    exact False.elim h_false

end B1
end RadialBootstrapping
