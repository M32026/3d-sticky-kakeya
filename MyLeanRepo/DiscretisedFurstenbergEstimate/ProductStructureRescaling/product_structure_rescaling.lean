module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.Basics
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.CoveringScaling
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.GridResidualScaling

@[expose] public section

/-!
# Product-structure rescaling inside one common thick tube

This is the geometric bridge in OS (A.48)--(A.53).  At the special relation
`δ = Δ²`, parameters of fine tubes lying in one `Δ`-parameter square are
dilated by `Δ⁻¹`.  The fine `δ`-grid becomes the coarse `Δ`-grid, incidence
errors become `O(Δ)`, and covering numbers are preserved up to an absolute
constant.

The theorem stops at parameter sets.  Replacing each `Δ`-grid parameter by its
canonical dyadic `Δ`-tube is a finite-to-one bookkeeping step.
-/

noncomputable section

open scoped ENNReal NNReal

theorem product_structure_rescaling
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∃ A : ℝ, A = 1 ∧
      ∀ {Δ δ C K_resid : ℝ}
        (Y : Set ℝ) (X : ℝ → Set ℝ)
        (fineParams : EuclideanPlane → Set EuclideanPlane)
        (allFine : Set EuclideanPlane),
        0 < Δ → Δ ≤ 1 → δ = Δ ^ (2 : ℕ) → 1 ≤ C → 0 < K_resid →
        (∀ z ∈ productIncidenceSet Y X,
          fineParams z ⊆ allFine ∧
          fineParams z ⊆ parameterGrid δ ∧
          IsRescalableDeltaSet δ Δ s C (fineParams z) ∧
          ∀ θ ∈ fineParams z,
            lineResidual (unscaleHorizontal Δ z) θ ≤ K_resid * δ) →
        ∃ coarseParams : EuclideanPlane → Set EuclideanPlane,
          (∀ z ∈ productIncidenceSet Y X,
            coarseParams z = scaleParameters Δ (fineParams z) ∧
            coarseParams z ⊆ parameterGrid Δ ∧
            IsDeltaSSet Δ s (A * C) (coarseParams z) ∧
            ∀ θ ∈ coarseParams z, lineResidual z θ ≤ K_resid * Δ) ∧
          Ncover Δ
              (⋃ z ∈ productIncidenceSet Y X, coarseParams z) ≤
            ENNReal.ofReal A * Ncover δ allFine := by
  use 1
  constructor
  · rfl
  intro Δ δ C K_resid Y X fineParams allFine hΔ hΔ1 hδ hC1 hK_pos h_main
  let coarseParams : EuclideanPlane → Set EuclideanPlane :=
    fun z => scaleParameters Δ (fineParams z)
  let S : Set EuclideanPlane := productIncidenceSet Y X
  let c : ℝ := Δ⁻¹
  have hc : 0 < c := by positivity
  have hδ_pos : 0 < δ := by
    rw [hδ]
    positivity
  have hC_pos : 0 < C := by linarith
  have hs_nonneg : 0 ≤ s := by linarith
  let K : NNReal := ⟨c, hc.le⟩

  -- Key NNReal equality: K * δ.toNNReal = Δ.toNNReal
  have hNNReal_eq : K * δ.toNNReal = Δ.toNNReal := by
    apply NNReal.coe_injective
    have hδ_nonneg : 0 ≤ δ := by linarith
    have hδ_toNNReal : (↑δ.toNNReal : ℝ) = δ := by
      simp [Real.toNNReal_of_nonneg hδ_nonneg]
    have hK_coe : (↑K : ℝ) = c := by exact_mod_cast rfl
    have h1 : (↑(K * δ.toNNReal) : ℝ) = c * δ := by
      calc (↑(K * δ.toNNReal) : ℝ)
        = (↑K : ℝ) * (↑δ.toNNReal : ℝ) := by exact_mod_cast rfl
      _ = c * (↑δ.toNNReal : ℝ) := by rw [hK_coe]
      _ = c * δ := by rw [hδ_toNNReal]
    rw [h1]
    have h2 : c * δ = Δ := by
      dsimp only [c]
      rw [hδ]
      field_simp [hΔ.ne'] <;> ring
    rw [h2]
    have h3 : (↑Δ.toNNReal : ℝ) = Δ := by
      simp [Real.toNNReal_of_nonneg hΔ.le]
    rw [h3]

  have h_pointwise : ∀ z ∈ S,
      coarseParams z = scaleParameters Δ (fineParams z) ∧
      coarseParams z ⊆ parameterGrid Δ ∧
      IsDeltaSSet Δ s (1 * C) (coarseParams z) ∧
      ∀ θ ∈ coarseParams z, lineResidual z θ ≤ K_resid * Δ := by
    intro z hz
    set P : Set EuclideanPlane := fineParams z with hP_def
    set Q : Set EuclideanPlane := coarseParams z with hQ_def
    have hQ_eq : Q = (fun p : EuclideanPlane ↦ c • p) '' P := by
      simp [hQ_def, coarseParams, scaleParameters, hP_def]
      <;> rfl
    rcases h_main z hz with ⟨hP_all, hP_grid, hP_resc, hP_resid⟩
    rcases hP_resc with ⟨hP_nonempty, _, _, hC_pos', hs_nonneg', hP_cover⟩

    -- 1. Q = scaleParameters Δ P
    have h1 : Q = scaleParameters Δ P := by
      simp [hQ_def, coarseParams, scaleParameters, hP_def]

    -- 2. Q ⊆ parameterGrid Δ
    have h2 : Q ⊆ parameterGrid Δ := by
      intro θ' hθ'
      rcases (Set.mem_image _ _ _).mp hθ' with ⟨θ, hθ, rfl⟩
      have hθ_grid : θ ∈ parameterGrid δ := hP_grid hθ
      exact grid_scaling hΔ hδ θ hθ_grid

    -- 3. IsDeltaSSet Δ s C Q
    have hQ_nonempty : Q.Nonempty := hP_nonempty.image _
    have h3_cover : ∀ (y : EuclideanPlane) (r : ℝ), Δ ≤ r →
        Ncover Δ (Q ∩ Metric.closedBall y r) ≤
          ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Ncover Δ Q := by
      intro y r hr
      have hr_pos : 0 < r := by linarith
      have hr_nonneg : 0 ≤ r := by linarith
      have hball_eq : Q ∩ Metric.closedBall y r =
          (fun x : EuclideanPlane ↦ c • x) ''
            (P ∩ Metric.closedBall (c⁻¹ • y) (r / c)) :=
        smul_closedBall_inter hc hr_nonneg
      have hcenter : c⁻¹ • y = (Δ : ℝ) • y := by
        have h4 : c⁻¹ = Δ := by
          dsimp only [c]
          field_simp [hΔ.ne'] <;> ring
        rw [h4]
      have hradius : r / c = Δ * r := by
        dsimp only [c]
        field_simp [hΔ.ne'] <;> ring
      rw [hball_eq, hcenter, hradius]
      have h4 : Ncover Δ ((fun x : EuclideanPlane ↦ c • x) ''
            (P ∩ Metric.closedBall ((Δ : ℝ) • y) (Δ * r))) =
          Ncover δ (P ∩ Metric.closedBall ((Δ : ℝ) • y) (Δ * r)) := by
        have h5 := externalCoveringNumber_smul (hc := hc) (ε := δ.toNNReal)
          (A := P ∩ Metric.closedBall ((Δ : ℝ) • y) (Δ * r))
        rw [hNNReal_eq] at h5
        dsimp only [Ncover]
        exact_mod_cast h5
      rw [h4]
      have h6 : Ncover δ (P ∩ Metric.closedBall ((Δ : ℝ) • y) (Δ * r)) ≤
          ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Ncover δ P :=
        hP_cover ((Δ : ℝ) • y) r hr
      have h7 : Ncover Δ Q = Ncover δ P := by
        have h8 := externalCoveringNumber_smul (hc := hc) (ε := δ.toNNReal) (A := P)
        rw [hNNReal_eq] at h8
        dsimp only [Ncover]
        exact_mod_cast h8
      rw [h7]
      exact h6
    have h3 : IsDeltaSSet Δ s C Q :=
      ⟨hQ_nonempty, hΔ, hC_pos, hs_nonneg, h3_cover⟩
    have h3' : IsDeltaSSet Δ s (1 * C) Q := by
      have h9 : (1 * C : ℝ) = C := by ring
      rw [h9]
      exact h3

    -- 4. Line residual bound
    have h4 : ∀ θ' ∈ Q, lineResidual z θ' ≤ K_resid * Δ := by
      intro θ' hθ'
      rcases (Set.mem_image _ _ _).mp hθ' with ⟨θ, hθ, rfl⟩
      have h : lineResidual (unscaleHorizontal Δ z) θ ≤ K_resid * δ := hP_resid θ hθ
      exact lineResidual_scaling_bound_general (K := K_resid) hΔ hδ h

    exact ⟨h1, h2, h3', h4⟩

  -- Global union bound
  have h_union_eq : (⋃ z ∈ S, coarseParams z) =
      (fun p : EuclideanPlane ↦ c • p) '' (⋃ z ∈ S, fineParams z) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨z, hz, hx⟩
      rcases hx with ⟨p, hp, rfl⟩
      exact ⟨p, ⟨z, hz, hp⟩, rfl⟩
    · rintro ⟨p, ⟨z, hz, hp⟩, rfl⟩
      exact ⟨z, hz, ⟨p, hp, rfl⟩⟩
  have h_subset : (⋃ z ∈ S, fineParams z) ⊆ allFine := by
    intro p hp
    simp only [Set.mem_iUnion] at hp
    rcases hp with ⟨z, hz, hpz⟩
    have h : fineParams z ⊆ allFine := (h_main z hz).1
    exact h hpz
  have h_image_subset : ((fun p : EuclideanPlane ↦ c • p) '' (⋃ z ∈ S, fineParams z)) ⊆
      (fun p : EuclideanPlane ↦ c • p) '' allFine := by
    intro x hx
    rcases (Set.mem_image _ _ _).mp hx with ⟨p, hp, rfl⟩
    exact ⟨p, h_subset hp, rfl⟩
  have h_union_subset : (⋃ z ∈ S, coarseParams z) ⊆
      (fun p : EuclideanPlane ↦ c • p) '' allFine := by
    rw [h_union_eq]
    exact h_image_subset
  have h_mono : Metric.externalCoveringNumber Δ.toNNReal (⋃ z ∈ S, coarseParams z) ≤
      Metric.externalCoveringNumber Δ.toNNReal ((fun p : EuclideanPlane ↦ c • p) '' allFine) :=
    Metric.externalCoveringNumber_mono_set h_union_subset
  have h_smul_eq : Metric.externalCoveringNumber Δ.toNNReal
        ((fun p : EuclideanPlane ↦ c • p) '' allFine) =
      Metric.externalCoveringNumber δ.toNNReal allFine := by
    have h9 := externalCoveringNumber_smul (hc := hc) (ε := δ.toNNReal) (A := allFine)
    rw [hNNReal_eq] at h9
    exact h9
  have h_mono' : Ncover Δ (⋃ z ∈ S, coarseParams z) ≤
      Ncover Δ ((fun p : EuclideanPlane ↦ c • p) '' allFine) := by
    dsimp only [Ncover]
    exact_mod_cast h_mono
  have h_smul_eq' : Ncover Δ ((fun p : EuclideanPlane ↦ c • p) '' allFine) =
      Ncover δ allFine := by
    dsimp only [Ncover]
    exact_mod_cast h_smul_eq
  have h_global : Ncover Δ (⋃ z ∈ S, coarseParams z) ≤ Ncover δ allFine := by
    calc Ncover Δ (⋃ z ∈ S, coarseParams z)
      ≤ Ncover Δ ((fun p : EuclideanPlane ↦ c • p) '' allFine) := h_mono'
    _ = Ncover δ allFine := h_smul_eq'
  have h_final : Ncover Δ (⋃ z ∈ S, coarseParams z) ≤
      ENNReal.ofReal (1 : ℝ) * Ncover δ allFine := by
    have h10 : ENNReal.ofReal (1 : ℝ) = 1 := by simp
    rw [h10]
    simpa using h_global

  refine' ⟨coarseParams, h_pointwise, h_final⟩

end
