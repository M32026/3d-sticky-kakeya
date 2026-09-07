module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.Basics

@[expose] public section

/-!
# Covering number scaling lemmas

This module proves two scaling facts for `Metric.externalCoveringNumber` used
in the product-structure rescaling theorem:

1. `externalCoveringNumber_smul`: covering numbers are invariant under positive
   scalar dilation in `EuclideanPlane`.
2. `smul_closedBall_inter`: the intersection of a dilated set with a closed ball
   equals the dilation of the intersection with a scaled ball.

Whiteprint node: `covering_scaling`.
-/

noncomputable section

open scoped ENNReal NNReal

section Lipschitz

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- External covering number of a Lipschitz image. -/
lemma externalCoveringNumber_image_lipschitz
    {f : X → Y} {K : NNReal} (hf : LipschitzWith K f)
    {ε : NNReal} {A : Set X} :
    Metric.externalCoveringNumber (K * ε) (f '' A) ≤
      Metric.externalCoveringNumber ε A := by
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  have h1 : Metric.IsCover (K * ε) (f '' A) (f '' C) := hC.image_lipschitz hf
  have h2 : Metric.externalCoveringNumber (K * ε) (f '' A) ≤ (f '' C).encard :=
    Metric.IsCover.externalCoveringNumber_le_encard h1
  have h3 : (f '' C).encard ≤ C.encard := Set.encard_image_le f C
  exact h2.trans h3

end Lipschitz

section Smul

variable {c : ℝ} (hc : 0 < c) {ε : NNReal} {A : Set EuclideanPlane}

/-- External covering number is invariant under positive scalar dilation. -/
lemma externalCoveringNumber_smul :
    Metric.externalCoveringNumber (⟨c, hc.le⟩ * ε)
      ((fun x : EuclideanPlane ↦ c • x) '' A) =
    Metric.externalCoveringNumber ε A := by
  set f : EuclideanPlane → EuclideanPlane := fun x ↦ c • x with hf_def
  set g : EuclideanPlane → EuclideanPlane := fun x ↦ c⁻¹ • x with hg_def
  set K : NNReal := ⟨c, hc.le⟩ with hK_def
  set Kinv : NNReal := ⟨c⁻¹, by positivity⟩ with hKinv_def

  have hf_dist : ∀ x y, dist (f x) (f y) = c * dist x y := by
    intro x y
    have h1 : f x - f y = c • (x - y) := by
      simp [hf_def, smul_sub] <;> abel
    calc dist (f x) (f y)
      = ‖f x - f y‖ := by rw [dist_eq_norm]
    _ = ‖c • (x - y)‖ := by rw [h1]
    _ = ‖c‖ * ‖x - y‖ := by rw [norm_smul]
    _ = |c| * ‖x - y‖ := by rw [Real.norm_eq_abs]
    _ = c * ‖x - y‖ := by rw [abs_of_pos hc]
    _ = c * dist x y := by rw [dist_eq_norm]

  have hg_dist : ∀ x y, dist (g x) (g y) = c⁻¹ * dist x y := by
    intro x y
    have h1 : g x - g y = c⁻¹ • (x - y) := by
      simp [hg_def, smul_sub] <;> abel
    calc dist (g x) (g y)
      = ‖g x - g y‖ := by rw [dist_eq_norm]
    _ = ‖c⁻¹ • (x - y)‖ := by rw [h1]
    _ = ‖c⁻¹‖ * ‖x - y‖ := by rw [norm_smul]
    _ = |c⁻¹| * ‖x - y‖ := by rw [Real.norm_eq_abs]
    _ = c⁻¹ * ‖x - y‖ := by rw [abs_of_pos (by positivity)]
    _ = c⁻¹ * dist x y := by rw [dist_eq_norm]

  have hf_lip : LipschitzWith K f :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [hf_dist x y]
      have hK : (↑K : ℝ) = c := by exact_mod_cast rfl
      rw [hK] <;> rfl

  have hg_lip : LipschitzWith Kinv g :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [hg_dist x y]
      have hKinv : (↑Kinv : ℝ) = c⁻¹ := by exact_mod_cast rfl
      rw [hKinv] <;> rfl

  have hgf : ∀ x, g (f x) = x := by
    intro x
    have h : g (f x) = c⁻¹ • (c • x) := by rfl
    rw [h, smul_smul]
    have h2 : c⁻¹ * c = 1 := by field_simp [hc.ne']
    rw [h2]
    simp

  have h1 : Metric.externalCoveringNumber (K * ε) (f '' A) ≤
      Metric.externalCoveringNumber ε A :=
    externalCoveringNumber_image_lipschitz (hf := hf_lip)

  have hg_image : g '' (f '' A) = A := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      have h4 : g (f x) = x := hgf x
      rw [h4]; exact hx
    · intro hz
      exact ⟨f z, ⟨z, hz, rfl⟩, hgf z⟩

  have hKinv_eq : Kinv * (K * ε) = ε := by
    apply NNReal.coe_injective
    have h_coe : (↑(Kinv * (K * ε)) : ℝ) = (↑Kinv : ℝ) * ((↑K : ℝ) * (↑ε : ℝ)) := by
      simp [mul_assoc] <;> ring
    rw [h_coe]
    have hK : (↑K : ℝ) = c := by exact_mod_cast rfl
    have hKinv : (↑Kinv : ℝ) = c⁻¹ := by exact_mod_cast rfl
    rw [hK, hKinv]
    have h3 : c⁻¹ * (c * (↑ε : ℝ)) = (↑ε : ℝ) := by
      field_simp [hc.ne'] <;> ring
    rw [h3]

  have h2 : Metric.externalCoveringNumber ε A ≤
      Metric.externalCoveringNumber (K * ε) (f '' A) := by
    have h3 : Metric.externalCoveringNumber (Kinv * (K * ε)) (g '' (f '' A)) ≤
        Metric.externalCoveringNumber (K * ε) (f '' A) :=
      externalCoveringNumber_image_lipschitz (hf := hg_lip)
    rw [hKinv_eq] at h3
    rw [hg_image] at h3
    exact h3

  exact le_antisymm h1 h2

/-- Intersection of a dilated set with a closed ball equals the dilation of
    the intersection with an appropriately scaled ball. -/
lemma smul_closedBall_inter
    {c : ℝ} (hc : 0 < c) {A : Set EuclideanPlane}
    {y : EuclideanPlane} {r : ℝ} (hr : 0 ≤ r) :
    ((fun x : EuclideanPlane ↦ c • x) '' A) ∩ Metric.closedBall y r =
    (fun x : EuclideanPlane ↦ c • x) ''
      (A ∩ Metric.closedBall ((fun x : EuclideanPlane ↦ c⁻¹ • x) y) (r / c)) := by
  set f : EuclideanPlane → EuclideanPlane := fun x ↦ c • x with hf_def
  set g : EuclideanPlane → EuclideanPlane := fun x ↦ c⁻¹ • x with hg_def

  have h2 : c • (g y) = y := by
    simp [hf_def, hg_def, smul_smul]
    <;> field_simp [hc.ne'] <;> simp

  have h_dist_eq : ∀ (x : EuclideanPlane), dist (f x) y = c * dist x (g y) := by
    intro x
    have h1 : f x - y = c • (x - g y) := by
      calc f x - y
        = c • x - y := by rfl
      _ = c • x - c • (g y) := by rw [h2]
      _ = c • (x - g y) := by rw [smul_sub]
    calc dist (f x) y
      = ‖f x - y‖ := by rw [dist_eq_norm]
    _ = ‖c • (x - g y)‖ := by rw [h1]
    _ = ‖c‖ * ‖x - g y‖ := by rw [norm_smul]
    _ = |c| * ‖x - g y‖ := by rw [Real.norm_eq_abs]
    _ = c * ‖x - g y‖ := by rw [abs_of_pos hc]
    _ = c * dist x (g y) := by rw [dist_eq_norm]

  ext z
  simp only [Set.mem_inter_iff, Set.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hball⟩
    have hdist : dist (f x) y ≤ r := by simpa [Metric.mem_closedBall] using hball
    have h4 : dist x (g y) ≤ r / c := by
      have h_eq : dist (f x) y = c * dist x (g y) := h_dist_eq x
      rw [h_eq] at hdist
      calc dist x (g y)
        = (c * dist x (g y)) / c := by field_simp [hc.ne'] <;> ring
      _ ≤ r / c := by gcongr
    exact ⟨x, ⟨hx, by simpa [Metric.mem_closedBall] using h4⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hball⟩, rfl⟩
    have hdist : dist x (g y) ≤ r / c := by simpa [Metric.mem_closedBall] using hball
    have h5 : dist (f x) y ≤ r := by
      have h_eq : dist (f x) y = c * dist x (g y) := h_dist_eq x
      rw [h_eq]
      calc c * dist x (g y) ≤ c * (r / c) := by gcongr
      _ = r := by field_simp [hc.ne'] <;> ring
    exact ⟨⟨x, hx, rfl⟩, by simpa [Metric.mem_closedBall] using h5⟩

end Smul

end
