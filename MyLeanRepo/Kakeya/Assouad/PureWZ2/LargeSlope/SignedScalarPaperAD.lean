import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ADTransfer

/-!
# Signed scalar transport for paper AD projections

Scaling a projection normal by a nonzero real scalar scales the projected set
by that scalar.  The negative case is handled through the reflection
`x ↦ -x`, before applying the positive affine transfer.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Scaling a normal scales its scalar projection by the same scalar. -/
lemma scalarProjection_smul_eq_image
    (s : ℝ) (n : Point3) (E : Set Point3) :
    scalarProjection (s • n) E =
      (fun x : ℝ => s * x) '' scalarProjection n E := by
  ext y
  simp only [scalarProjection, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨inner ℝ x n, ⟨x, hx, rfl⟩, ?_⟩
    rw [inner_smul_right]
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [inner_smul_right]

/-- Reflection preserves external covering numbers on the real line. -/
lemma externalCoveringNumber_neg_image
    {A : Set ℝ} {ε : NNReal} :
    Metric.externalCoveringNumber ε ((fun x : ℝ => -x) '' A) =
      Metric.externalCoveringNumber ε A := by
  let neg : ℝ → ℝ := fun x => -x
  have hneg : LipschitzWith (1 : NNReal) neg := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [neg, dist_neg_neg]
    change dist x y ≤ 1 * dist x y
    rw [one_mul]
  have h_forward := externalCoveringNumber_lipschitz_image
    (f := neg) (L := (1 : NNReal)) hneg (A := A) (ε := ε)
  simp only [one_mul] at h_forward
  have h_image : neg '' (neg '' A) = A := by
    rw [Set.image_image]
    ext x
    simp [neg]
  have h_backward := externalCoveringNumber_lipschitz_image
    (f := neg) (L := (1 : NNReal)) hneg
    (A := neg '' A) (ε := ε)
  simp only [one_mul, h_image] at h_backward
  exact le_antisymm h_forward h_backward

/-- Reflection reverses a closed interval. -/
lemma image_neg_Icc (left length : ℝ) :
    (fun x : ℝ => -x) '' Set.Icc left (left + length) =
      Set.Icc (-(left + length)) (-left) := by
  ext y
  simp only [Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨x, ⟨hleft, hright⟩, rfl⟩
    constructor <;> linarith
  · rintro ⟨hleft, hright⟩
    refine ⟨-y, ?_, by ring⟩
    constructor <;> linarith

/-- Paper AD is invariant under the scalar reflection `x ↦ -x`. -/
lemma PureWZ2PaperADSet1.neg_transfer
    {S : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 S delta alpha C) :
    PureWZ2PaperADSet1 ((fun x : ℝ => -x) '' S) delta alpha C := by
  rcases hAD with ⟨hdelta, halpha, halpha_one, hC_one, hC_top, hcover⟩
  refine ⟨hdelta, halpha, halpha_one, hC_one, hC_top, ?_⟩
  intro rho hrho hdelta_rho left length hrho_length
  let sourceLeft : ℝ := -(left + length)
  have h_source_inter :
      (fun x : ℝ => -x) '' (S ∩ Set.Icc sourceLeft (sourceLeft + length)) =
        ((fun x : ℝ => -x) '' S) ∩ Set.Icc left (left + length) := by
    have h_source_interval :
        (fun x : ℝ => -x) '' Set.Icc sourceLeft (sourceLeft + length) =
          Set.Icc left (left + length) := by
      rw [image_neg_Icc]
      dsimp [sourceLeft]
      congr 1 <;> ring
    have h_inj : Function.Injective (fun x : ℝ => -x) := by
      intro x y h
      linarith
    rw [Set.image_inter h_inj, h_source_interval]
  have h_cover_source :
      (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩
        (S ∩ Set.Icc sourceLeft (sourceLeft + length))) : ENNReal) ≤
        C * Kakeya.realRpowENN (length / rho) alpha :=
    hcover rho hrho hdelta_rho sourceLeft length hrho_length
  rw [← h_source_inter, externalCoveringNumber_neg_image]
  exact h_cover_source

/-- Transport paper AD under any nonzero scalar rescaling of a projection normal. -/
lemma PureWZ2PaperADSet1.scalarProjection_smul_transfer
    {n : Point3} {E : Set Point3} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 (scalarProjection n E) delta alpha C)
    {s : ℝ} (hs : s ≠ 0) :
    PureWZ2PaperADSet1 (scalarProjection (s • n) E) (|s| * delta) alpha C := by
  rcases lt_or_gt_of_ne hs with hs_neg | hs_pos
  · have hpos : 0 < -s := by linarith
    have hnormal : s • n = (-s) • (-n) := by
      ext i
      simp
    rw [hnormal, scalarProjection_smul_eq_image]
    have hneg : PureWZ2PaperADSet1 (scalarProjection (-n) E) delta alpha C := by
      rw [show scalarProjection (-n) E =
        (fun x : ℝ => -x) '' scalarProjection n E by
          simpa using scalarProjection_smul_eq_image (-1) n E]
      exact hAD.neg_transfer
    have hscaled := hneg.affine_transfer (a := -s) (b := 0) hpos
    simpa [abs_of_neg hs_neg] using hscaled
  · rw [scalarProjection_smul_eq_image]
    have hscaled := hAD.affine_transfer (a := s) (b := 0) hs_pos
    simpa [abs_of_pos hs_pos] using hscaled

end Kakeya.Assouad

end
