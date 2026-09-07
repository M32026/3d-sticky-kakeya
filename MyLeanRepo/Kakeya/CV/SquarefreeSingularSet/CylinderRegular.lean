import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.Basic
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.ImplicitCover
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.GeometricLemmas
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Cylinder regular intersection dimension lemma

Given coprime polynomials f (3 vars) and h (2 vars), the regular part
{f=0, h=0, f_z≠0} has Hausdorff dimension at most 1.

This uses the existing z-graph cover from ImplicitCover.lean and the
plane curve dimension bound.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace Kakeya.CV

/-- Local zGraphEmbed: maps y ∈ Point 2 to (y₀, y₁, f y) ∈ Point 3. -/
def local_zGraphEmbed (f : Point 2 → ℝ) (y : Point 2) : Point 3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![y 0, y 1, f y]

lemma local_zGraphEmbed_proj2 (f : Point 2 → ℝ) (y : Point 2) :
    proj2 (local_zGraphEmbed f y) = y := by
  ext i
  fin_cases i <;> simp [local_zGraphEmbed, proj2, EuclideanSpace.equiv]

lemma local_zGraphEmbed_coord2 (f : Point 2 → ℝ) (y : Point 2) :
    (local_zGraphEmbed f y) 2 = f y := by
  simp [local_zGraphEmbed, EuclideanSpace.equiv]

lemma local_zGraphEmbed_eq (f : Point 2 → ℝ) {x : Point 3} {U : Set (Point 2)}
    (_h1 : proj2 x ∈ U) (h2 : x 2 = f (proj2 x)) :
    local_zGraphEmbed f (proj2 x) = x := by
  ext i
  fin_cases i
  · simp [local_zGraphEmbed, EuclideanSpace.equiv, proj2]
  · simp [local_zGraphEmbed, EuclideanSpace.equiv, proj2]
  · simp [local_zGraphEmbed, EuclideanSpace.equiv, h2]

/-- Evaluating a renamed 2-var polynomial at x equals evaluating the original at proj2 x. -/
lemma rename_eval_proj2 (h : MvPolynomial (Fin 2) ℝ) (x : Point 3) :
    polynomialValue (MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3) h) x =
    polynomialValue h (proj2 x) := by
  simp only [polynomialValue, MvPolynomial.eval_rename]
  <;> rfl

/-- Regular part of a cylinder intersection has dimH ≤ 1.

Given `f` in 3 variables and `h` in 2 variables (both nonzero), the set
`{f=0, h(x,y)=0, ∂f/∂z ≠ 0}` is locally a Lipschitz graph over
`{h=0} ⊆ R²`. Since `dimH({h=0}) ≤ 1`, the graph also has dimH ≤ 1.
-/
lemma cylinder_regular_dimH_le_one
    (f : MvPolynomial (Fin 3) ℝ)
    (h : MvPolynomial (Fin 2) ℝ)
    (hh : h ≠ 0) :
    dimH {p : Point 3 |
      polynomialValue f p = 0 ∧
      polynomialValue (MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3) h) p = 0 ∧
      (polynomialGradient f p) 2 ≠ 0} ≤ 1 := by
  let S : Set (Point 3) := {p |
    polynomialValue f p = 0 ∧
    polynomialValue (MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3) h) p = 0 ∧
    (polynomialGradient f p) 2 ≠ 0}
  have h_cover := regular_zero_set_zGraph_cover f
  rcases h_cover with ⟨patches, hpatches, hcover⟩
  have hS_sub : S ⊆ ⋃ i, patches i := by
    intro p hp
    have h1 : p ∈ polynomialZeroSet f := hp.1
    have h2 : (polynomialGradient f p) 2 ≠ 0 := hp.2.2
    exact hcover ⟨h1, h2⟩
  have h_main : ∀ i, dimH (S ∩ patches i) ≤ 1 := by
    intro i
    rcases hpatches i with ⟨U, ψ, hU_open, hψ_diff, hpatch_eq, hpatch_zero, hpatch_reg⟩
    let D : Set (Point 2) := {y | y ∈ U ∧ polynomialValue h y = 0}
    let g : Point 2 → Point 3 := local_zGraphEmbed ψ
    have hS_patch : S ∩ patches i ⊆ g '' D := by
      intro x hx
      have hxS : x ∈ S := hx.1
      have hxP : x ∈ patches i := hx.2
      have h_in_graph : x ∈ zGraph U ψ := by
        rw [hpatch_eq] at hxP; exact hxP
      have h1 : proj2 x ∈ U ∧ x 2 = ψ (proj2 x) := by
        simpa [zGraph] using h_in_graph
      have h1' : proj2 x ∈ U := h1.1
      have h2 : x 2 = ψ (proj2 x) := h1.2
      have h3 : polynomialValue (MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3) h) x = 0 :=
        hxS.2.1
      have h4 : polynomialValue h (proj2 x) = 0 := by
        have h5 : polynomialValue (MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3) h) x =
            polynomialValue h (proj2 x) := rename_eval_proj2 h x
        rw [h5] at h3
        exact h3
      have h6 : proj2 x ∈ D := ⟨h1', h4⟩
      have h7 : g (proj2 x) = x := local_zGraphEmbed_eq ψ h1' h2
      exact ⟨proj2 x, h6, h7⟩
    have hD_sub : D ⊆ {y : Point 2 | polynomialValue h y = 0} := by
      intro y hy; exact hy.2
    have hD_dim : dimH D ≤ 1 := by
      have h1 : dimH D ≤ dimH {y : Point 2 | polynomialValue h y = 0} := dimH_mono hD_sub
      have h2 : dimH {y : Point 2 | polynomialValue h y = 0} ≤ 1 := plane_curve_dimH_le_one hh
      exact le_trans h1 h2
    have h_lip : ∀ (x : Point 2), x ∈ D →
        ∃ (C : NNReal), ∃ (t : Set (Point 2)), t ∈ nhdsWithin x D ∧ LipschitzOnWith C g t := by
      intro x hx
      have hxU : x ∈ U := hx.1
      have h_diff_at : ContDiffAt ℝ 1 ψ x :=
        hψ_diff.contDiffAt (hU_open.mem_nhds hxU)
      let h_vec : Point 2 → (Fin 3 → ℝ) := fun y => ![y 0, y 1, ψ y]
      have h_coord0 : ContDiffAt ℝ 1 (fun y : Point 2 => y 0) x := by
        exact contDiffAt_piLp_apply 2
      have h_coord1 : ContDiffAt ℝ 1 (fun y : Point 2 => y 1) x := by
        exact contDiffAt_piLp_apply 2
      have h_coord2 : ContDiffAt ℝ 1 ψ x := h_diff_at
      have h_tuple : ContDiffAt ℝ 1 h_vec x := by
        have hpi : ∀ (i : Fin 3), ContDiffAt ℝ 1 (fun y : Point 2 => h_vec y i) x := by
          intro i
          fin_cases i <;> tauto
        simpa [contDiffAt_pi] using hpi
      have h3 : ContDiff ℝ ⊤ ((EuclideanSpace.equiv (Fin 3) ℝ).symm) := by
        exact ContinuousLinearEquiv.contDiff (EuclideanSpace.equiv (Fin 3) ℝ).symm
      have h3_at : ContDiffAt ℝ ⊤ ((EuclideanSpace.equiv (Fin 3) ℝ).symm) (h_vec x) :=
        h3.contDiffAt
      have hg_diff : ContDiffAt ℝ 1 g x := by
        have h_eq : g = (EuclideanSpace.equiv (Fin 3) ℝ).symm ∘ h_vec := by funext y; rfl
        rw [h_eq]
        exact
          (ContinuousLinearEquiv.comp_contDiffAt_iff
            (EuclideanSpace.equiv (Fin 3) ℝ).symm).mpr h_tuple
      have hg_strict : HasStrictFDerivAt g (fderiv ℝ g x) x :=
        hg_diff.hasStrictFDerivAt (by norm_num)
      rcases hg_strict.exists_lipschitzOnWith with ⟨C, t, ht_nhds, ht_lip⟩
      have ht_within : t ∈ nhdsWithin x D := nhdsWithin_le_nhds ht_nhds
      exact ⟨C, t, ht_within, ht_lip⟩
    have h_dim_image : dimH (g '' D) ≤ dimH D :=
      dimH_image_le_of_locally_lipschitzOn h_lip
    have h_final : dimH (S ∩ patches i) ≤ 1 := by
      calc
        dimH (S ∩ patches i) ≤ dimH (g '' D) := dimH_mono hS_patch
        _ ≤ dimH D := h_dim_image
        _ ≤ 1 := hD_dim
    exact h_final
  have hS_union : S ⊆ ⋃ i, S ∩ patches i := by
    intro z hz
    have h1 : z ∈ ⋃ i, patches i := hS_sub hz
    rcases Set.mem_iUnion.mp h1 with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨hz, hi⟩⟩
  have h_dim_union : dimH (⋃ i : ℕ, S ∩ patches i) ≤ 1 := by
    rw [dimH_iUnion]
    exact iSup_le h_main
  exact le_trans (dimH_mono hS_union) h_dim_union

end Kakeya.CV
