import MyLeanRepo.Kakeya.CV.PrincipalAxes.DirectionalPerDirectionPatch
import MyLeanRepo.Kakeya.CV.GeometricMeasure.DirectionalSurfaceAreaAdditivity
import MyLeanRepo.Kakeya.CV.PrincipalAxes.CoordinatePermutation
import MyLeanRepo.Kakeya.CV.GeometricMeasure.GraphImageMeasurable
import Mathlib.Order.Disjointed

/-!
# Measurable disjoint cover additivity on a measurable subset

Generalization of `direction_i_measurable_cover_additivity`: the same countable
cover identity, but restricted to an arbitrary measurable set `S`.  The
disjointified patches are intersected with `S` before summing.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

/-- Given a countable cover by coordinate-permuted regular graph patches and a
measurable set `S`, disjointify the patches intersected with `S` and sum the
per-patch directional surface-area identities. -/
lemma direction_i_measurable_cover_additivity_on
    (p q : MvPolynomial (Fin 3) ℝ)
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : Point 3) (hη : 0 < η)
    (b : OrthonormalBasis (Fin 3) ℝ (Point 3))
    (ℓ : Fin 3 → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hA : ∀ i, A (eBasis i) = ℓ i • b i)
    (hpq : ∀ x, polynomialValue p (z + η • A x) = polynomialValue q x)
    (i : Fin 3)
    (patches : ℕ → Set (Point 3))
    (U : ℕ → Set R2)
    (g : ℕ → R2 → ℝ)
    (hprops : ∀ n, IsOpen (U n) ∧ ContDiffOn ℝ 1 (g n) (U n) ∧
      patches n = coordPerm i '' (graphMap (g n) '' U n) ∧
      (∀ u ∈ U n, polynomialValue q (coordPerm i (graphMap (g n) u)) = 0) ∧
      (∀ u ∈ U n, (polynomialGradient q (coordPerm i (graphMap (g n) u))) i ≠ 0))
    (S : Set (Point 3)) (hS : MeasurableSet S) :
    ENNReal.ofReal (ℓ i) *
      directionalSurfaceArea (b i) p
        ((fun y => z + η • A y) '' (S ∩ ⋃ n, patches n)) =
    ENNReal.ofReal
      (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
      directionalSurfaceArea (eBasis i) q (S ∩ ⋃ n, patches n) := by
  let f : Point 3 → Point 3 := fun y => z + η • A y
  let g_inv : Point 3 → Point 3 := fun y => A.symm (η⁻¹ • (y - z))
  let D : ℕ → Set (Point 3) := fun n => disjointed patches n ∩ S

  have hU n : IsOpen (U n) := (hprops n).1
  have hg n : ContDiffOn ℝ 1 (g n) (U n) := (hprops n).2.1
  have hpatches n : patches n = coordPerm i '' (graphMap (g n) '' U n) :=
    (hprops n).2.2.1
  have h_zero n : ∀ u ∈ U n,
      polynomialValue q (coordPerm i (graphMap (g n) u)) = 0 :=
    (hprops n).2.2.2.1
  have h_reg n : ∀ u ∈ U n,
      (polynomialGradient q (coordPerm i (graphMap (g n) u))) i ≠ 0 :=
    (hprops n).2.2.2.2

  have h_patches_meas : ∀ n, MeasurableSet (patches n) := by
    intro n
    rw [hpatches n]
    have h_graph_meas : MeasurableSet (graphMap (g n) '' U n) :=
      graphMap_image_measurable_of_continuousOn
        (hU n).measurableSet (hg n).continuousOn
    exact (coordPerm i).toMeasurableEquiv.measurableSet_image.mpr
      h_graph_meas

  have hD0_disj :
      Pairwise (fun n m : ℕ => Disjoint (disjointed patches n) (disjointed patches m)) :=
    disjoint_disjointed patches
  have hD0_meas : ∀ n, MeasurableSet (disjointed patches n) :=
    fun n => MeasurableSet.disjointed h_patches_meas n

  have hD_meas : ∀ n, MeasurableSet (D n) := by
    intro n
    exact (hD0_meas n).inter hS

  have hD_disj :
      Pairwise (fun n m : ℕ => Disjoint (D n) (D m)) := by
    intro n m hne
    have h : Disjoint (disjointed patches n) (disjointed patches m) := hD0_disj hne
    rw [Set.disjoint_left] at h ⊢
    intro x hx1 hx2
    have h1 : x ∈ disjointed patches n := hx1.1
    have h2 : x ∈ disjointed patches m := hx2.1
    exact h h1 h2

  have hUnion : (⋃ n, D n) = S ∩ (⋃ n, patches n) := by
    have h1 : (⋃ n, D n) = (⋃ n, disjointed patches n) ∩ S := by
      ext x
      simp only [D, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨n, hn, hS⟩
        exact ⟨⟨n, hn⟩, hS⟩
      · rintro ⟨⟨n, hn⟩, hS⟩
        exact ⟨n, hn, hS⟩
    rw [h1, iUnion_disjointed]
    exact Set.inter_comm _ _

  let B : ℕ → Set R2 := fun n =>
    {u ∈ U n | coordPerm i (graphMap (g n) u) ∈ D n}

  have hB_sub : ∀ n, B n ⊆ U n := by
    intro n u hu
    exact hu.1

  have h_graphMap_contOn : ∀ n, ContinuousOn (graphMap (g n)) (U n) := by
    intro n
    have hgm : ContinuousOn (g n) (U n) := (hg n).continuousOn
    have hpi : ContinuousOn
        (fun x : R2 => (![x 0, x 1, (g n) x] : Fin 3 → ℝ)) (U n) := by
      rw [continuousOn_iff_continuous_restrict]
      have h_components : ∀ (j : Fin 3), Continuous (fun (x : U n) =>
          ((![(x : R2) 0, (x : R2) 1, (g n) (x : R2)] : Fin 3 → ℝ) j)) := by
        intro j
        fin_cases j
        · exact (PiLp.continuous_apply 2 (fun _ => ℝ) 0).comp continuous_subtype_val
        · exact (PiLp.continuous_apply 2 (fun _ => ℝ) 1).comp continuous_subtype_val
        · exact continuousOn_iff_continuous_restrict.mp hgm
      have h_cont : Continuous (fun (x : U n) =>
          (![(x : R2) 0, (x : R2) 1, (g n) (x : R2)] : Fin 3 → ℝ)) :=
        continuous_pi h_components
      exact h_cont
    have h4 : graphMap (g n) = (EuclideanSpace.equiv (Fin 3) ℝ).symm ∘
        (fun x : R2 => (![x 0, x 1, (g n) x] : Fin 3 → ℝ)) := by
      funext x
      rfl
    rw [h4]
    exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp_continuousOn hpi

  have h_coord_cont : Continuous (coordPerm i) := (coordPerm i).continuous

  have hB_meas : ∀ n, MeasurableSet (B n) := by
    intro n
    let h : R2 → Point 3 := fun u => coordPerm i (graphMap (g n) u)
    have h_contOn : ContinuousOn h (U n) :=
      h_coord_cont.comp_continuousOn (h_graphMap_contOn n)
    let h' : U n → Point 3 := fun x => h (x : R2)
    have h'_cont : Continuous h' := continuousOn_iff_continuous_restrict.mp h_contOn
    have h'_meas : Measurable h' := h'_cont.measurable
    have h_preimage : MeasurableSet (h' ⁻¹' (D n)) :=
      h'_meas (hD_meas n)
    have h_emb : MeasurableEmbedding (fun (x : U n) => (x : R2)) :=
      MeasurableEmbedding.subtype_coe (hU n).measurableSet
    have h1 : MeasurableSet ((fun (x : U n) => (x : R2)) '' (h' ⁻¹' (D n))) :=
      h_emb.measurableSet_image.mpr h_preimage
    have h2 : (fun (x : U n) => (x : R2)) '' (h' ⁻¹' (D n)) = B n := by
      ext u
      simp only [Set.mem_image, Set.mem_preimage, B, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.property, hx⟩
      · rintro ⟨hu1, hu2⟩
        refine ⟨⟨u, hu1⟩, hu2, rfl⟩
    rw [← h2]
    exact h1

  have hD_eq : ∀ n,
      D n = coordPerm i '' (graphMap (g n) '' B n) := by
    intro n
    ext x
    simp only [Set.mem_image]
    constructor
    · intro hxD
      have hD_sub : D n ⊆ disjointed patches n := by
        intro x hx
        exact hx.1
      have hD0_sub : disjointed patches n ⊆ patches n := disjointed_subset patches n
      have hx_patches : x ∈ patches n := hD0_sub (hD_sub hxD)
      rw [hpatches n] at hx_patches
      rcases hx_patches with ⟨y, hy, rfl⟩
      rcases hy with ⟨u, huU, rfl⟩
      have huB : u ∈ B n := by
        exact ⟨huU, by simpa [B] using hxD⟩
      exact ⟨graphMap (g n) u, ⟨u, huB, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨u, huB, rfl⟩, rfl⟩
      exact huB.2

  have h_patch : ∀ n,
      ENNReal.ofReal (ℓ i) *
        directionalSurfaceArea (b i) p (f '' (D n)) =
      ENNReal.ofReal (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
        directionalSurfaceArea (eBasis i) q (D n) := by
    intro n
    have h := direction_i_patch_identity_meas p q A η z hη b ℓ hℓ hA hpq i
      (hU n) (hg n) (hB_meas n) (hB_sub n) (h_zero n) (h_reg n)
    rw [hD_eq n]
    exact h

  have hf_inj : Function.Injective f := by
    intro x y hxy
    have h2 : η • A x = η • A y := by simpa [f] using hxy
    have h3 : A x = A y := by
      simpa [smul_smul, hη.ne'] using congr_arg (fun z : Point 3 => η⁻¹ • z) h2
    exact A.injective h3

  have hg_inv_left : Function.LeftInverse g_inv f := by
    intro x
    simp [g_inv, f, hη.ne', map_smul]

  have hg_inv_right : Function.RightInverse g_inv f := by
    intro y
    simp [g_inv, f, hη.ne', map_smul]

  have hf_image_meas : ∀ n, MeasurableSet (f '' (D n)) := by
    intro n
    have h1 : f '' (D n) = g_inv ⁻¹' (D n) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h_goal : g_inv (f x) ∈ D n :=
          (hg_inv_left x).symm ▸ hx
        simpa [Set.mem_preimage] using h_goal
      · intro hy
        refine ⟨g_inv y, hy, ?_⟩
        exact hg_inv_right y
    rw [h1]
    have hgm : Measurable g_inv := by
      have h_cont : Continuous g_inv := by
        have h1 : Continuous (fun y : Point 3 => y - z) :=
          continuous_id.sub continuous_const
        have h2 : Continuous (fun y : Point 3 => η⁻¹ • y) :=
          continuous_const.smul continuous_id
        have h3 : Continuous (A.symm : Point 3 → Point 3) :=
          LinearMap.continuous_of_finiteDimensional (A.symm : Point 3 →ₗ[ℝ] Point 3)
        exact h3.comp (h2.comp h1)
      exact h_cont.measurable
    exact hgm (hD_meas n)

  have h_fD_disj :
      Pairwise (fun n m : ℕ =>
        Disjoint (f '' (D n)) (f '' (D m))) := by
    intro n m hne
    have h : Disjoint (D n) (D m) := hD_disj hne
    have h_img : Disjoint (f '' (D n)) (f '' (D m)) := by
      rw [Set.disjoint_left] at h ⊢
      intro y hy1 hy2
      rcases hy1 with ⟨x1, hx1, rfl⟩
      rcases hy2 with ⟨x2, hx2, h_eq2⟩
      have h_eq : x2 = x1 := hf_inj h_eq2
      rw [h_eq] at hx2
      exact h hx1 hx2
    exact h_img

  have h_f_image_union :
      f '' (⋃ n, D n) = ⋃ n, f '' (D n) := by
    rw [Set.image_iUnion]

  have h_lhs_sum :
      directionalSurfaceArea (b i) p (f '' (⋃ n, D n)) =
      ∑' n, directionalSurfaceArea (b i) p (f '' (D n)) := by
    rw [h_f_image_union]
    exact directionalSurfaceArea_iUnion (b i) p
      (fun n => f '' (D n)) h_fD_disj hf_image_meas

  have h_rhs_sum :
      directionalSurfaceArea (eBasis i) q (⋃ n, D n) =
      ∑' n, directionalSurfaceArea (eBasis i) q (D n) := by
    exact directionalSurfaceArea_iUnion (eBasis i) q
      (fun n => D n) hD_disj hD_meas

  calc
    ENNReal.ofReal (ℓ i) *
          directionalSurfaceArea (b i) p (f '' (S ∩ ⋃ n, patches n))
      = ENNReal.ofReal (ℓ i) *
          directionalSurfaceArea (b i) p (f '' (⋃ n, D n)) := by
        rw [hUnion]
    _ = ENNReal.ofReal (ℓ i) *
          ∑' n, directionalSurfaceArea (b i) p (f '' (D n)) := by
        rw [h_lhs_sum]
    _ = ∑' n, ENNReal.ofReal (ℓ i) *
          directionalSurfaceArea (b i) p (f '' (D n)) := by
        rw [← ENNReal.tsum_mul_left]
    _ = ∑' n, ENNReal.ofReal
          (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
          directionalSurfaceArea (eBasis i) q (D n) := by
        congr with n
        exact h_patch n
    _ = ENNReal.ofReal
          (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
          ∑' n, directionalSurfaceArea (eBasis i) q (D n) := by
        rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal
          (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
          directionalSurfaceArea (eBasis i) q (⋃ n, D n) := by
        rw [h_rhs_sum]
    _ = ENNReal.ofReal
          (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
          directionalSurfaceArea (eBasis i) q (S ∩ ⋃ n, patches n) := by
        rw [hUnion]

end Kakeya.CV
