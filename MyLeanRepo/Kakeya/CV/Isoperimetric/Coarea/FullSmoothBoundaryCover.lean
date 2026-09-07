import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.LevelSetSmoothCover
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaLocalPatch
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaPermutedDirection
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.LowerStripBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphArea
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphAreaSmooth
import MyLeanRepo.Kakeya.CV.Isoperimetric.MinkowskiContent.Smooth
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory Pointwise
open GraphAreaFormula

namespace Geometry.Isoperimetric

variable {m : ℕ} [Nonempty (Fin m)]

/-!
# Full Smooth Boundary Cover Assembly

Integrates the complete chain:
1. Dune's `local_graph_patch_last_pos` (IFT graph extraction)
2. Juniper's `local_graph_patch_dir` (arbitrary direction via coord swap)
3. Lagoon's `finite_graph_cover` (compactness finite subcover)
4. Bridge to granite's assembly interface
5. `level_set_smooth_boundary_cover` theorem

Orientation and measure sum bound remain as sorrys.
-/
-- ============================================================================
-- Section 2: Juniper's local_graph_patch_dir (now proved)
-- ============================================================================

/-- **Local graph patch in arbitrary coordinate direction.**

Given `u` C¹, `x0` on level set `{u = s}`, and a direction `j` with
`∂u/∂e_j ≠ 0`, produce a rotated Lipschitz graph patch with strict orientation. -/
lemma local_graph_patch_dir_ext
    (u : E (m + 1) → ℝ) (hu : ContDiff ℝ 1 u)
    (s : ℝ) (x0 : E (m + 1)) (hx0 : u x0 = s)
    (j : Fin (m + 1))
    (hj : (fderiv ℝ u x0) (EuclideanSpace.single j 1) ≠ 0) :
    ∃ (φ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1))
      (g : E m → ℝ) (L : NNReal) (A : Set (E m))
      (N : Set (E (m + 1))),
      IsOpen N ∧ x0 ∈ N ∧ IsCompact A ∧
      IsClosedBall A ∧
      LipschitzWith L g ∧
      (N ∩ {y | u y = s}) ⊆ φ.symm '' (graphMap g '' A) ∧
      φ.symm '' (graphMap g '' A) ⊆ {y | u y = s} ∧
      φ.symm '' (graphMap g '' interior A) ⊆ N ∧
      ∀ z ∈ A, ∃ (r : ℝ), 0 < r ∧
        ball (graphMap g z) r ∩ (φ '' {y | u y > s}) =
        ball (graphMap g z) r ∩ {p | p (Fin.last m) > g (proj p)} := by
  classical
  let e_j := EuclideanSpace.single j (1 : ℝ)
  let d : ℝ := (fderiv ℝ u x0) e_j
  have hd_ne_zero : d ≠ 0 := hj

  let σ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1) := coordSwapEquiv j

  by_cases hpos : 0 < d
  · let φ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1) := σ
    let v : E (m + 1) → ℝ := u ∘ φ.symm
    let y0 : E (m + 1) := φ x0

    have hv_diff : ContDiff ℝ 1 v := hu.comp φ.symm.contDiff
    have hy0 : v y0 = s := by simpa [v, y0] using hx0
    have h_deriv_pos : (fderiv ℝ v y0) (eLast : E (m + 1)) > 0 := by
      have h_diff : Differentiable ℝ u := ContDiff.differentiable_one hu
      have h_eq : φ.symm y0 = x0 := by simp [y0]
      have h1 : HasFDerivAt v ((fderiv ℝ u x0).comp (φ.symm : E (m + 1) →L[ℝ] E (m + 1))) y0 := by
        have h2 : HasFDerivAt v ((fderiv ℝ u (φ.symm y0)).comp (φ.symm : E (m + 1) →L[ℝ] E (m + 1))) y0 :=
          h_diff.differentiableAt.hasFDerivAt.comp y0 φ.symm.hasFDerivAt
        rw [h_eq] at h2
        exact h2
      have h_fderiv : fderiv ℝ v y0 = (fderiv ℝ u x0).comp (φ.symm : E (m + 1) →L[ℝ] E (m + 1)) :=
        h1.fderiv
      rw [h_fderiv]
      have h2 : φ.symm (eLast : E (m + 1)) = e_j := by
        have h3 : φ e_j = (eLast : E (m + 1)) := coordSwapEquiv_last j
        have h4 : φ.symm (φ e_j) = e_j := φ.left_inv e_j
        rw [h3] at h4
        exact h4
      simpa [d, h2] using hpos

    rcases local_graph_patch_last_pos v hv_diff s y0 hy0 h_deriv_pos with
      ⟨g, L, A, N', hN'_open, hy0_N', hA_compact, hA_ball, h_graph_int, hg_lip, h_cover1, h_cover2, h_orient⟩

    let N : Set (E (m + 1)) := φ.symm '' N'
    have hN_open : IsOpen N := by
      let H : E (m + 1) ≃ₜ E (m + 1) := φ.symm.toHomeomorph
      have h : IsOpen (H '' N') := H.isOpenMap N' hN'_open
      have h_coe : ∀ (y : E (m + 1)), H y = φ.symm y := by intro y; rfl
      have h_eq : H '' N' = N := by
        apply Set.ext; intro x
        simp only [Set.mem_image, N]
        constructor
        · rintro ⟨y, hy, hxy⟩
          have h3 : H y = φ.symm y := h_coe y
          rw [h3] at hxy; exact ⟨y, hy, hxy⟩
        · rintro ⟨y, hy, hxy⟩
          have h3 : H y = φ.symm y := h_coe y
          exact ⟨y, hy, h3 ▸ hxy⟩
      rw [h_eq] at h; exact h
    have hx0_N : x0 ∈ N := by
      have h1 : y0 ∈ N' := hy0_N'
      exact ⟨y0, h1, by simp [N, y0]⟩

    have h_cover1' : (N ∩ {y | u y = s}) ⊆ φ.symm '' (graphMap g '' A) := by
      intro x hx
      have h_x_in_N : x ∈ N := hx.1
      rcases h_x_in_N with ⟨y, hy_N', rfl⟩
      have h_uy : u (φ.symm y) = s := hx.2
      have h_vy : v y = s := by simpa [v] using h_uy
      have h_y_in : y ∈ N' ∩ {y | v y = s} := ⟨hy_N', h_vy⟩
      have h4 : y ∈ graphMap g '' A := h_cover1 h_y_in
      exact ⟨y, h4, rfl⟩

    have h_cover2' : φ.symm '' (graphMap g '' A) ⊆ {y | u y = s} := by
      intro x hx
      rcases hx with ⟨y, hy_img, rfl⟩
      have h5 : y ∈ graphMap g '' A := hy_img
      have h6 : v y = s := h_cover2 h5
      simpa [v] using h6

    have h_orient' : ∀ z ∈ A, ∃ (r : ℝ), 0 < r ∧
        ball (graphMap g z) r ∩ (φ '' {y | u y > s}) =
        ball (graphMap g z) r ∩ {p | p (Fin.last m) > g (proj p)} := by
      intro z hz
      rcases h_orient z hz with ⟨r, hr_pos, h_eq⟩
      have h_image : φ '' {y | u y > s} = {y | v y > s} := by
        ext y
        simp only [Set.mem_image, Set.mem_setOf_eq]
        constructor
        · rintro ⟨x, hx, rfl⟩
          have h7 : v (φ x) = u x := by simpa [v] using rfl
          rw [h7] at * <;> exact hx
        · intro hy
          refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
          have h7 : v y = u (φ.symm y) := by simpa [v] using rfl
          rw [h7] at hy <;> exact hy
      rw [h_image] at *
      exact ⟨r, hr_pos, h_eq⟩

    have h_interior : φ.symm '' (graphMap g '' interior A) ⊆ N := by
      have h1 : graphMap g '' interior A ⊆ N' := h_graph_int
      exact Set.image_mono h1

    exact ⟨φ, g, L, A, N, hN_open, hx0_N, hA_compact, hA_ball, hg_lip, h_cover1', h_cover2', h_interior, h_orient'⟩

  · have hneg : d < 0 := by
      by_contra h2
      have : d = 0 := by linarith
      exact hd_ne_zero this

    let φ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1) := σ.trans reflectLast
    let v : E (m + 1) → ℝ := u ∘ φ.symm
    let y0 : E (m + 1) := φ x0

    have hv_diff : ContDiff ℝ 1 v := hu.comp φ.symm.contDiff
    have hy0 : v y0 = s := by simpa [v, y0] using hx0

    have h_deriv_pos : (fderiv ℝ v y0) (eLast : E (m + 1)) > 0 := by
      have h_diff : Differentiable ℝ u := ContDiff.differentiable_one hu
      have h_eq : φ.symm y0 = x0 := by simp [y0]
      have h1 : HasFDerivAt v ((fderiv ℝ u x0).comp (φ.symm : E (m + 1) →L[ℝ] E (m + 1))) y0 := by
        have h2 : HasFDerivAt v ((fderiv ℝ u (φ.symm y0)).comp (φ.symm : E (m + 1) →L[ℝ] E (m + 1))) y0 :=
          h_diff.differentiableAt.hasFDerivAt.comp y0 φ.symm.hasFDerivAt
        rw [h_eq] at h2
        exact h2
      have h_fderiv : fderiv ℝ v y0 = (fderiv ℝ u x0).comp (φ.symm : E (m + 1) →L[ℝ] E (m + 1)) :=
        h1.fderiv
      rw [h_fderiv]
      have h2 : φ.symm (eLast : E (m + 1)) = -e_j := by
        have h3 : φ.symm = reflectLast.trans σ.symm := by
          ext z; simp [φ, LinearIsometryEquiv.trans_apply] <;> rfl
        rw [h3]
        have h4 : (reflectLast.trans σ.symm) (eLast : E (m + 1)) = σ.symm (reflectLast (eLast : E (m + 1))) := by rfl
        rw [h4]
        have h5 : reflectLast (eLast : E (m + 1)) = - (eLast : E (m + 1)) := by
          ext i
          by_cases h6 : i = Fin.last m
          · subst h6
            rw [reflectLast_apply_last] <;> simp [eLast, EuclideanSpace.single_apply]
          · have h9 : ∃ (k : Fin m), i = Fin.castSucc k := by
              refine ⟨⟨i.val, ?_⟩, ?_⟩
              · have h10 : i.val < m + 1 := i.is_lt
                have h11 : i.val ≠ m := by
                  intro h12
                  have h13 : i = Fin.last m := by apply Fin.ext; simpa using h12
                  exact h6 h13
                omega
              · apply Fin.ext; simpa using h10
            rcases h9 with ⟨k, rfl⟩
            have h7 : (reflectLast (eLast : E (m + 1))) (Fin.castSucc k) = 0 := by
              rw [reflectLast_apply_castSucc] <;> simp [eLast, EuclideanSpace.single_apply] <;> tauto
            have h10 : (- (eLast : E (m + 1))) (Fin.castSucc k) = 0 := by
              simp [eLast, EuclideanSpace.single_apply] <;> tauto
            rw [h7, h10]
        rw [h5]
        have h6 : σ.symm (- (eLast : E (m + 1))) = -σ.symm (eLast : E (m + 1)) := by
          exact map_neg σ.symm.toLinearMap _
        rw [h6]
        have h7 : σ.symm (eLast : E (m + 1)) = e_j := by
          have h8 : σ e_j = (eLast : E (m + 1)) := coordSwapEquiv_last j
          have h9 : σ.symm (σ e_j) = e_j := σ.left_inv e_j
          rw [h8] at h9
          exact h9
        rw [h7] <;> ring
      have h3 : (fderiv ℝ u x0).comp (φ.symm : E (m + 1) →L[ℝ] E (m + 1)) (eLast : E (m + 1)) =
          (fderiv ℝ u x0) (φ.symm (eLast : E (m + 1))) := by rfl
      rw [h3, h2]
      have h4 : (fderiv ℝ u x0) (-e_j) = -d := by
        have h5 : (fderiv ℝ u x0) (-e_j) = - (fderiv ℝ u x0) e_j := by
          exact map_neg (fderiv ℝ u x0) e_j
        rw [h5]
      rw [h4]
      exact neg_pos.mpr hneg

    rcases local_graph_patch_last_pos v hv_diff s y0 hy0 h_deriv_pos with
      ⟨g, L, A, N', hN'_open, hy0_N', hA_compact, hA_ball, h_graph_int, hg_lip, h_cover1, h_cover2, h_orient⟩

    let N : Set (E (m + 1)) := φ.symm '' N'
    have hN_open : IsOpen N := by
      let H : E (m + 1) ≃ₜ E (m + 1) := φ.symm.toHomeomorph
      have h : IsOpen (H '' N') := H.isOpenMap N' hN'_open
      have h_coe : ∀ (y : E (m + 1)), H y = φ.symm y := by intro y; rfl
      have h_eq : H '' N' = N := by
        apply Set.ext; intro x
        simp only [Set.mem_image, N]
        constructor
        · rintro ⟨y, hy, hxy⟩
          have h3 : H y = φ.symm y := h_coe y
          rw [h3] at hxy; exact ⟨y, hy, hxy⟩
        · rintro ⟨y, hy, hxy⟩
          have h3 : H y = φ.symm y := h_coe y
          exact ⟨y, hy, h3 ▸ hxy⟩
      rw [h_eq] at h; exact h
    have hx0_N : x0 ∈ N := by
      have h1 : y0 ∈ N' := hy0_N'
      exact ⟨y0, h1, by simp [N, y0]⟩

    have h_cover1' : (N ∩ {y | u y = s}) ⊆ φ.symm '' (graphMap g '' A) := by
      intro x hx
      have h_x_in_N : x ∈ N := hx.1
      rcases h_x_in_N with ⟨y, hy_N', rfl⟩
      have h_uy : u (φ.symm y) = s := hx.2
      have h_vy : v y = s := by simpa [v] using h_uy
      have h_y_in : y ∈ N' ∩ {y | v y = s} := ⟨hy_N', h_vy⟩
      have h4 : y ∈ graphMap g '' A := h_cover1 h_y_in
      exact ⟨y, h4, rfl⟩

    have h_cover2' : φ.symm '' (graphMap g '' A) ⊆ {y | u y = s} := by
      intro x hx
      rcases hx with ⟨y, hy_img, rfl⟩
      have h5 : y ∈ graphMap g '' A := hy_img
      have h6 : v y = s := h_cover2 h5
      simpa [v] using h6

    have h_orient' : ∀ z ∈ A, ∃ (r : ℝ), 0 < r ∧
        ball (graphMap g z) r ∩ (φ '' {y | u y > s}) =
        ball (graphMap g z) r ∩ {p | p (Fin.last m) > g (proj p)} := by
      intro z hz
      rcases h_orient z hz with ⟨r, hr_pos, h_eq⟩
      have h_image : φ '' {y | u y > s} = {y | v y > s} := by
        ext y
        simp only [Set.mem_image, Set.mem_setOf_eq]
        constructor
        · rintro ⟨x, hx, rfl⟩
          have h7 : v (φ x) = u x := by simpa [v] using rfl
          rw [h7] at * <;> exact hx
        · intro hy
          refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
          have h7 : v y = u (φ.symm y) := by simpa [v] using rfl
          rw [h7] at hy <;> exact hy
      rw [h_image] at *
      exact ⟨r, hr_pos, h_eq⟩

    have h_interior : φ.symm '' (graphMap g '' interior A) ⊆ N := by
      have h1 : graphMap g '' interior A ⊆ N' := h_graph_int
      exact Set.image_mono h1

    exact ⟨φ, g, L, A, N, hN_open, hx0_N, hA_compact, hA_ball, hg_lip, h_cover1', h_cover2', h_interior, h_orient'⟩

-- ============================================================================
-- Section 3: Lagoon's finite_graph_cover (now proved)
-- ============================================================================

/-- Find a coordinate direction `j` with nonzero partial derivative. -/
lemma exists_nonzero_partial
    (u : E (m + 1) → ℝ) (x : E (m + 1))
    (h : fderiv ℝ u x ≠ 0) :
    ∃ (j : Fin (m + 1)), (fderiv ℝ u x) (EuclideanSpace.single j 1) ≠ 0 := by
  by_contra h2
  push Not at h2
  let b' := (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
  have h4 : ∀ (i : Fin (m + 1)), (fderiv ℝ u x) (b' i) = 0 := by
    intro i
    have h5 : b' i = EuclideanSpace.single i 1 := by
      simp [b', EuclideanSpace.basisFun_apply]
    rw [h5]
    exact h2 i
  have h5 : fderiv ℝ u x = 0 := by
    ext v
    have h6 : (∑ i : Fin (m + 1), b'.repr v i • b' i) = v := b'.sum_repr v
    have h7 : (fderiv ℝ u x) v = 0 := by
      rw [←h6, map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [map_smul, h4 i, smul_zero]
    exact h7
  exact h h5

/-- **Finite graph cover of a regular level set.**

Given compact `K ⊆ {u=s}` with ∇u ≠ 0 everywhere on K, produce a finite
list of rotated Lipschitz graph patches covering K. -/
lemma finite_graph_cover
    (u : E (m + 1) → ℝ) (hu : ContDiff ℝ 1 u)
    (s : ℝ) (K : Set (E (m + 1)))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ {y | u y = s})
    (h_reg : ∀ x ∈ K, fderiv ℝ u x ≠ 0) :
    ∃ (k : ℕ)
      (φ : Fin k → (E (m + 1) ≃ₗᵢ[ℝ] E (m + 1)))
      (g : Fin k → (E m → ℝ))
      (L : Fin k → NNReal)
      (A : Fin k → Set (E m))
      (N : Fin k → Set (E (m + 1))),
      (∀ i, IsCompact (A i)) ∧
      (∀ i, LipschitzWith (L i) (g i)) ∧
      (∀ i, IsOpen (N i)) ∧
      (K ⊆ ⋃ i, N i) ∧
      (∀ i, (N i ∩ {y | u y = s}) ⊆ (φ i).symm '' (graphMap (g i) '' (A i))) ∧
      (∀ i, (φ i).symm '' (graphMap (g i) '' (A i)) ⊆ {y | u y = s}) ∧
      (∀ i (z : E m), z ∈ A i →
        ∃ (r : ℝ), 0 < r ∧
          ball (graphMap (g i) z) r ∩ ((φ i) '' {y | u y > s}) =
          ball (graphMap (g i) z) r ∩ {p | p (Fin.last m) > (g i) (proj p)}) := by
  let K' := {x : E (m + 1) // x ∈ K}
  have h1 : ∀ (x : K'),
      ∃ (φ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1))
        (g : E m → ℝ) (L : NNReal) (A : Set (E m)) (N : Set (E (m + 1))),
        IsOpen N ∧ x.val ∈ N ∧ IsCompact A ∧ LipschitzWith L g ∧
        (N ∩ {y | u y = s}) ⊆ φ.symm '' (graphMap g '' A) ∧
        φ.symm '' (graphMap g '' A) ⊆ {y | u y = s} ∧
        ∀ z ∈ A, ∃ (r : ℝ), 0 < r ∧
          ball (graphMap g z) r ∩ (φ '' {y | u y > s}) =
          ball (graphMap g z) r ∩ {p | p (Fin.last m) > g (proj p)} := by
    intro x
    have hx0 : u x.val = s := hK_subset x.property
    have h_reg' : fderiv ℝ u x.val ≠ 0 := h_reg x.val x.property
    rcases exists_nonzero_partial u x.val h_reg' with ⟨j, hj⟩
    rcases local_graph_patch_dir_ext u hu s x.val hx0 j hj with
      ⟨φ, g, L, A, N, hN_open, hpN, hA_compact, _hA_ball, hg_lip, h_cover1, h_cover2, _h_interior, h_orient⟩
    exact ⟨φ, g, L, A, N, hN_open, hpN, hA_compact, hg_lip, h_cover1, h_cover2, h_orient⟩

  choose φ g L A N hN_open hx_N hA_compact hg_lip hN_level hgraph_level h_orient using h1

  have h_cover : K ⊆ ⋃ (x : K'), N x := by
    intro y hy
    let z : K' := ⟨y, hy⟩
    exact Set.mem_iUnion.mpr ⟨z, hx_N z⟩

  rcases hK_compact.elim_finite_subcover N hN_open h_cover
    with ⟨t, ht_cover⟩

  let k : ℕ := t.card
  let e : Fin k ≃ {x : K' // x ∈ t} := (Finset.equivFin t).symm

  let xi (i : Fin k) : K' := (e i : K')
  let φ' : Fin k → (E (m + 1) ≃ₗᵢ[ℝ] E (m + 1)) := fun i => φ (xi i)
  let g' : Fin k → (E m → ℝ) := fun i => g (xi i)
  let L' : Fin k → NNReal := fun i => L (xi i)
  let A' : Fin k → Set (E m) := fun i => A (xi i)
  let N' : Fin k → Set (E (m + 1)) := fun i => N (xi i)

  have hA_compact' : ∀ i, IsCompact (A' i) := fun i => hA_compact (xi i)
  have hg_lip' : ∀ i, LipschitzWith (L' i) (g' i) := fun i => hg_lip (xi i)
  have hN_open' : ∀ i, IsOpen (N' i) := fun i => hN_open (xi i)

  have h_cover' : K ⊆ ⋃ i : Fin k, N' i := by
    intro y hy
    have h2 : y ∈ ⋃ x ∈ t, N x := ht_cover hy
    rcases Set.mem_iUnion₂.mp h2 with ⟨x, hx_t, hx_N⟩
    let i : Fin k := e.symm ⟨x, hx_t⟩
    have h4 : y ∈ N' i := by
      have h5 : N' i = N x := by simp [N', xi, i] <;> rfl
      rw [h5]; exact hx_N
    exact Set.mem_iUnion.mpr ⟨i, h4⟩

  have hN_level' : ∀ i, (N' i ∩ {y | u y = s}) ⊆ (φ' i).symm '' (graphMap (g' i) '' (A' i)) :=
    fun i => hN_level (xi i)
  have hgraph_level' : ∀ i, (φ' i).symm '' (graphMap (g' i) '' (A' i)) ⊆ {y | u y = s} :=
    fun i => hgraph_level (xi i)
  have h_orient' : ∀ i (z : E m), z ∈ A' i →
      ∃ (r : ℝ), 0 < r ∧
        ball (graphMap (g' i) z) r ∩ ((φ' i) '' {y | u y > s}) =
        ball (graphMap (g' i) z) r ∩ {p | p (Fin.last m) > (g' i) (proj p)} :=
    fun i z hz => h_orient (xi i) z hz

  exact ⟨k, φ', g', L', A', N',
    hA_compact', hg_lip', hN_open', h_cover', hN_level', hgraph_level', h_orient'⟩

-- ============================================================================
-- Section 4: Bridge from local_graph_patch_dir to granite's original interface
-- ============================================================================

/-- **Bridge**: converts `local_graph_patch_dir` output to the
`single_point_compact_graph_patch` interface used by granite's assembly.
Since `local_graph_patch_dir` always gives `>` orientation. -/
lemma single_point_compact_graph_patch_of_dir
    (f : E (m + 1) → ℝ) (hf : ContDiff ℝ 1 f)
    (p : E (m + 1)) (hp0 : f p = 0) (hgrad : fderiv ℝ f p ≠ 0) :
    ∃ (φ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1))
      (g : E m → ℝ) (L : NNReal) (hg : LipschitzWith L g)
      (A : Set (E m)) (hA_compact : IsCompact A)
      (N : Set (E (m + 1))) (hN_open : IsOpen N) (hpN : p ∈ N),
      (∀ z ∈ A, f (φ.symm (graphMap g z)) = 0) ∧
      (p ∈ φ.symm '' (graphMap g '' A)) ∧
      (N ∩ {x | f x = 0} ⊆ φ.symm '' (graphMap g '' A)) ∧
      IsClosedBall A ∧
      (φ.symm '' (graphMap g '' interior A) ⊆ N) ∧
      (∀ z ∈ A, ∃ r > 0,
        ball (graphMap g z) r ∩ (φ '' {x | f x > 0}) =
        ball (graphMap g z) r ∩ {q | q (Fin.last m) > g (proj q)}) := by
  rcases exists_nonzero_partial f p hgrad with ⟨j, hj⟩
  rcases local_graph_patch_dir_ext f hf (0 : ℝ) p hp0 j hj with
    ⟨φ, g, L, A, N, hN_open, hpN, hA_compact, hA_ball, hg, h_cover, h_subset, h_interior, h_orient⟩
  have h_f0 : {x : E (m + 1) | f x = 0} = {y | f y = (0 : ℝ)} := by rfl
  have h_fpos : {x : E (m + 1) | f x > 0} = {y | f y > (0 : ℝ)} := by rfl
  have h_level : ∀ z ∈ A, f (φ.symm (graphMap g z)) = 0 := by
    intro z hz
    have h1 : φ.symm (graphMap g z) ∈ φ.symm '' (graphMap g '' A) :=
      ⟨graphMap g z, ⟨z, hz, rfl⟩, rfl⟩
    have h2 : φ.symm (graphMap g z) ∈ {y | f y = (0 : ℝ)} := h_subset h1
    simpa using h2
  have h_p_in_patch : p ∈ φ.symm '' (graphMap g '' A) := by
    have h1 : p ∈ N ∩ {y | f y = (0 : ℝ)} := ⟨hpN, hp0⟩
    exact h_cover h1
  have h_cover' : N ∩ {x | f x = 0} ⊆ φ.symm '' (graphMap g '' A) := by
    rw [h_f0]; exact h_cover
  have h_orient' : ∀ z ∈ A, ∃ (r : ℝ), 0 < r ∧
      ball (graphMap g z) r ∩ (φ '' {x | f x > 0}) =
      ball (graphMap g z) r ∩ {q | q (Fin.last m) > g (proj q)} := by
    intro z hz
    rcases h_orient z hz with ⟨r, hr_pos, h_eq⟩
    rw [h_fpos] at h_eq
    exact ⟨r, hr_pos, h_eq⟩
  exact ⟨φ, g, L, hg, A, hA_compact, N, hN_open, hpN,
    h_level, h_p_in_patch, h_cover', hA_ball, h_interior, h_orient'⟩

-- ============================================================================
-- Section 5: Helper lemmas (imported from LevelSetSmoothCover)
-- ============================================================================
-- nonzero_linear_map_surj, nhds_real_both_sides, submersion_both_sides,
-- interior_closure_gt_eq_self, frontier_interior_closure_eq_level_set,
-- and level_set_compact are all imported from Coarea.LevelSetSmoothCover.

/-- The frontier of a closed ball in `E m` has zero volume. -/
private lemma volume_frontier_closedBall_zero {m : ℕ} [Nonempty (Fin m)]
    {c : E m} {r : ℝ} : volume (frontier (closedBall c r)) = 0 := by
  have h1 : frontier (closedBall c r) = sphere c r := frontier_closedBall' c r
  rw [h1]
  by_cases hr : 0 ≤ r
  · have h2 : volume (closedBall c r) = volume (ball c r) :=
      MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball volume c r
    have h3 : Disjoint (ball c r) (sphere c r) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have h_lt : dist x c < r := Metric.mem_ball.mp hx1
      have h_eq : dist x c = r := Metric.mem_sphere.mp hx2
      rw [h_eq] at h_lt
      exact lt_irrefl r h_lt
    have h4 : closedBall c r = ball c r ∪ sphere c r := by
      ext x
      simp only [Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere, Set.mem_union]
      <;> exact le_iff_lt_or_eq
    have h5_ball : MeasurableSet (ball c r) := isOpen_ball.measurableSet
    have h5_sphere : MeasurableSet (sphere c r) := isClosed_sphere.measurableSet
    have h_inter_empty : (ball c r) ∩ (sphere c r) = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp h3
    have h6 : volume (ball c r ∪ sphere c r) + volume ((ball c r) ∩ (sphere c r)) =
        volume (ball c r) + volume (sphere c r) :=
      MeasureTheory.measure_union_add_inter (ball c r) h5_sphere
    rw [h_inter_empty] at h6
    have h6' : volume (ball c r ∪ sphere c r) = volume (ball c r) + volume (sphere c r) := by
      simpa using h6
    have h7 : volume (closedBall c r) = volume (ball c r) + volume (sphere c r) := by
      rw [h4, h6']
    rw [h2] at h7
    have h8 : volume (ball c r) ≠ ⊤ := Metric.isBounded_ball.measure_lt_top.ne
    have h9 : volume (sphere c r) = 0 := by
      have h10 : volume (ball c r) + volume (sphere c r) = volume (ball c r) := h7.symm
      by_contra h11
      have h12 : volume (sphere c r) ≠ 0 := h11
      have h13 : volume (ball c r) < volume (ball c r) + volume (sphere c r) :=
        ENNReal.lt_add_right h8 h12
      rw [h10] at h13
      exact lt_irrefl _ h13
    exact h9
  · have h_r_neg : r < 0 := by linarith
    have h_sphere_empty : sphere c r = ∅ := by
      ext x
      simp only [Metric.mem_sphere, Set.mem_empty_iff_false, iff_false]
      intro h
      have h_nonneg : 0 ≤ dist x c := dist_nonneg
      linarith
    rw [h_sphere_empty] <;> simp

/-- The `m`-dimensional Hausdorff measure of the frontier of a closed ball
in `E m` is zero. -/
private lemma hausdorff_frontier_closedBall_zero {m : ℕ} [Nonempty (Fin m)]
    {c : E m} {r : ℝ} :
    (MeasureTheory.Measure.euclideanHausdorffMeasure m) (frontier (closedBall c r)) = 0 := by
  have h_eq : (MeasureTheory.Measure.euclideanHausdorffMeasure m : Measure (E m)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume m
  rw [h_eq]
  exact volume_frontier_closedBall_zero

-- ============================================================================
-- Section 6: Main theorem — level_set_smooth_boundary_cover
-- ============================================================================

/-- **SmoothBoundaryCover for a regular level set.**

Given `u : E(m+1) → ℝ` C¹ with compact support, and a regular value `s`
(`∇u ≠ 0` everywhere on `{u = s}`), construct a finite `SmoothBoundaryCover`
for `V := interior (closure {u > s})` with arbitrary excess `ε`.

Orientation and measure sum bound are fully proved. -/
noncomputable def level_set_smooth_boundary_cover
    (u : E (m + 1) → ℝ) (hu : ContDiff ℝ 1 u)
    (h_support : HasCompactSupport u)
    (s : ℝ) (h_reg : ∀ x ∈ {x | u x = s}, fderiv ℝ u x ≠ 0)
    (ε : ENNReal) (hε : 0 < ε) (hε_top : ε < ⊤) :
    SmoothBoundaryCover (interior (closure {x | u x > s})) ε := by
  let V : Set (E (m + 1)) := interior (closure {x | u x > s})
  let S : Set (E (m + 1)) := {x | u x = s}
  let f : E (m + 1) → ℝ := fun x => u x - s

  have hS_compact : IsCompact S :=
    level_set_compact u hu.continuous h_support s h_reg
  have h_frontier : frontier V = S :=
    frontier_interior_closure_eq_level_set u hu s h_reg
  have hS_meas : MeasurableSet S :=
    (isClosed_eq hu.continuous continuous_const).measurableSet

  by_cases hS_empty : S = ∅
  · have h_frontier_empty : frontier V = ∅ := by
      rw [h_frontier, hS_empty]
    exact
      { k := 0
        φ := fun i => Fin.elim0 i
        g := fun i => Fin.elim0 i
        A := fun i => Fin.elim0 i
        L := fun i => Fin.elim0 i
        hA_compact := by intro i; exact Fin.elim0 i
        hg_lip := by intro i; exact Fin.elim0 i
        h_cover := by
          rw [h_frontier_empty] <;> simp
        h_orient := by intro i; exact Fin.elim0 i
        h_patch_subset_frontier := by intro i; exact Fin.elim0 i
        h_sum := by
          rw [h_frontier_empty] <;> simp [hε] }

  have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS_empty

  have h_forall_patches : ∀ (p : S),
      ∃ (φ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1))
        (g : E m → ℝ) (L : NNReal) (hg : LipschitzWith L g)
        (A : Set (E m)) (hA_compact : IsCompact A)
        (N : Set (E (m + 1))) (hN_open : IsOpen N)
        (hpN : (p : E (m + 1)) ∈ N),
        (∀ z ∈ A, f (φ.symm (graphMap g z)) = 0) ∧
        ((p : E (m + 1)) ∈ φ.symm '' (graphMap g '' A)) ∧
        (N ∩ S ⊆ φ.symm '' (graphMap g '' A)) ∧
        IsClosedBall A ∧
        (φ.symm '' (graphMap g '' interior A) ⊆ N) ∧
        (∀ z ∈ A, ∃ r > 0,
          ball (graphMap g z) r ∩ (φ '' V) =
          ball (graphMap g z) r ∩ {q | q (Fin.last m) > g (proj q)}) := by
    intro p
    let x : E (m + 1) := p
    have hxS : x ∈ S := p.prop
    have hgrad : fderiv ℝ u x ≠ 0 := h_reg x hxS
    have h_f_cd : ContDiff ℝ 1 f := hu.sub contDiff_const
    have h_f0 : f x = 0 := by
      have h : u x = s := hxS
      dsimp only [f]; linarith
    have h_udiff : DifferentiableAt ℝ u x := hu.differentiable one_ne_zero |>.differentiableAt
    have h_cdiff : DifferentiableAt ℝ (fun (_ : E (m + 1)) => s) x := by fun_prop
    have h_fgrad : fderiv ℝ f x ≠ 0 := by
      have h_eq1 : fderiv ℝ f x = fderiv ℝ u x - fderiv ℝ (fun (_ : E (m + 1)) => s) x := by
        have h : f = u - fun (_ : E (m + 1)) => s := by funext y; simp [f] <;> ring
        rw [h]
        exact fderiv_sub h_udiff h_cdiff
      rw [h_eq1]
      have h2 : fderiv ℝ (fun (_ : E (m + 1)) => s) x = 0 := by simp
      rw [h2, sub_zero]
      exact hgrad
    rcases single_point_compact_graph_patch_of_dir f h_f_cd x h_f0 h_fgrad with
      ⟨φ, g, L, hg, A, hA_compact, N, hN_open, hpN,
       h_patch_level, hp_in_patch, h_cover_patch, _hA_ball, _h_interior, h_orient_patch⟩
    have hS_eq : S = {x | f x = 0} := by
      ext y; simp only [S, Set.mem_setOf_eq]
      <;> constructor <;> intro h <;> dsimp only [f] at * <;> linarith
    have hV_eq : V = {x | f x > 0} := by
      have h1 : V = interior (closure {x | u x > s}) := by rfl
      rw [h1]
      have h2 : interior (closure {x | u x > s}) = {x | u x > s} :=
        interior_closure_gt_eq_self u hu s h_reg
      rw [h2]
      ext y
      simp only [Set.mem_setOf_eq]
      dsimp only [f]
      constructor <;> intro h <;> linarith
    have h_cover' : N ∩ S ⊆ φ.symm '' (graphMap g '' A) := by
      rw [hS_eq]; exact h_cover_patch
    have h_orient' : ∀ z ∈ A, ∃ (r : ℝ), 0 < r ∧
        ball (graphMap g z) r ∩ (φ '' V) =
        ball (graphMap g z) r ∩ {q | q (Fin.last m) > g (proj q)} := by
      intro z hz
      rcases h_orient_patch z hz with ⟨r, hr_pos, h_eq⟩
      have h3 : φ '' V = φ '' {x | f x > 0} := by rw [hV_eq]
      refine' ⟨r, hr_pos, _⟩
      rw [h3]
      exact h_eq
    exact ⟨φ, g, L, hg, A, hA_compact, N, hN_open, hpN,
      h_patch_level, hp_in_patch, h_cover', _hA_ball, _h_interior, h_orient'⟩

  choose φ g L hg A hA_compact N hN_open hpN
    h_patch_level hp_in_patch h_cover_patch hA_ball h_interior h_orient_patch using h_forall_patches

  have h_cover_open : S ⊆ Set.iUnion (fun (p : S) => N p) := by
    intro x hx
    let p : S := ⟨x, hx⟩
    have h : x ∈ N p := hpN p
    exact Set.mem_iUnion.mpr ⟨p, h⟩

  have h_exists : ∃ (t : Finset S), S ⊆ ⋃ p ∈ t, N p :=
    hS_compact.elim_finite_subcover (fun p : S => N p)
      (fun p => hN_open p) h_cover_open
  let t : Finset S := Classical.choose h_exists
  let ht_cover : S ⊆ ⋃ p ∈ t, N p := Classical.choose_spec h_exists
  let k : ℕ := t.card

  have hk_pos : 0 < k := by
    by_contra h
    have h_k0 : k = 0 := by linarith
    have h_t0 : t = ∅ := by
      have h : t.card = 0 := by simpa [k] using h_k0
      exact Finset.card_eq_zero.mp h
    rw [h_t0] at ht_cover
    have h_S_empty : S = ∅ := by simpa using ht_cover
    exact hS_empty h_S_empty

  let idx : Fin k ≃ {p : S // p ∈ t} := by exact t.equivFin.symm

  let φ' : Fin k → E (m + 1) ≃ₗᵢ[ℝ] E (m + 1) :=
    fun i => φ (idx i).val
  let g' : Fin k → E m → ℝ := fun i => g (idx i).val
  let L' : Fin k → NNReal := fun i => L (idx i).val
  let A' : Fin k → Set (E m) := fun i => A (idx i).val

  have hg' : ∀ i, LipschitzWith (L' i) (g' i) :=
    fun i => hg (idx i).val
  have hA' : ∀ i, IsCompact (A' i) :=
    fun i => hA_compact (idx i).val

  -- No reflection needed, orientation is always above
  let φ_final : Fin k → E (m + 1) ≃ₗᵢ[ℝ] E (m + 1) := φ'
  let g_final : Fin k → (E m → ℝ) := g'

  have hg_final : ∀ i, LipschitzWith (L' i) (g_final i) := hg'
  have hA_final : ∀ i, IsCompact (A' i) := hA'

  have h_patch_eq : ∀ i,
      (φ_final i).symm '' (graphMap (g_final i) '' (A' i)) =
      (φ' i).symm '' (graphMap (g' i) '' (A' i)) := by
    intro i; rfl

  have h_cover_final : S ⊆ ⋃ i : Fin k,
      (φ_final i).symm '' (graphMap (g_final i) '' (A' i)) := by
    intro x hx
    have h_x_in_union : x ∈ ⋃ p ∈ t, N p := ht_cover hx
    have h_exists_p : ∃ (p : S), p ∈ t ∧ x ∈ N p := by
      simpa using h_x_in_union
    rcases h_exists_p with ⟨pS, hp_t, hp_N⟩
    let i : Fin k := idx.symm ⟨pS, hp_t⟩
    have h_idx_val : (idx i).val = pS := by
      simp [i] <;> rfl
    have h_x_in_patch : x ∈ (φ' i).symm '' (graphMap (g' i) '' (A' i)) := by
      have h : N pS ∩ S ⊆ (φ' i).symm '' (graphMap (g' i) '' (A' i)) := by
        simpa [φ', g', A', h_idx_val] using h_cover_patch pS
      exact h ⟨hp_N, hx⟩
    have h_final_patch : x ∈ (φ_final i).symm '' (graphMap (g_final i) '' (A' i)) := by
      rw [h_patch_eq i]
      exact h_x_in_patch
    exact Set.mem_iUnion.mpr ⟨i, h_final_patch⟩

  have h_patch_subset_final : ∀ i,
      (φ_final i).symm '' (graphMap (g_final i) '' (A' i)) ⊆ frontier V := by
    intro i
    rw [h_patch_eq i, h_frontier]
    intro y hy
    rcases hy with ⟨w, hw_in_graph, rfl⟩
    rcases hw_in_graph with ⟨z : E m, hz : z ∈ A' i, rfl⟩
    have h_eq : f ((φ' i).symm (graphMap (g' i) z)) = 0 :=
      h_patch_level (idx i).val z hz
    have h_uz : u ((φ' i).symm (graphMap (g' i) z)) = s := by linarith
    exact h_uz

  have h_cover_frontier : frontier V ⊆ ⋃ i : Fin k,
      (φ_final i).symm '' (graphMap (g_final i) '' (A' i)) := by
    rw [h_frontier]
    exact h_cover_final

  -- Orientation: since bridge always gives above=true and φ_final=φ', g_final=g',
  -- the chosen h_orient_patch already gives exactly the required equation
  have h_orient_final : ∀ i (z : E m), z ∈ A' i →
      ∃ (r : ℝ), 0 < r ∧
        ball (graphMap (g_final i) z) r ∩ ((φ_final i) '' V) =
        ball (graphMap (g_final i) z) r ∩
          {q | q (Fin.last m) > g_final i (proj q)} := by
    intro i z hz
    let pS : S := (idx i).val
    rcases h_orient_patch pS z hz with ⟨r, hr_pos, h_eq⟩
    refine' ⟨r, hr_pos, _⟩
    have hφ : φ_final i = φ' i := by rfl
    have hg : g_final i = g' i := by rfl
    rw [hφ, hg]
    exact h_eq

  -- ========================================================================
  -- Disjointification: subtract relative interiors, pairwise intersections null
  -- ========================================================================

  let P (i : Fin k) : Set (E (m + 1)) :=
    (φ_final i).symm '' (graphMap (g_final i) '' (A' i))
  let h (i : Fin k) : E m → E (m + 1) :=
    fun z => (φ_final i).symm (graphMap (g_final i) z)
  let N' (i : Fin k) : Set (E (m + 1)) := N (idx i).val

  have hA_ball' : ∀ i, IsClosedBall (A' i) := fun i => hA_ball (idx i).val

  -- Helper: graphMap of a continuous function is continuous
  have h_graphMap_cont : ∀ (g : E m → ℝ), Continuous g → Continuous (graphMap g) := by
    intro g hg
    have h1 : Continuous (fun (y : E m) (i : Fin (m + 1)) =>
        if h : i.val < m then y ⟨i.val, h⟩ else g y) := by
      apply continuous_pi
      intro i
      by_cases h : i.val < m
      · let j : Fin m := ⟨i.val, h⟩
        have h_if : (fun (y : E m) => (if h2 : i.val < m then y ⟨i.val, h2⟩ else g y)) =
              (fun (y : E m) => y j) := by
          funext y
          have h_pos : i.val < m := h
          rw [dif_pos h_pos]
          <;> congr <;> exact Fin.ext rfl
        rw [h_if]
        exact (EuclideanSpace.proj j : E m →L[ℝ] ℝ).continuous
      · have h_if : (fun (y : E m) => (if h2 : i.val < m then y ⟨i.val, h2⟩ else g y)) = g := by
          funext y; simp [h]
        rw [h_if]
        exact hg
    exact (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp h1

  -- P i is compact
  have hP_compact : ∀ i, IsCompact (P i) := by
    intro i
    have h1 : IsCompact (A' i) := hA_final i
    have hg_cont : Continuous (g_final i) := (hg_final i).continuous
    have h2 : Continuous (graphMap (g_final i)) := h_graphMap_cont (g_final i) hg_cont
    have h3 : IsCompact (graphMap (g_final i) '' (A' i)) := h1.image h2
    have h4 : Continuous (φ_final i).symm := (φ_final i).symm.continuous
    exact h3.image h4

  -- h i is injective
  have h_inj : ∀ i, Function.Injective (h i) := by
    intro i z1 z2 h_eq
    have h5 : graphMap (g_final i) z1 = graphMap (g_final i) z2 :=
      (φ_final i).symm.injective h_eq
    have h6 : z1 = z2 := by
      have h7 : proj (graphMap (g_final i) z1) = proj (graphMap (g_final i) z2) := by rw [h5]
      rw [graphMap_proj (g_final i) z1, graphMap_proj (g_final i) z2] at h7
      exact h7
    exact h6

  -- h i is continuous
  have h_cont : ∀ i, Continuous (h i) := by
    intro i
    have hg_cont : Continuous (g_final i) := (hg_final i).continuous
    have h1 : Continuous (graphMap (g_final i)) := h_graphMap_cont (g_final i) hg_cont
    exact (φ_final i).symm.continuous.comp h1

  -- h i '' interior(A' i) ⊆ N' i
  have h_graph_int : ∀ i, h i '' interior (A' i) ⊆ N' i := by
    intro i
    let pS : S := (idx i).val
    have hint := h_interior pS
    have h_eq1 : h i '' interior (A' i) = (φ pS).symm '' (graphMap (g pS) '' interior (A pS)) := by
      have h_h : (h i) = (φ pS).symm ∘ graphMap (g pS) := by
        funext z
        simp [h, φ_final, g_final] <;> rfl
      have h_A : A' i = A pS := by rfl
      have h_right : (φ pS).symm '' (graphMap (g pS) '' interior (A pS)) =
          ((φ pS).symm ∘ graphMap (g pS)) '' interior (A pS) := by
        exact Set.image_image _ _ _
      rw [h_right, ←h_h, h_A]
    rw [h_eq1]
    exact hint

  -- N' i ∩ S ⊆ P i
  have h_N_cover : ∀ i, N' i ∩ S ⊆ P i := by
    intro i
    let pS : S := (idx i).val
    have hcov := h_cover_patch pS
    simpa [φ_final, g_final, A', P, N'] using hcov

  -- Relative interior of P within S: {x ∈ S | ∃ open U, x ∈ U, U ∩ S ⊆ P}
  let rel_int (P S : Set (E (m + 1))) : Set (E (m + 1)) :=
    {x | x ∈ S ∧ ∃ (U : Set (E (m + 1))), IsOpen U ∧ x ∈ U ∧ U ∩ S ⊆ P}

  have h_rel_int_sub_P : ∀ P S, rel_int P S ⊆ P := by
    intro P S x hx
    have hxs : x ∈ S := hx.1
    rcases hx.2 with ⟨U, hU_open, hxU, h_sub⟩
    exact h_sub ⟨hxU, hxs⟩

  have h_rel_int_rel_open : ∀ P S, ∃ (V : Set (E (m + 1))), IsOpen V ∧ rel_int P S = S ∩ V := by
    intro P S
    let V : Set (E (m + 1)) := ⋃ (U : Set (E (m + 1))) (_ : IsOpen U ∧ U ∩ S ⊆ P), U
    have hV_open : IsOpen V := isOpen_iUnion (fun U => isOpen_iUnion (fun h => h.1))
    have h_eq : rel_int P S = S ∩ V := by
      ext x
      simp only [rel_int, Set.mem_setOf_eq, Set.mem_inter_iff]
      <;> constructor
      · rintro ⟨hxs, U, hU_open, hxU, h_sub⟩
        have h_in_V : x ∈ V := by
          apply Set.mem_iUnion.mpr
          exact ⟨U, Set.mem_iUnion.mpr ⟨⟨hU_open, h_sub⟩, hxU⟩⟩
        exact ⟨hxs, h_in_V⟩
      · rintro ⟨hxs, h_in_V⟩
        rcases Set.mem_iUnion.mp h_in_V with ⟨U, h_in_inner⟩
        rcases Set.mem_iUnion.mp h_in_inner with ⟨h, hxU⟩
        exact ⟨hxs, U, h.1, hxU, h.2⟩
    exact ⟨V, hV_open, h_eq⟩

  -- h i '' interior(A' i) ⊆ rel_int(P i) S
  have h_int_sub : ∀ i, h i '' interior (A' i) ⊆ rel_int (P i) S := by
    intro i x hx
    rcases hx with ⟨z, hz, rfl⟩
    have h1 : h i z ∈ N' i := h_graph_int i ⟨z, hz, rfl⟩
    have hP_eq : P i = h i '' A' i := by simp [P, h, Set.image_image] <;> rfl
    have h3 : h i z ∈ P i := by
      rw [hP_eq]; exact ⟨z, interior_subset hz, rfl⟩
    have h4 : h i z ∈ frontier V := h_patch_subset_final i h3
    have h5 : h i z ∈ S := by
      have h6 : frontier V = S := h_frontier
      rw [h6] at h4; exact h4
    have h6 : N' i ∩ S ⊆ P i := h_N_cover i
    exact ⟨h5, N' i, hN_open (idx i).val, h1, h6⟩

  -- Relative interiors of earlier patches
  let R_int (i : Fin k) : Set (E (m + 1)) :=
    ⋃ j ∈ Finset.Iio i, rel_int (P j) S

  -- Choose ambient open Vj for each patch's relative interior
  have h1_global : ∀ (j : Fin k), ∃ (V : Set (E (m + 1))), IsOpen V ∧ rel_int (P j) S = S ∩ V :=
    fun j => h_rel_int_rel_open (P j) S
  choose Vj hVj_open hVj_eq using h1_global

  -- R_int i is relatively open in S: union of ambient open Vj
  have hR_int_rel_open : ∀ i, ∃ (V : Set (E (m + 1))), IsOpen V ∧ R_int i = S ∩ V := by
    intro i
    let W : Set (E (m + 1)) := ⋃ j ∈ Finset.Iio i, Vj j
    have hW_open : IsOpen W := isOpen_biUnion (fun j _ => hVj_open j)
    have h_eq : R_int i = S ∩ W := by
      ext x
      have h_unfold_R : x ∈ R_int i ↔ ∃ j ∈ Finset.Iio i, x ∈ rel_int (P j) S := by
        simp [R_int]
        <;> aesop
      have h_unfold_W : x ∈ W ↔ ∃ j ∈ Finset.Iio i, x ∈ Vj j := by
        simp [W]
        <;> aesop
      constructor
      · intro hx
        rcases (h_unfold_R.mp hx) with ⟨j, hj, hxj⟩
        have h2 : x ∈ S ∩ Vj j := by
          rw [←hVj_eq j]
          exact hxj
        have h5 : x ∈ W := h_unfold_W.mpr ⟨j, hj, h2.2⟩
        exact ⟨h2.1, h5⟩
      · rintro ⟨hxs, hxW⟩
        rcases (h_unfold_W.mp hxW) with ⟨j, hj, hxj⟩
        have h2 : x ∈ S ∩ Vj j := ⟨hxs, hxj⟩
        have h3 : x ∈ rel_int (P j) S := by
          rw [hVj_eq j]
          exact h2
        exact h_unfold_R.mpr ⟨j, hj, h3⟩
    exact ⟨W, hW_open, h_eq⟩
  choose V_amb hV_amb_open hV_amb_eq using hR_int_rel_open

  -- A_new i = A' i \ (h i) ⁻¹' (V_amb i) — compact since V_amb i is open
  let A_new (i : Fin k) : Set (E m) := A' i \ (h i) ⁻¹' (V_amb i)

  have hA_new_sub : ∀ i, A_new i ⊆ A' i := by
    intro i
    intro x hx
    exact hx.1

  have hA_new_compact : ∀ i, IsCompact (A_new i) := by
    intro i
    have h1 : IsOpen ((h i) ⁻¹' (V_amb i)) := (hV_amb_open i).preimage (h_cont i)
    have h2 : IsClosed (((h i) ⁻¹' (V_amb i))ᶜ) := h1.isClosed_compl
    have h3 : A_new i = A' i ∩ ((h i) ⁻¹' (V_amb i))ᶜ := by
      simp [A_new, Set.diff_eq] <;> rfl
    rw [h3]
    exact (hA_final i).inter_right h2

  let Q (i : Fin k) : Set (E (m + 1)) := h i '' A_new i

  -- P i = h i '' A' i
  have hP_eq : ∀ i, P i = h i '' A' i := by
    intro i
    simp [P, h, Set.image_image] <;> rfl

  -- Q i = P i \ R_int i
  have hQ_eq : ∀ i, Q i = P i \ R_int i := by
    intro i
    have h_img_diff : h i '' (A' i \ (h i) ⁻¹' (V_amb i)) =
        (h i '' A' i) \ (h i '' ((h i) ⁻¹' (V_amb i))) :=
      Set.image_diff (h_inj i) (A' i) ((h i) ⁻¹' (V_amb i))
    have h_preimg : h i '' ((h i) ⁻¹' (V_amb i)) = V_amb i ∩ Set.range (h i) :=
      Set.image_preimage_eq_inter_range
    have h_sub_range : (h i '' A' i) ⊆ Set.range (h i) :=
      Set.image_subset_range (h i) (A' i)
    have h4 : (h i '' A' i) \ (V_amb i ∩ Set.range (h i)) = (h i '' A' i) \ V_amb i := by
      ext y
      simp only [Set.mem_diff, Set.mem_inter_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hV => h2 ⟨hV, h_sub_range h1⟩⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h_and => h2 h_and.1⟩
    have h5 : (h i '' A' i) \ V_amb i = P i \ V_amb i := by
      rw [hP_eq i]
    have h7 : P i ⊆ S := by
      have h8 : P i ⊆ frontier V := h_patch_subset_final i
      rw [h_frontier] at h8
      exact h8
    have h6 : P i \ V_amb i = P i \ R_int i := by
      ext y
      simp only [Set.mem_diff]
      constructor
      · intro hy
        have h9 : y ∈ P i := hy.1
        have h10 : y ∉ V_amb i := hy.2
        have h11 : y ∉ R_int i := by
          rw [hV_amb_eq i]
          intro h12
          exact h10 h12.2
        exact ⟨h9, h11⟩
      · intro hy
        have h9 : y ∈ P i := hy.1
        have h10 : y ∉ R_int i := hy.2
        have h11 : y ∉ V_amb i := by
          intro h12
          have h13 : y ∈ S := h7 h9
          have h14 : y ∈ R_int i := by
            rw [hV_amb_eq i]
            exact ⟨h13, h12⟩
          exact h10 h14
        exact ⟨h9, h11⟩
    calc Q i
      = h i '' (A' i \ (h i) ⁻¹' (V_amb i)) := by rfl
    _ = (h i '' A' i) \ (h i '' ((h i) ⁻¹' (V_amb i))) := h_img_diff
    _ = (h i '' A' i) \ (V_amb i ∩ Set.range (h i)) := by rw [h_preimg]
    _ = (h i '' A' i) \ V_amb i := h4
    _ = P i \ V_amb i := h5
    _ = P i \ R_int i := h6

  -- Cover: smallest index with x ∈ P i gives x ∈ Q i
  have h_cover_new : S ⊆ ⋃ i : Fin k, Q i := by
    classical
    intro x hx
    have h_in_P : x ∈ ⋃ i : Fin k, P i := by
      have h_x_f : x ∈ frontier V := by
        rw [h_frontier]
        exact hx
      exact h_cover_frontier h_x_f
    rcases Set.mem_iUnion.mp h_in_P with ⟨i, hi⟩
    let I : Finset (Fin k) := Finset.filter (fun j => x ∈ P j) Finset.univ
    have hi_in : i ∈ I := by
      rw [Finset.mem_filter] <;> exact ⟨Finset.mem_univ i, hi⟩
    have hI_nonempty : I.Nonempty := ⟨i, hi_in⟩
    let j0 := Finset.min' I hI_nonempty
    have hj0_in : j0 ∈ I := Finset.min'_mem I hI_nonempty
    have hx_Pj0 : x ∈ P j0 := (Finset.mem_filter.mp hj0_in).2
    have h_min : ∀ l < j0, x ∉ P l := by
      intro l hl
      by_contra hxl
      have h_l_in_I : l ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ l, hxl⟩
      have h_le : j0 ≤ l := Finset.min'_le I l h_l_in_I
      exact not_le.mpr hl h_le
    have hx_not_Rint : x ∉ R_int j0 := by
      simp only [R_int, Set.mem_iUnion, Finset.mem_Iio]
      intro h
      rcases h with ⟨l, hl, hxl⟩
      have h9 : x ∈ P l := h_rel_int_sub_P (P l) S hxl
      exact h_min l hl h9
    have hx_Q : x ∈ Q j0 := by
      rw [hQ_eq j0]
      exact ⟨hx_Pj0, hx_not_Rint⟩
    exact Set.mem_iUnion.mpr ⟨j0, hx_Q⟩

  -- Null pairwise intersections: Q i ∩ Q j ⊆ h i '' frontier(A' i)
  have h_null_inter : ∀ (i j : Fin k), i ≠ j → μHE[m] (Q i ∩ Q j) = 0 := by
    have h_main : ∀ (i j : Fin k), i < j → μHE[m] (Q i ∩ Q j) = 0 := by
      intro i j h_lt
      have h1 : Q i ∩ Q j ⊆ P i \ rel_int (P i) S := by
        intro x hx
        have hxi : x ∈ Q i := hx.1
        have hxj : x ∈ Q j := hx.2
        have h2 : x ∈ P i := (hQ_eq i ▸ hxi).1
        have h3 : x ∉ R_int j := (hQ_eq j ▸ hxj).2
        have h4 : rel_int (P i) S ⊆ R_int j := by
          intro x hx
          have h6 : x ∈ R_int j := by
            dsimp only [R_int]
            simpa using ⟨i, h_lt, hx⟩
          exact h6
        exact ⟨h2, fun h5 => h3 (h4 h5)⟩
      have h5 : P i \ rel_int (P i) S ⊆ h i '' frontier (A' i) := by
        have hP_eq : P i = h i '' A' i := by
          simp [P, h, Set.image_image] <;> rfl
        intro x hx
        have h6 : x ∈ P i := hx.1
        have h7 : x ∉ rel_int (P i) S := hx.2
        have h8 : x ∉ h i '' interior (A' i) := by
          intro h9
          exact h7 (h_int_sub i h9)
        rw [hP_eq] at h6
        rcases h6 with ⟨z, hz, h_eq⟩
        have h10 : z ∉ interior (A' i) := by
          intro h11
          have h12 : h i z ∈ h i '' interior (A' i) := ⟨z, h11, rfl⟩
          rw [h_eq] at h12
          exact h8 h12
        have h13 : z ∈ frontier (A' i) := by
          have h_closed : IsClosed (A' i) := (hA_final i).isClosed
          have h_frontier_eq : frontier (A' i) = (A' i) \ interior (A' i) :=
            IsClosed.frontier_eq h_closed
          rw [h_frontier_eq]
          exact ⟨hz, h10⟩
        exact ⟨z, h13, h_eq⟩
      have h14 : μHE[m] (h i '' frontier (A' i)) = 0 := by
        rcases (hA_ball' i).proof with ⟨c, r, hAr⟩
        have h_frontier_A : frontier (A' i) = sphere c r := by
          rw [hAr]; exact frontier_closedBall' c r
        -- μHE[m] of sphere in E m is zero (equals volume)
        have h_vol_domain : μHE[m] (frontier (A' i)) = 0 := by
          have h_eq_vol : (μHE[m] : Measure (E m)) = volume :=
            EuclideanSpace.euclideanHausdorffMeasure_eq_volume (d := m)
          rw [h_eq_vol, hAr]
          exact volume_frontier_closedBall_zero
        -- μHE ↔ μH null equivalence
        have h_scalar_ne_zero : (MeasureTheory.Measure.addHaarScalarFactor
            (volume : Measure (E m)) (MeasureTheory.Measure.hausdorffMeasure (m : ℝ))) ≠ 0 :=
          MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero m
        have h_iff : ∀ (s : Set (E m)), μHE[m] s = 0 ↔
            MeasureTheory.Measure.hausdorffMeasure (m : ℝ) s = 0 := by
          intro s
          simp [MeasureTheory.Measure.euclideanHausdorffMeasure_def, h_scalar_ne_zero]
          <;> tauto
        have hH_null : MeasureTheory.Measure.hausdorffMeasure (m : ℝ) (frontier (A' i)) = 0 :=
          (h_iff (frontier (A' i))).mp h_vol_domain
        -- h i is Lipschitz (graphMap then isometry)
        have h_graphMap_dist : ∀ (z1 z2 : E m),
            dist (graphMap (g_final i) z1) (graphMap (g_final i) z2) ≤ ↑(L' i + 1) * dist z1 z2 := by
          intro z1 z2
          have h2 : ‖graphMap (g_final i) z1 - graphMap (g_final i) z2‖ ^ 2 =
              ‖z1 - z2‖ ^ 2 + (g_final i z1 - g_final i z2) ^ 2 :=
            graphMap_norm_sq (g_final i) z1 z2
          have h3 : |g_final i z1 - g_final i z2| ≤ (L' i : ℝ) * ‖z1 - z2‖ :=
            (hg_final i).dist_le_mul z1 z2
          have h4 : (g_final i z1 - g_final i z2) ^ 2 ≤ (L' i : ℝ) ^ 2 * ‖z1 - z2‖ ^ 2 := by
            have h5 : (g_final i z1 - g_final i z2) ^ 2 = |g_final i z1 - g_final i z2| ^ 2 :=
              (sq_abs _).symm
            rw [h5]
            have h6 : |g_final i z1 - g_final i z2| ^ 2 ≤ ((L' i : ℝ) * ‖z1 - z2‖) ^ 2 := by gcongr
            have h7 : ((L' i : ℝ) * ‖z1 - z2‖) ^ 2 = (L' i : ℝ) ^ 2 * ‖z1 - z2‖ ^ 2 := by ring
            rw [h7] at h6
            exact h6
          have h7 : ‖graphMap (g_final i) z1 - graphMap (g_final i) z2‖ ^ 2 ≤
              ((L' i : ℝ) + 1) ^ 2 * ‖z1 - z2‖ ^ 2 := by
            rw [h2]
            have h_ineq : 1 + (L' i : ℝ) ^ 2 ≤ ((L' i : ℝ) + 1) ^ 2 := by
              have h13 : 0 ≤ (L' i : ℝ) := by positivity
              have h14 : ((L' i : ℝ) + 1) ^ 2 = (L' i : ℝ) ^ 2 + 2 * (L' i : ℝ) + 1 := by ring
              rw [h14]
              have h15 : 0 ≤ 2 * (L' i : ℝ) := by positivity
              linarith
            have h_add : ‖z1 - z2‖ ^ 2 + (g_final i z1 - g_final i z2) ^ 2 ≤
                ‖z1 - z2‖ ^ 2 + (L' i : ℝ) ^ 2 * ‖z1 - z2‖ ^ 2 :=
              add_le_add_right h4 (‖z1 - z2‖ ^ 2)
            have h_final : ‖z1 - z2‖ ^ 2 + (L' i : ℝ) ^ 2 * ‖z1 - z2‖ ^ 2 ≤
                ((L' i : ℝ) + 1) ^ 2 * ‖z1 - z2‖ ^ 2 := by
              have h16 : (1 + (L' i : ℝ) ^ 2) * ‖z1 - z2‖ ^ 2 ≤
                  ((L' i : ℝ) + 1) ^ 2 * ‖z1 - z2‖ ^ 2 := by gcongr
              have h17 : ‖z1 - z2‖ ^ 2 + (L' i : ℝ) ^ 2 * ‖z1 - z2‖ ^ 2 =
                  (1 + (L' i : ℝ) ^ 2) * ‖z1 - z2‖ ^ 2 := by ring
              rw [h17]
              exact h16
            exact le_trans h_add h_final
          have h8 : 0 ≤ ‖graphMap (g_final i) z1 - graphMap (g_final i) z2‖ := by positivity
          have h9 : 0 ≤ ((L' i : ℝ) + 1) * ‖z1 - z2‖ := by positivity
          have h10 : ‖graphMap (g_final i) z1 - graphMap (g_final i) z2‖ ≤ ((L' i : ℝ) + 1) * ‖z1 - z2‖ := by
            have h11 : ((L' i : ℝ) + 1) ^ 2 * ‖z1 - z2‖ ^ 2 =
                (((L' i : ℝ) + 1) * ‖z1 - z2‖) ^ 2 := by ring
            rw [h11] at h7
            have h12 : |‖graphMap (g_final i) z1 - graphMap (g_final i) z2‖| ≤
                |((L' i : ℝ) + 1) * ‖z1 - z2‖| := (sq_le_sq).mp h7
            rw [abs_of_nonneg h8, abs_of_nonneg h9] at h12
            exact h12
          simpa [dist_eq_norm] using h10
        have h_graphMap_lip : LipschitzWith (L' i + 1) (graphMap (g_final i)) :=
          lipschitzWith_iff_dist_le_mul.mpr h_graphMap_dist
        have h_h_lip : LipschitzWith (L' i + 1) (h i) := by
          have h_comp : LipschitzWith (1 * (L' i + 1)) ((φ_final i).symm ∘ graphMap (g_final i)) :=
            (φ_final i).symm.lipschitz.comp h_graphMap_lip
          have h_mono : LipschitzWith (L' i + 1) ((φ_final i).symm ∘ graphMap (g_final i)) :=
            LipschitzWith.weaken h_comp (by simp)
          have h_eq : (h i) = (φ_final i).symm ∘ graphMap (g_final i) := by
            funext z; rfl
          rw [h_eq]
          exact h_mono
        have hH_img : MeasureTheory.Measure.hausdorffMeasure (m : ℝ) (h i '' frontier (A' i)) ≤
            (↑(L' i + 1) : ENNReal) ^ (m : ℝ) *
            MeasureTheory.Measure.hausdorffMeasure (m : ℝ) (frontier (A' i)) :=
          h_h_lip.hausdorffMeasure_image_le (by positivity) (frontier (A' i))
        rw [hH_null] at hH_img
        have hH_img' : MeasureTheory.Measure.hausdorffMeasure (m : ℝ) (h i '' frontier (A' i)) ≤ 0 := by
          simpa [mul_zero] using hH_img
        have hH_img_null : MeasureTheory.Measure.hausdorffMeasure (m : ℝ) (h i '' frontier (A' i)) = 0 :=
          le_zero_iff.mp hH_img'
        have h_iff2 : ∀ (s : Set (E (m + 1))), μHE[m] s = 0 ↔
            MeasureTheory.Measure.hausdorffMeasure (m : ℝ) s = 0 := by
          intro s
          simp [MeasureTheory.Measure.euclideanHausdorffMeasure_def, h_scalar_ne_zero]
          <;> tauto
        exact (h_iff2 (h i '' frontier (A' i))).mpr hH_img_null
      have h15 : μHE[m] (Q i ∩ Q j) ≤ μHE[m] (h i '' frontier (A' i)) :=
        MeasureTheory.measure_mono (Set.Subset.trans h1 h5)
      rw [h14] at h15
      exact le_zero_iff.mp h15
    intro i j hne
    have h_lt : i < j ∨ j < i := by omega
    rcases h_lt with (h_ij | h_ji)
    · exact h_main i j h_ij
    · have h_comm : Q i ∩ Q j = Q j ∩ Q i := Set.inter_comm (Q i) (Q j)
      rw [h_comm]
      exact h_main j i h_ji

  -- Finite union with null pairwise intersections has measure equal to sum
  have hQ_meas : ∀ i, MeasurableSet (Q i) := by
    intro i
    have h1 : IsCompact (A_new i) := hA_new_compact i
    have h2 : Continuous (h i) := h_cont i
    have h3 : IsCompact (Q i) := h1.image h2
    exact h3.isClosed.measurableSet
  have h_ae_disj : Set.Pairwise (↑(Finset.univ : Finset (Fin k))) (fun i j => AEDisjoint μHE[m] (Q i) (Q j)) := by
    intro i _ j _ hne
    exact h_null_inter i j hne
  have hQ_nullmeas : ∀ b ∈ (Finset.univ : Finset (Fin k)), NullMeasurableSet (Q b) μHE[m] := by
    intro b _
    exact (hQ_meas b).nullMeasurableSet
  have h_univ_eq : (⋃ i : Fin k, Q i) = (⋃ b ∈ (Finset.univ : Finset (Fin k)), Q b) := by
    ext x
    simp [Set.mem_iUnion, Finset.mem_univ]
    <;> tauto
  have h_sum_eq : μHE[m] (⋃ i : Fin k, Q i) = ∑ i : Fin k, μHE[m] (Q i) := by
    have h_main := MeasureTheory.measure_biUnion_finset₀ h_ae_disj hQ_nullmeas
    rw [h_univ_eq]
    exact h_main

  -- Sum bound
  have h_sum_final : ∑ i : Fin k, μHE[m] (Q i) ≤ μHE[m] (frontier V) + ε := by
    have h_sub : (⋃ i : Fin k, Q i) ⊆ frontier V := by
      intro y hy
      rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
      have h9 : y ∈ Q i := hi
      have h10 : y ∈ P i := (hQ_eq i ▸ h9).1
      exact h_patch_subset_final i h10
    have h_le : μHE[m] (⋃ i : Fin k, Q i) ≤ μHE[m] (frontier V) :=
      MeasureTheory.measure_mono h_sub
    rw [←h_sum_eq]
    exact le_trans h_le (le_add_right (le_refl _))

  -- Orientation restricts to smaller domains
  have h_orient_new : ∀ i (z : E m), z ∈ A_new i →
      ∃ (r : ℝ), 0 < r ∧
        ball (graphMap (g_final i) z) r ∩ ((φ_final i) '' V) =
        ball (graphMap (g_final i) z) r ∩
          {q | q (Fin.last m) > g_final i (proj q)} := by
    intro i z hz
    have hz' : z ∈ A' i := hA_new_sub i hz
    exact h_orient_final i z hz'

  -- Patch subset frontier
  have h_patch_subset_new : ∀ i, Q i ⊆ frontier V := by
    intro i y hy
    have h1 : y ∈ P i := (hQ_eq i ▸ hy).1
    exact h_patch_subset_final i h1

  -- Adapt Q i to expected patch expression
  have hQ_eq2 : ∀ i, Q i = (φ_final i).symm '' (graphMap (g_final i) '' A_new i) := by
    intro i
    have hQ_def : Q i = h i '' A_new i := by rfl
    rw [hQ_def]
    have h_h_def : h i = (φ_final i).symm ∘ graphMap (g_final i) := by
      funext z; simp [h] <;> rfl
    rw [h_h_def, Set.image_image]
    <;> rfl

  -- Adapt cover to expected type
  have h_cover_final' : frontier V ⊆ ⋃ i : Fin k,
      (φ_final i).symm '' (graphMap (g_final i) '' A_new i) := by
    have h_eq1 : S = frontier V := h_frontier.symm
    rw [h_eq1] at h_cover_new
    simpa [hQ_eq2] using h_cover_new

  -- Adapt patch subset to expected type
  have h_patch_subset_final' : ∀ i, (φ_final i).symm '' (graphMap (g_final i) '' A_new i) ⊆ frontier V := by
    intro i
    have h_eq : Q i = (φ_final i).symm '' (graphMap (g_final i) '' A_new i) := hQ_eq2 i
    rw [←h_eq]
    exact h_patch_subset_new i

  -- Adapt sum bound to expected type
  have h_sum_final' : ∑ i : Fin k, μHE[m] ((φ_final i).symm '' (graphMap (g_final i) '' A_new i)) ≤
      μHE[m] (frontier (interior (closure {x | u x > s}))) + ε := by
    have h_eq_sum : ∑ i : Fin k, μHE[m] ((φ_final i).symm '' (graphMap (g_final i) '' A_new i)) =
        ∑ i : Fin k, μHE[m] (Q i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hQ_eq2 i]
    rw [h_eq_sum]
    simpa [V] using h_sum_final

  exact ⟨k, φ_final, g_final, A_new, L', hA_new_compact, hg_final,
    h_cover_final', h_orient_new, h_patch_subset_final', h_sum_final'⟩

end Geometry.Isoperimetric
