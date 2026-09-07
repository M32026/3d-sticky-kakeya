import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaSinglePatch
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory

namespace Geometry

variable {m : ℕ} [Nonempty (Fin m)]

/-!
# Coarea Single Patch — Arbitrary Direction Wrapper

Extends `coarea_single_patch` from the `eLast` direction to an arbitrary
coordinate direction `j` by conjugating with the coordinate swap
`coordSwapEquiv j`.
-/

/-- Coordinate functional for direction `j`. -/
noncomputable def coordJ (j : Fin (m + 1)) : E (m + 1) →L[ℝ] ℝ :=
  { toFun := fun x => x j
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl
    cont := by fun_prop }

/-- Projection onto hyperplane perpendicular to `e_j`. -/
noncomputable def projDir (j : Fin (m + 1)) : E (m + 1) →L[ℝ] E (m + 1) :=
  ContinuousLinearMap.id ℝ (E (m + 1)) -
  (coordJ j).smulRight (EuclideanSpace.single j (1 : ℝ))

private def swapσ (j : Fin (m + 1)) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.swap j (Fin.last m)

/-- Coordinate permutation swapping `j` and `Fin.last m`, as a linear isometry. -/
noncomputable def coordSwapEquiv (j : Fin (m + 1)) : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1) :=
  let σ := swapσ j
  let toFun : E (m + 1) → E (m + 1) := fun x =>
    WithLp.toLp 2 (x.ofLp ∘ σ)
  let invFun : E (m + 1) → E (m + 1) := fun x =>
    WithLp.toLp 2 (x.ofLp ∘ σ)
  { toFun := toFun
    invFun := invFun
    left_inv := by
      intro x
      apply WithLp.ofLp_injective (2 : ℝ≥0∞)
      funext i
      have hσ : σ (σ i) = i := by exact (Equiv.apply_eq_iff_eq_symm_apply σ).mpr rfl
      simp [toFun, invFun, Function.comp, hσ]
    right_inv := by
      intro x
      apply WithLp.ofLp_injective (2 : ℝ≥0∞)
      funext i
      have hσ : σ (σ i) = i := by exact (Equiv.apply_eq_iff_eq_symm_apply σ).mpr rfl
      simp [toFun, invFun, Function.comp, hσ]
    map_add' := by
      intro x y
      apply WithLp.ofLp_injective (2 : ℝ≥0∞)
      funext i
      simp [toFun, Function.comp] <;> rfl
    map_smul' := by
      intro c x
      apply WithLp.ofLp_injective (2 : ℝ≥0∞)
      funext i
      simp [toFun, Function.comp] <;> rfl
    norm_map' := by
      intro x
      have h4 : ‖toFun x‖ ^ 2 = ∑ i : Fin (m + 1), ((toFun x).ofLp i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq (toFun x)
      have h5 : ‖x‖ ^ 2 = ∑ i : Fin (m + 1), (x.ofLp i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq x
      have h6 : ∑ i : Fin (m + 1), ((toFun x).ofLp i) ^ 2 =
          ∑ i : Fin (m + 1), (x.ofLp (σ i)) ^ 2 := by
        apply Finset.sum_congr rfl; intro i _; rfl
      have h7 : ∑ i : Fin (m + 1), (x.ofLp (σ i)) ^ 2 = ∑ i : Fin (m + 1), (x.ofLp i) ^ 2 := by
        rw [Finset.sum_equiv σ] <;> simp
      have h8 : ‖toFun x‖ ^ 2 = ‖x‖ ^ 2 := by rw [h4, h6, h7, h5]
      have h11 : ‖toFun x‖ = ‖x‖ := by
        nlinarith [norm_nonneg (toFun x), norm_nonneg x]
      exact h11 }

lemma coordSwapEquiv_apply (j : Fin (m + 1)) (x : E (m + 1)) (k : Fin (m + 1)) :
    (coordSwapEquiv j x) k = x (swapσ j k) := by
  change (WithLp.toLp 2 (x.ofLp ∘ swapσ j)) k = x (swapσ j k)
  have h : (WithLp.toLp 2 (x.ofLp ∘ swapσ j)).ofLp = x.ofLp ∘ swapσ j := by exact Eq.symm (EqOn.comp_eq fun ⦃x_1⦄ => congrFun rfl)
  have h2 : (WithLp.toLp 2 (x.ofLp ∘ swapσ j)) k =
      (WithLp.toLp 2 (x.ofLp ∘ swapσ j)).ofLp k := by rfl
  rw [h2, h] <;> rfl

lemma coordSwapEquiv_involutive (j : Fin (m + 1)) (x : E (m + 1)) :
    coordSwapEquiv j (coordSwapEquiv j x) = x :=
  (coordSwapEquiv j).left_inv x

lemma coordSwapEquiv_last (j : Fin (m + 1)) :
    coordSwapEquiv j (EuclideanSpace.single j (1 : ℝ)) = (eLast : E (m + 1)) := by
  ext k
  rw [coordSwapEquiv_apply]
  simp [eLast, EuclideanSpace.single_apply, swapσ, Equiv.swap_apply_def]
  <;> split_ifs <;> simp_all <;> omega

lemma coordSwapEquiv_eLast (j : Fin (m + 1)) :
    coordSwapEquiv j (eLast : E (m + 1)) = EuclideanSpace.single j (1 : ℝ) := by
  ext k
  rw [coordSwapEquiv_apply]
  simp [eLast, EuclideanSpace.single_apply, swapσ, Equiv.swap_apply_def]
  <;> split_ifs <;> simp_all <;> omega

lemma coordSwapEquiv_coord_j (j : Fin (m + 1)) (y : E (m + 1)) :
    (coordSwapEquiv j y) j = y (Fin.last m) := by
  rw [coordSwapEquiv_apply]
  simp [swapσ, Equiv.swap_apply_def]
  <;> split_ifs <;> simp_all <;> omega

lemma coordSwapEquiv_coord_last (j : Fin (m + 1)) (y : E (m + 1)) :
    (coordSwapEquiv j y) (Fin.last m) = y j := by
  rw [coordSwapEquiv_apply]
  simp [swapσ, Equiv.swap_apply_def]
  <;> split_ifs <;> simp_all <;> omega

lemma coordSwapEquiv_preserves_volume (j : Fin (m + 1)) :
    MeasurePreserving (coordSwapEquiv j) volume volume :=
  (coordSwapEquiv j).measurePreserving

lemma coordSwapEquiv_preserves_hausdorff (j : Fin (m + 1)) (s : Set (E (m + 1))) :
    μHE[m] ((coordSwapEquiv j) '' s) = μHE[m] s :=
  (coordSwapEquiv j).isometry.euclideanHausdorffMeasure_image s

/-- **Coarea single patch in arbitrary coordinate direction.**

Given a patch `φ(y) = projDir j y + f y • e_j` with `∂f/∂e_j ≠ 0` on `V`,
the coarea formula holds on any compact measurable `A ⊆ V`. -/
lemma coarea_single_patch_dir
    (f : E (m + 1) → ℝ) (hf : ContDiff ℝ 1 f)
    (j : Fin (m + 1))
    (φ : OpenPartialHomeomorph (E (m + 1)) (E (m + 1)))
    (hφ_coe : (φ : E (m + 1) → E (m + 1)) =
        fun y => projDir j y + f y • EuclideanSpace.single j (1 : ℝ))
    (hφ_symm_diff : ContDiffOn ℝ 1 φ.symm φ.target)
    {V : Set (E (m + 1))}
    (hV_source : V ⊆ φ.source)
    (hV_reg : ∀ y ∈ V, (fderiv ℝ f y) (EuclideanSpace.single j (1 : ℝ)) ≠ 0)
    (A : Set (E (m + 1)))
    (hA : MeasurableSet A)
    (hA_compact : IsCompact A)
    (hA_sub : A ⊆ V) :
    ∫⁻ (t : ℝ), μHE[m] (A ∩ {y | f y = t}) =
    ∫⁻ (y : E (m + 1)) in A, ENNReal.ofReal ‖fderiv ℝ f y‖ := by
  classical
  let P := coordSwapEquiv j
  let g : E (m + 1) → ℝ := f ∘ P
  let e_j := EuclideanSpace.single j (1 : ℝ)
  let e_last := (eLast : E (m + 1))
  let P_homeo : Homeomorph (E (m + 1)) (E (m + 1)) := P.toHomeomorph
  let P_oph : OpenPartialHomeomorph (E (m + 1)) (E (m + 1)) :=
    P_homeo.toOpenPartialHomeomorph
  let φ_g : OpenPartialHomeomorph (E (m + 1)) (E (m + 1)) :=
    (P_oph.trans φ).trans P_oph.symm
  have hP_self : ∀ x, P (P x) = x := coordSwapEquiv_involutive j
  have hP_oph_source : P_oph.source = Set.univ := by simp [P_oph]
  have hP_oph_target : P_oph.target = Set.univ := by simp [P_oph]
  have hf_diff : Differentiable ℝ f := by exact ContDiff.differentiable_one hf

  -- Source inclusion: P '' V ⊆ φ_g.source
  have h_source_g : P '' V ⊆ φ_g.source := by
    intro y hy
    rcases hy with ⟨z, hzV, rfl⟩
    have h5 : P (P z) = z := hP_self z
    have h_eq1 : (P_oph.trans φ).source = P_oph.source ∩ P_oph ⁻¹' φ.source :=
      OpenPartialHomeomorph.trans_source P_oph φ
    have h_eq2 : φ_g.source = (P_oph.trans φ).source ∩ (P_oph.trans φ) ⁻¹' P_oph.symm.source :=
      OpenPartialHomeomorph.trans_source (P_oph.trans φ) P_oph.symm
    rw [h_eq2]
    have h6 : P z ∈ (P_oph.trans φ).source := by
      rw [h_eq1, hP_oph_source]
      simp
      have h_oph_eq : (P_oph : E (m + 1) → E (m + 1)) = P := by rfl
      rw [h_oph_eq]
      have h5' : P (P z) = z := h5
      rw [h5']
      exact hV_source hzV
    have h7 : (P_oph.trans φ) (P z) ∈ P_oph.symm.source := by
      have h_src : P_oph.symm.source = Set.univ := by simp [P_oph]
      rw [h_src] <;> trivial
    exact ⟨h6, h7⟩

  -- Projection identity: P (projDir j (P y)) = projHCL y
  have h_proj_id : ∀ (y : E (m + 1)), P (projDir j (P y)) = projHCL y := by
    intro y
    have h_expand : P (projDir j (P y)) =
        P (P y) - ((P y) j) • P e_j := by
      simp [projDir, coordJ, P.map_sub, P.map_smul] <;> rfl
    rw [h_expand]
    have h2 : P (P y) = y := hP_self y
    have h3 : (P y) j = y (Fin.last m) := by
      rw [coordSwapEquiv_apply]
      <;> simp [swapσ, Equiv.swap_apply_def]
    have h4 : P e_j = e_last := coordSwapEquiv_last j
    rw [h2, h3, h4] <;> rfl

  have hφ_g_form : (φ_g : E (m + 1) → E (m + 1)) =
      fun y => projHCL y + g y • e_last := by
    funext y
    have h1 : φ_g y = P (φ (P y)) := by rfl
    rw [h1, hφ_coe]
    have h_proj : P (projDir j (P y)) = projHCL y := h_proj_id y
    have h_smul : P (f (P y) • e_j) = g y • e_last := by
      have h5 : P e_j = e_last := coordSwapEquiv_last j
      have h : P (f (P y) • e_j) = f (P y) • P e_j := P.map_smul (f (P y)) e_j
      rw [h, h5] <;> rfl
    have h_add : P (projDir j (P y) + f (P y) • e_j) =
        P (projDir j (P y)) + P (f (P y) • e_j) := P.map_add _ _
    rw [h_add, h_proj, h_smul] <;> rfl

  -- Target membership: if z ∈ φ_g.target then P z ∈ φ.target
  have h_trans1_target_eq : (P_oph.trans φ).target = φ.target := by
    rw [OpenPartialHomeomorph.trans_target']
    have h9 : φ.target ∩ φ.symm ⁻¹' (φ.source ∩ P_oph.target) = φ.target := by
      rw [hP_oph_target]
      simp
      <;> intro y hy
      <;> exact φ.symm.mapsTo hy
    exact h9
  have h_mem_target : ∀ z ∈ φ_g.target, P z ∈ φ.target := by
    intro z hz
    have h_eq4 : φ_g.target = P_oph.symm.target ∩ P_oph.symm.symm ⁻¹' (P_oph.symm.source ∩ (P_oph.trans φ).target) :=
      OpenPartialHomeomorph.trans_target' (P_oph.trans φ) P_oph.symm
    rw [h_eq4] at hz
    rcases hz with ⟨_, h8⟩
    simp [hP_oph_source, hP_oph_target, h_trans1_target_eq] at h8 ⊢
    <;> exact h8

  have hφ_g_symm_diff : ContDiffOn ℝ 1 φ_g.symm φ_g.target := by
    have h_eq : (φ_g.symm : E (m + 1) → E (m + 1)) = fun z => P (φ.symm (P z)) := by rfl
    rw [h_eq]
    have hP_cdiff : ContDiff ℝ 1 P := P.contDiff
    have h_inner : ContDiffOn ℝ 1 (φ.symm ∘ P) φ_g.target :=
      hφ_symm_diff.comp hP_cdiff.contDiffOn h_mem_target
    exact hP_cdiff.contDiffOn.comp h_inner (fun _ _ => Set.mem_univ _)

  have hV_reg_g : ∀ y ∈ P '' V, (fderiv ℝ g y) e_last ≠ 0 := by
    intro y hy
    rcases hy with ⟨z, hzV, rfl⟩
    have hg_fderiv : fderiv ℝ g (P z) =
        (fderiv ℝ f z).comp P.toContinuousLinearMap := by
      let P_clm : E (m + 1) →L[ℝ] E (m + 1) := P.toContinuousLinearMap
      have hP_eq : (P : E (m + 1) → E (m + 1)) = P_clm := by rfl
      have h2 : fderiv ℝ (f ∘ P) (P z) =
          (fderiv ℝ f (P (P z))).comp (fderiv ℝ P (P z)) :=
        fderiv_comp (P z) (hf_diff.differentiableAt) (P.differentiableAt)
      have h3 : P (P z) = z := hP_self z
      have h4 : fderiv ℝ P (P z) = P_clm := by
        rw [hP_eq]
        exact P_clm.hasFDerivAt.fderiv
      rw [h2, h3, h4] <;> rfl
    rw [hg_fderiv]
    have h5 : P e_last = e_j := coordSwapEquiv_eLast j
    simpa [h5, ContinuousLinearMap.comp_apply] using hV_reg z hzV

  have hPA_compact : IsCompact (P '' A) := hA_compact.image P.continuous
  have hPA_meas : MeasurableSet (P '' A) := hPA_compact.measurableSet
  have hPA_sub : P '' A ⊆ P '' V := by
    intro x hx
    rcases hx with ⟨y, hyA, rfl⟩
    exact ⟨y, hA_sub hyA, rfl⟩
  have hg_cdiff : ContDiff ℝ 1 g := hf.comp P.contDiff

  have h_main := coarea_single_patch g hg_cdiff φ_g hφ_g_form hφ_g_symm_diff
    (hV_source := h_source_g) (hV_reg := hV_reg_g)
    (P '' A) hPA_meas hPA_compact hPA_sub

  -- Level set equality
  have h_level_eq : ∀ (t : ℝ), (P '' A) ∩ {y | g y = t} = P '' (A ∩ {y | f y = t}) := by
    intro t
    ext z
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨y, hyA, rfl⟩, hgt⟩
      have h_eq : g (P y) = f y := by
        simp [g, hP_self]
      have hyt : f y = t := by
        rw [←h_eq] <;> exact hgt
      exact ⟨y, ⟨hyA, hyt⟩, rfl⟩
    · rintro ⟨y, ⟨hyA, hyft⟩, rfl⟩
      have h_eq : g (P y) = f y := by
        simp [g, hP_self]
      have hgt : g (P y) = t := by
        rw [h_eq] <;> exact hyft
      exact ⟨⟨y, hyA, rfl⟩, hgt⟩

  have h_lhs : ∫⁻ (t : ℝ), μHE[m] ((P '' A) ∩ {y | g y = t}) =
      ∫⁻ (t : ℝ), μHE[m] (A ∩ {y | f y = t}) := by
    have h6 : ∀ t, μHE[m] ((P '' A) ∩ {y | g y = t}) =
        μHE[m] (A ∩ {y | f y = t}) := by
      intro t
      rw [h_level_eq t]
      exact coordSwapEquiv_preserves_hausdorff j (A ∩ {y | f y = t})
    rw [lintegral_congr h6]

  -- RHS: change of variables via measure preservation
  let F : E (m + 1) → ENNReal := fun y => ENNReal.ofReal ‖fderiv ℝ f y‖
  have h7 : ∀ y, ‖fderiv ℝ g y‖ = ‖fderiv ℝ f (P y)‖ := by
    intro y
    have h8 : fderiv ℝ g y = (fderiv ℝ f (P y)).comp P.toContinuousLinearMap := by
      let P_clm : E (m + 1) →L[ℝ] E (m + 1) := P.toContinuousLinearMap
      have hP_eq : (P : E (m + 1) → E (m + 1)) = P_clm := by rfl
      have h2 : fderiv ℝ (f ∘ P) y =
          (fderiv ℝ f (P y)).comp (fderiv ℝ P y) :=
        fderiv_comp y (hf_diff.differentiableAt) (P.differentiableAt)
      have h4 : fderiv ℝ P y = P_clm := by
        rw [hP_eq]
        exact P_clm.hasFDerivAt.fderiv
      rw [h2, h4] <;> rfl
    rw [h8]
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv (fderiv ℝ f (P y)) P

  have h_rhs : ∫⁻ (y : E (m + 1)) in P '' A, ENNReal.ofReal ‖fderiv ℝ g y‖ =
      ∫⁻ (y : E (m + 1)) in A, F y := by
    -- Step 1: replace g derivative with F(P y)
    have h9 : ∫⁻ (y : E (m + 1)) in P '' A, ENNReal.ofReal ‖fderiv ℝ g y‖ =
        ∫⁻ (y : E (m + 1)) in P '' A, F (P y) := by
      rw [lintegral_congr (fun y => by
        have h10 : ENNReal.ofReal ‖fderiv ℝ g y‖ = F (P y) := by
          rw [h7 y] <;> rfl
        exact h10)]
    rw [h9]
    -- Step 2: change of variables P
    have h10 : MeasurePreserving P volume volume := coordSwapEquiv_preserves_volume j
    let h : E (m + 1) → ENNReal := fun a => Set.indicator (P '' A) (fun a => F (P a)) a
    have h11 : ∫⁻ a, h a = ∫⁻ a, h (P a) :=
      h10.lintegral_map_equiv h P.toMeasurableEquiv
    have h12 : ∀ (a : E (m + 1)), h (P a) = Set.indicator A F a := by
      intro a
      simp only [h, Set.indicator_apply]
      have h_mem1 : P a ∈ P '' A ↔ a ∈ A := by
        constructor
        · rintro ⟨y, hy, h_eq⟩
          have h_inj : y = a := P.injective h_eq
          rw [h_inj] at hy
          exact hy
        · intro ha
          exact ⟨a, ha, rfl⟩
      rw [h_mem1]
      <;> rw [hP_self a]
    have h13 : ∫⁻ a, h a = ∫⁻ a, Set.indicator A F a := by
      rw [h11, lintegral_congr h12]
    have h14 : ∫⁻ a in P '' A, F (P a) = ∫⁻ a, h a := by
      rw [← lintegral_indicator hPA_meas (fun a => F (P a))]
      <;> rfl
    have h15 : ∫⁻ a in A, F a = ∫⁻ a, Set.indicator A F a := by
      rw [← lintegral_indicator hA F] <;> rfl
    rw [h14, h13, h15]

  rw [h_lhs, h_rhs] at h_main
  exact h_main

end Geometry
