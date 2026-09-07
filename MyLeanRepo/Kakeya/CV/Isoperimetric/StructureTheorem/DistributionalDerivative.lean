import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.SignedRieszRepresentation
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterVariation
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ZeroAtInfty CompactlySupported ContDiff

namespace Geometry.Perimeter

variable {n : ℕ}

-- ============================================================================
-- Analytic foundation: signed Riesz representation for ∂_i χ_S
-- ============================================================================

/-- Helper: a smooth compactly supported function has integrable directional derivative over any set. -/
lemma directionalDerivative_integrable {S : Set (E n)} {ψ : E n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ) (v : E n) :
    Integrable (fun x : E n => fderiv ℝ ψ x v) (volume.restrict S) := by
  have h1 : HasCompactSupport (fun x : E n => fderiv ℝ ψ x v) :=
    hsupp.fderiv_apply (𝕜 := ℝ) v
  let eval_v : (E n →L[ℝ] ℝ) →L[ℝ] ℝ :=
    { toFun := fun g => g v
      map_add' := by intro a b; rfl
      map_smul' := by intro c a; rfl }
  have hcont : Continuous (fun x : E n => fderiv ℝ ψ x v) :=
    eval_v.continuous.comp (hψ.continuous_fderiv (by norm_num))
  exact hcont.integrable_of_hasCompactSupport h1

/-- **Representation of the distributional derivative by a signed measure.** -/
theorem distributionalDerivative_signedMeasure (S : Set (E n)) (i : Fin n)
    (hfin : perimeter S < ⊤) :
    ∃ (μ_i : SignedMeasure (E n)),
      (∀ (ψ : E n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ),
        (∫ x in S, fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) =
          (∫ x, ψ x ∂μ_i.toJordanDecomposition.posPart) -
          (∫ x, ψ x ∂μ_i.toJordanDecomposition.negPart)) ∧
      (μ_i.totalVariation Set.univ ≤ perimeter S) := by
  let C : ℝ := (perimeter S).toReal
  have hC : 0 ≤ C := by positivity
  let e_i : E n := EuclideanSpace.single i (1 : ℝ)

  let smoothCc : Submodule ℝ (C_c(E n, ℝ)) :=
    { carrier := {f | ContDiff ℝ ∞ (f : E n → ℝ)}
      zero_mem' := by
        change ContDiff ℝ ∞ ((0 : C_c(E n, ℝ)) : E n → ℝ)
        have h : ((0 : C_c(E n, ℝ)) : E n → ℝ) = fun (_ : E n) => (0 : ℝ) := by
          funext x; simp
        rw [h]; exact contDiff_const
      add_mem' := by
        intro f g hf hg
        change ContDiff ℝ ∞ ((f + g : C_c(E n, ℝ)) : E n → ℝ)
        have hf' : ContDiff ℝ ∞ (f : E n → ℝ) := hf
        have hg' : ContDiff ℝ ∞ (g : E n → ℝ) := hg
        have h : ContDiff ℝ ∞ ((f : E n → ℝ) + (g : E n → ℝ)) := hf'.add hg'
        exact h
      smul_mem' := by
        intro c f hf
        change ContDiff ℝ ∞ ((c • f : C_c(E n, ℝ)) : E n → ℝ)
        have hf' : ContDiff ℝ ∞ (f : E n → ℝ) := hf
        have h : ContDiff ℝ ∞ (c • (f : E n → ℝ)) := hf'.const_smul c
        exact h }

  have get_diff : ∀ (ψ : smoothCc), ContDiff ℝ ∞ ((ψ : C_c(E n, ℝ)) : E n → ℝ) := by
    intro ψ; exact ψ.prop
  have get_supp : ∀ (ψ : smoothCc), HasCompactSupport ((ψ : C_c(E n, ℝ)) : E n → ℝ) := by
    intro ψ; exact (ψ : C_c(E n, ℝ)).hasCompactSupport'

  let L0 : smoothCc →ₗ[ℝ] ℝ :=
    { toFun := fun ψ => ∫ x in S, fderiv ℝ ((ψ : C_c(E n, ℝ)) : E n → ℝ) x e_i
      map_add' := by
        intro ψ₁ ψ₂
        let f1 := (ψ₁ : C_c(E n, ℝ))
        let f2 := (ψ₂ : C_c(E n, ℝ))
        have h1 : Integrable (fun x : E n => fderiv ℝ (f1 : E n → ℝ) x e_i) (volume.restrict S) :=
          directionalDerivative_integrable (get_diff ψ₁) (get_supp ψ₁) e_i
        have h2 : Integrable (fun x : E n => fderiv ℝ (f2 : E n → ℝ) x e_i) (volume.restrict S) :=
          directionalDerivative_integrable (get_diff ψ₂) (get_supp ψ₂) e_i
        have h_coe : ((ψ₁ + ψ₂ : smoothCc) : C_c(E n, ℝ)) = f1 + f2 := by rfl
        simp only [h_coe]
        have hdiff1 : Differentiable ℝ (f1 : E n → ℝ) := (get_diff ψ₁).differentiable (by norm_num)
        have hdiff2 : Differentiable ℝ (f2 : E n → ℝ) := (get_diff ψ₂).differentiable (by norm_num)
        have h_coe2 : ((f1 + f2 : C_c(E n, ℝ)) : E n → ℝ) = (f1 : E n → ℝ) + (f2 : E n → ℝ) := by rfl
        have h_eq : (fun x : E n => fderiv ℝ ((f1 + f2 : C_c(E n, ℝ)) : E n → ℝ) x e_i) =
            (fun x : E n => fderiv ℝ (f1 : E n → ℝ) x e_i + fderiv ℝ (f2 : E n → ℝ) x e_i) := by
          funext x
          have h4 : fderiv ℝ ((f1 + f2 : C_c(E n, ℝ)) : E n → ℝ) x =
              fderiv ℝ ((f1 : E n → ℝ) + (f2 : E n → ℝ)) x := by rw [h_coe2]
          rw [h4]
          have h : fderiv ℝ ((f1 : E n → ℝ) + (f2 : E n → ℝ)) x =
              fderiv ℝ (f1 : E n → ℝ) x + fderiv ℝ (f2 : E n → ℝ) x :=
            fderiv_add (hdiff1 x) (hdiff2 x)
          rw [h] <;> rfl
        rw [h_eq, integral_add h1 h2]
      map_smul' := by
        intro c ψ
        let f := (ψ : C_c(E n, ℝ))
        have hdiff : Differentiable ℝ (f : E n → ℝ) := (get_diff ψ).differentiable (by norm_num)
        have h_coe : ((c • ψ : smoothCc) : C_c(E n, ℝ)) = c • f := by rfl
        simp only [h_coe]
        have h_eq1 : ((c • f : C_c(E n, ℝ)) : E n → ℝ) = c • (f : E n → ℝ) := by rfl
        have h_eq2 : (fun x : E n => fderiv ℝ ((c • f : C_c(E n, ℝ)) : E n → ℝ) x e_i) =
            (fun x : E n => c * fderiv ℝ (f : E n → ℝ) x e_i) := by
          funext x
          have hdiff_at : DifferentiableAt ℝ (f : E n → ℝ) x := hdiff x
          have hfd : HasFDerivAt (f : E n → ℝ) (fderiv ℝ (f : E n → ℝ) x) x :=
            hdiff_at.hasFDerivAt
          have h2 : HasFDerivAt (c • (f : E n → ℝ)) (c • fderiv ℝ (f : E n → ℝ) x) x :=
            hfd.const_smul c
          have h3 : fderiv ℝ (c • (f : E n → ℝ)) x = c • fderiv ℝ (f : E n → ℝ) x := h2.fderiv
          rw [h_eq1, h3] <;> simp
        have h_integ : Integrable (fun x : E n => fderiv ℝ (f : E n → ℝ) x e_i) (volume.restrict S) :=
          directionalDerivative_integrable (get_diff ψ) (get_supp ψ) e_i
        let g := fun x : E n => fderiv ℝ (f : E n → ℝ) x e_i
        have h1 : (fun x : E n => c * g x) = fun x : E n => c • g x := by funext x; simp
        have h2 : ∫ x in S, c • g x = c • ∫ x in S, g x := by
          rw [integral_smul]
        have h_int : ∫ x in S, c * g x = c * ∫ x in S, g x := by
          rw [h1, h2] <;> simp
        have h_final : c * ∫ x in S, g x =
            c • ∫ x in S, fderiv ℝ ((ψ : C_c(E n, ℝ)) : E n → ℝ) x e_i := by
          have h3 : ∫ x in S, g x = ∫ x in S, fderiv ℝ ((ψ : C_c(E n, ℝ)) : E n → ℝ) x e_i := by rfl
          rw [h3] <;> simp
        rw [h_eq2, h_int]
        exact h_final }

  have h_bound : ∀ (ψ : smoothCc), |L0 ψ| ≤ C * ‖Cc.toC₀ (ψ : C_c(E n, ℝ))‖ := by
    intro ψ
    let ψ_cc : C_c(E n, ℝ) := ψ
    let M : ℝ := ‖Cc.toC₀ ψ_cc‖
    by_cases hM : M = 0
    · have h_eq0 : Cc.toC₀ ψ_cc = 0 := norm_eq_zero.mp hM
      have hψ0 : (ψ_cc : E n → ℝ) = 0 := by
        have h10 : (ψ_cc : E n → ℝ) = (Cc.toC₀ ψ_cc : E n → ℝ) := by rfl
        rw [h10, h_eq0] <;> rfl
      have hL0 : L0 ψ = 0 := by
        have h_fderiv_zero : (fun x : E n => fderiv ℝ (ψ_cc : E n → ℝ) x e_i) = 0 := by
          funext x; rw [hψ0] <;> simp
        have h_integral_zero : ∫ x in S, fderiv ℝ (ψ_cc : E n → ℝ) x e_i = 0 := by
          rw [h_fderiv_zero] <;> simp
        exact h_integral_zero
      rw [hL0] <;> simp [hM] <;> positivity
    · have hM_pos : 0 < M := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hM)
      let ψ' : C_c(E n, ℝ) := M⁻¹ • ψ_cc
      have hψ'_smooth : ContDiff ℝ ∞ (ψ' : E n → ℝ) := (get_diff ψ).const_smul M⁻¹
      have hψ'_norm : ‖Cc.toC₀ ψ'‖ = 1 := by
        have h1 : Cc.toC₀ ψ' = M⁻¹ • Cc.toC₀ ψ_cc := by ext x; simp [ψ'] <;> rfl
        rw [h1, norm_smul]
        have h2 : |M⁻¹| * M = 1 := by
          have h3 : 0 < M⁻¹ := by positivity
          have h4 : |M⁻¹| = M⁻¹ := abs_of_pos h3
          rw [h4]; field_simp [hM_pos.ne'] <;> ring
        exact h2
      have hψ'_bound : ∀ x, |(ψ' : E n → ℝ) x| ≤ 1 := by
        intro x
        have h1 : |(ψ' : E n → ℝ) x| ≤ ‖Cc.toC₀ ψ'‖ := by
          have h2 : (ψ' : E n → ℝ) = (Cc.toC₀ ψ' : E n → ℝ) := by rfl
          rw [h2]
          simpa [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using
            BoundedContinuousFunction.norm_coe_le_norm (Cc.toC₀ ψ').toBCF x
        rw [hψ'_norm] at h1; exact h1
      let φ : TestScalar :=
        { toFun := (ψ' : E n → ℝ), smooth := hψ'_smooth
          compact := ψ'.hasCompactSupport', bound := hψ'_bound }
      have h1 : ENNReal.ofReal |L0 ⟨ψ', hψ'_smooth⟩| ≤ directionalVariation S e_i := by
        exact le_iSup (fun (θ : TestScalar) => ENNReal.ofReal |∫ x in S, fderiv ℝ θ.toFun x e_i|) φ
      have h2 : directionalVariation S e_i ≤ perimeter S := by
        have h21 := directionalVariation_le_perimeter (S := S) (v := e_i)
        have hnorm : ‖e_i‖ = 1 := by simp [e_i, EuclideanSpace.norm_eq] <;> norm_num
        rw [hnorm] at h21; simpa using h21
      have h3 : ENNReal.ofReal |L0 ⟨ψ', hψ'_smooth⟩| ≤ perimeter S := h1.trans h2
      have h4 : |L0 ⟨ψ', hψ'_smooth⟩| ≤ C := by
        have h6 : ENNReal.ofReal C = perimeter S := by rw [ENNReal.ofReal_toReal hfin.ne]
        have h3' : ENNReal.ofReal |L0 ⟨ψ', hψ'_smooth⟩| ≤ ENNReal.ofReal C := by
          rw [h6]; exact h3
        have h_iff : ENNReal.ofReal |L0 ⟨ψ', hψ'_smooth⟩| ≤ ENNReal.ofReal C ↔
            |L0 ⟨ψ', hψ'_smooth⟩| ≤ C := ENNReal.ofReal_le_ofReal_iff hC
        exact h_iff.mp h3'
      have h5 : L0 ψ = M * L0 ⟨ψ', hψ'_smooth⟩ := by
        have h6 : (ψ : C_c(E n, ℝ)) = M • ψ' := by
          ext x; simp [ψ', smul_assoc] <;> field_simp [hM_pos.ne'] <;> ring
        have h7 : (ψ : smoothCc) = M • ⟨ψ', hψ'_smooth⟩ := by
          apply Subtype.ext; exact h6
        rw [h7, L0.map_smul] <;> simp
      rw [h5]
      have h7 : |M * L0 ⟨ψ', hψ'_smooth⟩| = M * |L0 ⟨ψ', hψ'_smooth⟩| := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ M from norm_nonneg _)]
      rw [h7]
      have h7 : M * |L0 ⟨ψ', hψ'_smooth⟩| ≤ M * C :=
        mul_le_mul_of_nonneg_left h4 (show 0 ≤ M from norm_nonneg _)
      have h8 : M * C = C * M := by ring
      rw [h8] at h7
      have h9 : M = ‖Cc.toC₀ (ψ : C_c(E n, ℝ))‖ := by rfl
      rw [h9] at h7; exact h7

  let N : C_c(E n, ℝ) → ℝ := fun f => C * ‖Cc.toC₀ f‖
  have N_hom : ∀ (c : ℝ), 0 < c → ∀ (f : C_c(E n, ℝ)), N (c • f) = c * N f := by
    intro c hc f
    have h1 : ‖Cc.toC₀ (c • f)‖ = |c| * ‖Cc.toC₀ f‖ := norm_smul c (Cc.toC₀ f)
    have h2 : |c| = c := abs_of_pos hc
    calc N (c • f) = C * ‖Cc.toC₀ (c • f)‖ := by rfl
      _ = C * (|c| * ‖Cc.toC₀ f‖) := by rw [h1]
      _ = C * (c * ‖Cc.toC₀ f‖) := by rw [h2]
      _ = c * (C * ‖Cc.toC₀ f‖) := by ring
      _ = c * N f := by rfl
  have N_add : ∀ (f g : C_c(E n, ℝ)), N (f + g) ≤ N f + N g := by
    intro f g
    have h1 : ‖Cc.toC₀ (f + g)‖ ≤ ‖Cc.toC₀ f‖ + ‖Cc.toC₀ g‖ :=
      norm_add_le (Cc.toC₀ f) (Cc.toC₀ g)
    have h2 : N (f + g) = C * ‖Cc.toC₀ (f + g)‖ := by rfl
    have h3 : N f = C * ‖Cc.toC₀ f‖ := by rfl
    have h4 : N g = C * ‖Cc.toC₀ g‖ := by rfl
    rw [h2, h3, h4]
    have h5 : C * ‖Cc.toC₀ (f + g)‖ ≤ C * (‖Cc.toC₀ f‖ + ‖Cc.toC₀ g‖) :=
      mul_le_mul_of_nonneg_left h1 hC
    have h6 : C * (‖Cc.toC₀ f‖ + ‖Cc.toC₀ g‖) = C * ‖Cc.toC₀ f‖ + C * ‖Cc.toC₀ g‖ := by ring
    rw [h6] at h5; exact h5
  have hf : ∀ (x : smoothCc), L0 x ≤ N x := by
    intro x
    have h : L0 x ≤ |L0 x| := le_abs_self (L0 x)
    have h2 : |L0 x| ≤ N x := h_bound x
    exact h.trans h2

  let f_pmap : (C_c(E n, ℝ)) →ₗ.[ℝ] ℝ :=
    { domain := smoothCc, toFun := L0 }
  have h_ext : ∃ (L : C_c(E n, ℝ) →ₗ[ℝ] ℝ),
      (∀ (x : smoothCc), L x = L0 x) ∧ ∀ (f : C_c(E n, ℝ)), L f ≤ N f :=
    exists_extension_of_le_sublinear f_pmap N N_hom N_add hf
  rcases h_ext with ⟨L, hL_ext, hL_le⟩

  have hL_bound : ∀ (f : C_c(E n, ℝ)), |L f| ≤ C * ‖Cc.toC₀ f‖ := by
    intro f
    have h1 : L f ≤ N f := hL_le f
    have h2 : L (-f) ≤ N (-f) := hL_le (-f)
    have h3 : N (-f) = N f := by
      have h4 : Cc.toC₀ (-f) = -Cc.toC₀ f := by
        ext x
        <;> simp [Cc.toC₀] <;> rfl
      have h5 : ‖Cc.toC₀ (-f)‖ = ‖Cc.toC₀ f‖ := by rw [h4, norm_neg]
      dsimp only [N]; rw [h5]
    have h4 : -L f ≤ N f := by
      have h5 : L (-f) = -L f := by simp
      rw [h5] at h2; rw [h3] at h2; exact h2
    have h4' : -N f ≤ L f := by linarith
    exact abs_le.mpr ⟨h4', h1⟩

  have h_riesz := signed_riesz_representation (X := E n) L C hC hL_bound
  rcases h_riesz with ⟨μ_i, hμ_int, hμ_tv⟩

  have h_final : ∀ (ψ : E n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ),
      (∫ x in S, fderiv ℝ ψ x e_i) =
        (∫ x, ψ x ∂μ_i.toJordanDecomposition.posPart) -
        (∫ x, ψ x ∂μ_i.toJordanDecomposition.negPart) := by
    intro ψ hψ hsupp
    let ψ_c : C(E n, ℝ) := ⟨ψ, hψ.continuous⟩
    let ψ_cc : C_c(E n, ℝ) := ⟨ψ_c, hsupp⟩
    have h_smooth : ψ_cc ∈ smoothCc := hψ
    let ψ_smooth : smoothCc := ⟨ψ_cc, h_smooth⟩
    have h1 : L ψ_cc = L0 ψ_smooth := hL_ext ψ_smooth
    have h2 : L0 ψ_smooth = ∫ x in S, fderiv ℝ ψ x e_i := by rfl
    have h3 : L ψ_cc = (∫ x, ψ x ∂μ_i.toJordanDecomposition.posPart) -
        (∫ x, ψ x ∂μ_i.toJordanDecomposition.negPart) := hμ_int ψ_cc
    rw [h1, h2] at h3
    exact h3

  have h_tv_bound : μ_i.totalVariation Set.univ ≤ perimeter S := by
    have h4 : μ_i.totalVariation Set.univ ≤ ENNReal.ofReal C := hμ_tv
    have h5 : ENNReal.ofReal C = perimeter S := by rw [ENNReal.ofReal_toReal hfin.ne]
    rw [h5] at h4; exact h4

  exact ⟨μ_i, h_final, h_tv_bound⟩

-- ============================================================================
-- Construction of Dχ_S
-- ============================================================================

noncomputable def distributionalDerivative (S : Set (E n)) :
    VectorMeasure (E n) (E n) :=
  if h : perimeter S < ⊤ then
    let μ : Fin n → SignedMeasure (E n) := fun i =>
      Classical.choose (distributionalDerivative_signedMeasure S i h)
    ∑ i : Fin n,
      let e_i : E n := EuclideanSpace.single i (1 : ℝ)
      let f_i : ℝ → E n := fun r => r • e_i
      let hom_i : ℝ →+ E n :=
        { toFun := f_i, map_zero' := by simp [f_i], map_add' := by intro a b; simp [f_i, add_smul] }
      have hcont_i : Continuous f_i := by
        change Continuous (fun r : ℝ => r • e_i)
        fun_prop
      (μ i).mapRange hom_i hcont_i
  else 0

noncomputable def perimeterMeasure (S : Set (E n)) : Measure (E n) :=
  (distributionalDerivative S).variation

-- ============================================================================
-- Integration formula
-- ============================================================================

private def projI (i : Fin n) : E n →L[ℝ] ℝ :=
  { toFun := fun x => x i, map_add' := by intro a b; rfl, map_smul' := by intro c a; rfl }

/-- If `T' s = T s ∘ L`, then `setToFun μ T' hT' f = setToFun μ T hT (L ∘ f)`. -/
lemma setToFun_comp_clm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {T : Set α → (F →L[ℝ] G)} {C : ℝ} (hT : DominatedFinMeasAdditive μ T C)
    (L : E →L[ℝ] F) (f : α → E) (hf : Integrable f μ) :
    setToFun μ (fun s => (T s).comp L)
      (⟨fun s t hs ht hμs hμt hdisj => by
        have h9 := hT.1 s t hs ht hμs hμt hdisj
        simpa [Function.comp] using congr_arg (fun g : F →L[ℝ] G => g.comp L) h9,
        fun s hs hsf => by
          have h10 : ‖T s‖ ≤ C * μ.real s := hT.2 s hs hsf
          calc ‖(T s).comp L‖
            ≤ ‖T s‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ (C * μ.real s) * ‖L‖ := by gcongr
          _ = (C * ‖L‖) * μ.real s := by ring⟩) f =
    setToFun μ T hT (fun x => L (f x)) := by
  let T' : Set α → (E →L[ℝ] G) := fun s => (T s).comp L
  let hT' : DominatedFinMeasAdditive μ T' (C * ‖L‖) := by
    refine ⟨fun s t hs ht hμs hμt hdisj => ?_, fun s hs hsf => ?_⟩
    · have h9 := hT.1 s t hs ht hμs hμt hdisj
      simpa [T', Function.comp] using congr_arg (fun g : F →L[ℝ] G => g.comp L) h9
    · have h10 : ‖T s‖ ≤ C * μ.real s := hT.2 s hs hsf
      calc ‖T' s‖
        ≤ ‖T s‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * μ.real s) * ‖L‖ := by gcongr
      _ = (C * ‖L‖) * μ.real s := by ring
  let P : (α → E) → Prop := fun g =>
    setToFun μ T' hT' g = setToFun μ T hT (fun x => L (g x))
  have h_ind : ∀ (c : E) ⦃s : Set α⦄, MeasurableSet s → μ s < ⊤ → P (s.indicator fun _ => c) := by
    intro c s hs hμs
    dsimp only [P]
    have h_L_ind : (fun x : α => L ((s.indicator (fun _ : α => c)) x)) =
        s.indicator (fun _ : α => L c) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx, Set.indicator_apply]
    calc setToFun μ T' hT' (s.indicator (fun _ => c))
      = (T' s) c := setToFun_indicator_const hT' hs hμs.ne c
    _ = (T s) (L c) := by rfl
    _ = setToFun μ T hT (s.indicator (fun _ => L c)) := (setToFun_indicator_const hT hs hμs.ne (L c)).symm
    _ = setToFun μ T hT (fun x => L ((s.indicator (fun _ => c)) x)) := by rw [h_L_ind]
  have h_add : ∀ ⦃f g : α → E⦄, Disjoint (Function.support f) (Function.support g) →
      Integrable f μ → Integrable g μ → P f → P g → P (f + g) := by
    intro f g hdisj hf hg hPf hPg
    have hfi : Integrable (fun x => L (f x)) μ := L.integrable_comp hf
    have hgi : Integrable (fun x => L (g x)) μ := L.integrable_comp hg
    dsimp only [P]
    have h_eq1 : (fun x : α => L ((f + g) x)) = (fun x : α => L (f x)) + (fun x : α => L (g x)) := by
      funext x; simp
    calc setToFun μ T' hT' (f + g)
      = setToFun μ T' hT' f + setToFun μ T' hT' g := setToFun_add hT' hf hg
    _ = setToFun μ T hT (fun x => L (f x)) + setToFun μ T hT (fun x => L (g x)) := by rw [hPf, hPg]
    _ = setToFun μ T hT ((fun x => L (f x)) + (fun x => L (g x))) := (setToFun_add hT hfi hgi).symm
    _ = setToFun μ T hT (fun x => L ((f + g) x)) := by rw [h_eq1]
  have h_ae : ∀ ⦃f g : α → E⦄, f =ᵐ[μ] g → Integrable f μ → P f → P g := by
    intro f g h_eq hf hPf
    have h_eq2 : (fun x => L (f x)) =ᵐ[μ] (fun x => L (g x)) := by
      filter_upwards [h_eq] with x hx
      rw [hx]
    dsimp only [P] at hPf ⊢
    have h1 : setToFun μ T' hT' g = setToFun μ T' hT' f := setToFun_congr_ae hT' h_eq.symm
    have h2 : setToFun μ T hT (fun x => L (g x)) = setToFun μ T hT (fun x => L (f x)) :=
      setToFun_congr_ae hT h_eq2.symm
    rw [h1, h2, hPf]
  have h_closed : IsClosed {f : Lp E 1 μ | P (f : α → E)} := by
    letI : Fact (1 ≤ 1) := ⟨by norm_num⟩
    let compLp_clm : Lp E 1 μ →L[ℝ] Lp F 1 μ := L.compLpL (p := 1) (μ := μ)
    let F1 : Lp E 1 μ → G := fun f => setToFun μ T' hT' (f : α → E)
    let F2 : Lp E 1 μ → G := fun f => setToFun μ T hT (compLp_clm f)
    have h_cont1 : Continuous F1 := continuous_setToFun hT'
    have h_cont2 : Continuous F2 := (continuous_setToFun hT).comp compLp_clm.continuous
    have h_eq_F2 : ∀ (f : Lp E 1 μ), F2 f = setToFun μ T hT (fun x => L ((f : α → E) x)) := by
      intro f
      have h2 : (compLp_clm f : α → F) =ᵐ[μ] fun x => L ((f : α → E) x) := by
        dsimp only [compLp_clm]
        exact L.coeFn_compLpL (p := 1) (μ := μ) f
      exact setToFun_congr_ae hT h2
    have h_eq_set : {f : Lp E 1 μ | P (f : α → E)} = {f | F1 f = F2 f} := by
      ext f
      simp only [Set.mem_setOf_eq, F1]
      rw [h_eq_F2 f]
      <;> rfl
    rw [h_eq_set]
    exact isClosed_eq h_cont1 h_cont2
  exact MeasureTheory.Integrable.induction P h_ind h_add h_closed h_ae hf

/-- Variation of coordinate-mapped signed measure equals the signed measure variation. -/
lemma mapRange_coordHom_variation_eq {μ : SignedMeasure (E n)} {i : Fin n} :
    (μ.mapRange (coordHom i) (coordHom_cont i)).variation = μ.variation := by
  let D_i := μ.mapRange (coordHom i) (coordHom_cont i)
  have h_norm_eq : ∀ (A : Set (E n)), ‖D_i A‖ₑ = ‖μ A‖ₑ := by
    intro A
    have h1 : D_i A = (μ A) • EuclideanSpace.single i (1 : ℝ) := by
      simp [D_i, VectorMeasure.mapRange_apply, coordHom] <;> rfl
    rw [h1]
    have h2 : ‖(μ A) • EuclideanSpace.single i (1 : ℝ)‖ₑ = ‖μ A‖ₑ := by
      rw [enorm_smul]
      have h3 : ‖EuclideanSpace.single i (1 : ℝ)‖ₑ = 1 := by
        have h4 : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
        have h5 : ‖EuclideanSpace.single i (1 : ℝ)‖ₑ = ENNReal.ofReal ‖EuclideanSpace.single i (1 : ℝ)‖ := by
          exact Eq.symm (ofReal_norm (EuclideanSpace.single i 1))
        rw [h5, h4] <;> norm_num
      rw [h3, mul_one]
    exact h2
  apply Measure.ext
  intro s hs
  have h1 : D_i.variation s ≤ μ.variation s := by
    apply VectorMeasure.variation_apply_le_of_forall_enorm_le hs
    intro E hE hEA
    have h2 : ‖D_i E‖ₑ = ‖μ E‖ₑ := h_norm_eq E
    rw [h2]
    exact VectorMeasure.enorm_measure_le_variation μ E
  have h2 : μ.variation s ≤ D_i.variation s := by
    apply VectorMeasure.variation_apply_le_of_forall_enorm_le hs
    intro E hE hEA
    have h3 : ‖μ E‖ₑ = ‖D_i E‖ₑ := (h_norm_eq E).symm
    rw [h3]
    exact VectorMeasure.enorm_measure_le_variation D_i E
  exact le_antisymm h1 h2

/-- Integral against coordinate-mapped signed measure. -/
lemma integral_mapRange_coordHom {μ : SignedMeasure (E n)} {i : Fin n} {f : E n → E n}
    (hf : μ.Integrable f) :
    ∫ᵛ x, f x ∂[innerBilinear; μ.mapRange (coordHom i) (coordHom_cont i)] =
    ∫ᵛ x, (f x i) ∂<•μ := by
  let D_i := μ.mapRange (coordHom i) (coordHom_cont i)
  let B_flip : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  let proj_i : E n →L[ℝ] ℝ := projI i
  let T2 := μ.transpose B_flip
  let T' : Set (E n) → (E n →L[ℝ] ℝ) := fun s => (T2 s).comp proj_i
  let IB : (E n) →L[ℝ] ((E n) →L[ℝ] ℝ) := innerBilinear
  let trans : VectorMeasure (E n) ((E n) →L[ℝ] ℝ) := D_i.transpose IB

  have h_var_eq : D_i.variation = μ.variation := mapRange_coordHom_variation_eq

  let h_dom1 : DominatedFinMeasAdditive D_i.variation trans ‖IB‖ :=
    dominatedFinMeasAdditive_cbmApplyMeasure D_i IB
  let h_dom2 : DominatedFinMeasAdditive μ.variation T2 ‖B_flip‖ :=
    dominatedFinMeasAdditive_cbmApplyMeasure μ B_flip

  have h_dom1'' : DominatedFinMeasAdditive μ.variation trans ‖IB‖ := by
    have h : D_i.variation = μ.variation := h_var_eq
    rw [← h]
    exact h_dom1

  let h_dom_T' : DominatedFinMeasAdditive μ.variation T' (‖B_flip‖ * ‖proj_i‖) := by
    refine ⟨fun s t hs ht hμs hμt hdisj => ?_, fun s hs hsf => ?_⟩
    · have h9 : T2 (s ∪ t) = T2 s + T2 t := h_dom2.1 s t hs ht hμs hμt hdisj
      have h10 : (T2 (s ∪ t)).comp proj_i = (T2 s).comp proj_i + (T2 t).comp proj_i := by
        rw [h9] <;> simp
      exact h10
    · have h10 : ‖T2 s‖ ≤ ‖B_flip‖ * μ.variation.real s := h_dom2.2 s hs hsf
      calc ‖T' s‖
        ≤ ‖T2 s‖ * ‖proj_i‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖B_flip‖ * μ.variation.real s) * ‖proj_i‖ := by gcongr
      _ = (‖B_flip‖ * ‖proj_i‖) * μ.variation.real s := by ring

  have h_transpose_eq : trans = T' := by
    funext s
    apply ContinuousLinearMap.ext
    intro x
    have h4 : trans s x = IB x (D_i s) := by
      exact cbmApplyMeasure_apply D_i IB s x
    rw [h4]
    have h1 : D_i s = (μ s) • EuclideanSpace.single i (1 : ℝ) := by
      simp [D_i, VectorMeasure.mapRange_apply, coordHom] <;> rfl
    rw [h1]
    have h2 : IB x ((μ s) • EuclideanSpace.single i (1 : ℝ)) = (μ s) * (x i) := by
      rw [innerBilinear_apply]
      have h21 : inner ℝ x ((μ s) • EuclideanSpace.single i (1 : ℝ)) =
          (μ s) * inner ℝ x (EuclideanSpace.single i (1 : ℝ)) := by
        rw [inner_smul_right]
      rw [h21]
      have h22 : inner ℝ x (EuclideanSpace.single i (1 : ℝ)) = x i := by
        simpa [EuclideanSpace.inner_single_right] using rfl
      rw [h22] <;> ring
    have h3 : T' s x = (μ s) * (x i) := by
      dsimp only [T']
      have h_a : (T2 s).comp proj_i x = T2 s (proj_i x) := by rfl
      have h_b : T2 = cbmApplyMeasure μ B_flip := transpose_eq_cbmApplyMeasure μ B_flip
      have h_c : T2 s (proj_i x) = B_flip (proj_i x) (μ s) := by
        rw [h_b]
        exact cbmApplyMeasure_apply μ B_flip s (proj_i x)
      have h_d : B_flip (proj_i x) (μ s) = (μ s) * (proj_i x) := by rfl
      have h_e : proj_i x = x i := by rfl
      rw [h_a, h_c, h_d, h_e]
    rw [h2, h3]

  have hf_variation : Integrable f μ.variation := by
    simpa [VectorMeasure.Integrable] using hf

  have hf' : Integrable f D_i.variation := by
    rw [h_var_eq]
    exact hf_variation

  have h_main1 : ∫ᵛ x, f x ∂[IB; D_i] = setToFun D_i.variation trans h_dom1 f := by
    rfl

  have h_congr_measure : setToFun D_i.variation trans h_dom1 f =
      setToFun μ.variation trans h_dom1'' f :=
    setToFun_congr_measure_of_integrable (1 : ENNReal) one_ne_top
      (by rw [one_smul, h_var_eq]) h_dom1 h_dom1'' f hf'

  have h_congr_left : setToFun μ.variation trans h_dom1'' f =
      setToFun μ.variation T' h_dom_T' f :=
    setToFun_congr_left' h_dom1'' h_dom_T'
      (fun s hs _ => by rw [← h_transpose_eq]) f

  have h_comp : setToFun μ.variation T' h_dom_T' f =
      setToFun μ.variation T2 h_dom2 (fun x => f x i) :=
    setToFun_comp_clm h_dom2 proj_i f hf_variation

  have h_main2 : ∫ᵛ x, (f x i) ∂<•μ = setToFun μ.variation T2 h_dom2 (fun x => f x i) := by
    rfl

  rw [h_main1, h_congr_measure, h_congr_left, h_comp, h_main2]

/-- Simplification lemma for `distributionalDerivative` when perimeter is finite. -/
lemma distributionalDerivative_eq (S : Set (E n)) (hfin : perimeter S < ⊤) :
    distributionalDerivative S =
    ∑ i : Fin n, (Classical.choose (distributionalDerivative_signedMeasure S i hfin)).mapRange
      (coordHom i) (coordHom_cont i) := by
  rw [distributionalDerivative, dif_pos hfin]
  dsimp only
  <;> congr <;> funext i <;> simp [coordHom, coordHom_cont] <;> rfl

/-- Finiteness of Jordan decomposition parts. -/
lemma jordanParts_finite {μ : SignedMeasure (E n)} (h : μ.totalVariation Set.univ < ⊤) :
    IsFiniteMeasure μ.toJordanDecomposition.posPart ∧ IsFiniteMeasure μ.toJordanDecomposition.negPart := by
  let μpos := μ.toJordanDecomposition.posPart
  let μneg := μ.toJordanDecomposition.negPart
  have h_tv : μ.totalVariation = μpos + μneg := by
    simp [SignedMeasure.totalVariation, μpos, μneg] <;> rfl
  have hpos_le : μpos ≤ μ.totalVariation := by
    rw [h_tv]
    apply Measure.le_iff.mpr
    intro s _
    simp [Measure.add_apply]
    <;> exact le_add_of_nonneg_right (Measure.zero_le μneg s)
  have hneg_le : μneg ≤ μ.totalVariation := by
    rw [h_tv]
    apply Measure.le_iff.mpr
    intro s _
    simp [Measure.add_apply]
    <;> exact le_add_of_nonneg_left (Measure.zero_le μpos s)
  exact ⟨⟨(hpos_le Set.univ).trans_lt h⟩, ⟨(hneg_le Set.univ).trans_lt h⟩⟩

/-- Integration formula: `∫ φ · dDχ_S = ∫_S div φ`. -/
lemma distributionalDerivative_integral_formula (S : Set (E n)) (hfin : perimeter S < ⊤)
    (φ : E n → E n) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    ∫ᵛ x, φ x ∂[innerBilinear; distributionalDerivative S] =
    ∫ x in S, divergence φ x := by
  let μ : Fin n → SignedMeasure (E n) := fun i =>
    Classical.choose (distributionalDerivative_signedMeasure S i hfin)
  have hμ_main : ∀ i : Fin n,
      (∀ (ψ : E n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ),
        (∫ x in S, fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) =
          (∫ x, ψ x ∂(μ i).toJordanDecomposition.posPart) -
          (∫ x, ψ x ∂(μ i).toJordanDecomposition.negPart)) ∧
      ((μ i).totalVariation Set.univ ≤ perimeter S) := by
    intro i
    exact Classical.choose_spec (distributionalDerivative_signedMeasure S i hfin)

  have hD : distributionalDerivative S =
      ∑ i : Fin n, (μ i).mapRange (coordHom i) (coordHom_cont i) :=
    distributionalDerivative_eq S hfin

  have h_fin_var : ∀ i : Fin n, IsFiniteMeasure (μ i).variation := by
    intro i
    let μpos := (μ i).toJordanDecomposition.posPart
    let μneg := (μ i).toJordanDecomposition.negPart
    have h_tv_lt_top : (μ i).totalVariation Set.univ < ⊤ := by
      calc (μ i).totalVariation Set.univ
        ≤ perimeter S := (hμ_main i).2
      _ < ⊤ := hfin
    have hle : (μ i).variation ≤ (μ i).totalVariation := by
      apply Measure.le_iff.mpr
      intro s hs
      have h1 : ∀ (A : Set (E n)), MeasurableSet A → A ⊆ s →
          ‖(μ i) A‖ₑ ≤ (μ i).totalVariation A := by
        intro A hA _
        have h2 : ‖(μ i) A‖ₑ = ENNReal.ofReal |(μ i) A| :=
          Real.enorm_eq_ofReal_abs ((μ i) A)
        rw [h2]
        exact signed_abs_le_totalVariation (μ i) hA
      exact VectorMeasure.variation_apply_le_of_forall_enorm_le hs h1
    have h1 : (μ i).variation Set.univ < ⊤ := by
      calc (μ i).variation Set.univ
        ≤ (μ i).totalVariation Set.univ := hle Set.univ
      _ ≤ perimeter S := (hμ_main i).2
      _ < ⊤ := hfin
    exact ⟨h1⟩

  rw [hD]

  have h1 : ∫ᵛ x, φ x ∂[innerBilinear; ∑ i : Fin n, (μ i).mapRange (coordHom i) (coordHom_cont i)] =
      ∑ i : Fin n, ∫ᵛ x, φ x ∂[innerBilinear; (μ i).mapRange (coordHom i) (coordHom_cont i)] := by
    apply VectorMeasure.integral_finsetSum_vectorMeasure
    intro i _
    haveI : IsFiniteMeasure (μ i).variation := h_fin_var i
    have hfi : Integrable φ (μ i).variation :=
      hφ.continuous.integrable_of_hasCompactSupport (μ := (μ i).variation) hsupp
    have h_var_eq : ((μ i).mapRange (coordHom i) (coordHom_cont i)).variation = (μ i).variation :=
      mapRange_coordHom_variation_eq
    simpa [VectorMeasure.Integrable, h_var_eq] using hfi
  rw [h1]

  have h2 : ∀ i : Fin n, ∫ᵛ x, φ x ∂[innerBilinear; (μ i).mapRange (coordHom i) (coordHom_cont i)] =
      ∫ᵛ x, (φ x i) ∂<•(μ i) := by
    intro i
    haveI : IsFiniteMeasure (μ i).variation := h_fin_var i
    have hfi : Integrable φ (μ i).variation :=
      hφ.continuous.integrable_of_hasCompactSupport (μ := (μ i).variation) hsupp
    exact integral_mapRange_coordHom (μ := μ i) (f := φ) hfi
  rw [Finset.sum_congr rfl (fun i _ => h2 i)]

  let ψ : Fin n → (E n → ℝ) := fun i x => φ x i
  have hψ_diff : ∀ i, ContDiff ℝ ∞ (ψ i) := by
    intro i
    exact (projI i).contDiff.comp hφ
  have hψ_supp : ∀ i, HasCompactSupport (ψ i) := by
    intro i
    have h1 : Function.support (ψ i) ⊆ Function.support φ := by
      intro x hx
      by_contra h
      have h2 : φ x = 0 := by simpa [Function.mem_support] using h
      have h3 : ψ i x = 0 := by
        simp [ψ, h2]
      exact hx h3
    exact HasCompactSupport.mono hsupp h1

  have h3 : ∀ i : Fin n, ∫ᵛ x, (φ x i) ∂<•(μ i) =
      (∫ x, (φ x i) ∂(μ i).toJordanDecomposition.posPart) -
      (∫ x, (φ x i) ∂(μ i).toJordanDecomposition.negPart) := by
    intro i
    let μpos := (μ i).toJordanDecomposition.posPart
    let μneg := (μ i).toJordanDecomposition.negPart
    have h_decomp : (μ i) = μpos.toSignedMeasure - μneg.toSignedMeasure :=
      (SignedMeasure.toSignedMeasure_toJordanDecomposition (μ i)).symm
    have h_tv_lt_top : (μ i).totalVariation Set.univ < ⊤ := by
      calc (μ i).totalVariation Set.univ
        ≤ perimeter S := (hμ_main i).2
      _ < ⊤ := hfin
    have h_jordan := jordanParts_finite (h := h_tv_lt_top)
    haveI hpos_fin : IsFiniteMeasure μpos := h_jordan.1
    haveI hneg_fin : IsFiniteMeasure μneg := h_jordan.2
    have h_int_pos : MeasureTheory.Integrable (ψ i) μpos :=
      (hψ_diff i).continuous.integrable_of_hasCompactSupport (hψ_supp i)
    have h_int_neg : MeasureTheory.Integrable (ψ i) μneg :=
      (hψ_diff i).continuous.integrable_of_hasCompactSupport (hψ_supp i)
    have hvm_pos : μpos.toSignedMeasure.Integrable (ψ i) := by
      have h_eq : μpos.toSignedMeasure.variation = μpos := Measure.variation_toSignedMeasure (μ := μpos)
      have h : Integrable (ψ i) μpos.toSignedMeasure.variation := by
        rw [h_eq]
        exact h_int_pos
      exact h
    have hvm_neg : μneg.toSignedMeasure.Integrable (ψ i) := by
      have h_eq : μneg.toSignedMeasure.variation = μneg := Measure.variation_toSignedMeasure (μ := μneg)
      have h : Integrable (ψ i) μneg.toSignedMeasure.variation := by
        rw [h_eq]
        exact h_int_neg
      exact h
    have h_int_pos' : ∫ᵛ x, (ψ i) x ∂<•μpos.toSignedMeasure = ∫ x, (ψ i) x ∂μpos :=
      VectorMeasure.integral_toSignedMeasure (μ := μpos)
    have h_int_neg' : ∫ᵛ x, (ψ i) x ∂<•μneg.toSignedMeasure = ∫ x, (ψ i) x ∂μneg :=
      VectorMeasure.integral_toSignedMeasure (μ := μneg)
    have h_lhs : ∫ᵛ x, (φ x i) ∂<•(μ i) =
        (∫ x, (ψ i) x ∂μpos) - (∫ x, (ψ i) x ∂μneg) := by
      rw [h_decomp]
      rw [VectorMeasure.integral_sub_vectorMeasure hvm_pos hvm_neg, h_int_pos', h_int_neg']
    have h_rhs : (∫ x, (φ x i) ∂(μ i).toJordanDecomposition.posPart) -
        (∫ x, (φ x i) ∂(μ i).toJordanDecomposition.negPart) =
        (∫ x, (ψ i) x ∂μpos) - (∫ x, (ψ i) x ∂μneg) := by rfl
    exact h_lhs.trans h_rhs.symm
  rw [Finset.sum_congr rfl (fun i _ => h3 i)]

  have h4 : ∑ i : Fin n, ((∫ x, (φ x i) ∂(μ i).toJordanDecomposition.posPart) -
        (∫ x, (φ x i) ∂(μ i).toJordanDecomposition.negPart)) =
      ∑ i : Fin n, (∫ x in S, fderiv ℝ (ψ i) x (EuclideanSpace.single i (1 : ℝ))) := by
    apply Finset.sum_congr rfl
    intro i _
    exact ((hμ_main i).1 (ψ i) (hψ_diff i) (hψ_supp i)).symm
  rw [h4]

  let g : Fin n → E n → ℝ := fun i x => fderiv ℝ (ψ i) x (EuclideanSpace.single i (1 : ℝ))
  have hg_int : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (g i) (volume.restrict S) := by
    intro i _
    exact directionalDerivative_integrable (hψ_diff i) (hψ_supp i) (EuclideanSpace.single i (1 : ℝ))
  have h5 : ∑ i : Fin n, (∫ x in S, g i x) =
      ∫ x in S, ∑ i : Fin n, g i x := by
    have h_eq : ∫ x in S, ∑ i : Fin n, g i x = ∑ i : Fin n, (∫ x in S, g i x) :=
      integral_finsetSum (Finset.univ) (hf := hg_int)
    exact h_eq.symm
  rw [h5]

  have h6 : ∀ (x : E n), (∑ i : Fin n, g i x) = divergence φ x := by
    intro x
    rfl
  have h7 : (fun x : E n => ∑ i : Fin n, g i x) = (fun x : E n => divergence φ x) := by
    funext x
    exact h6 x
  exact congr_arg (fun f : E n → ℝ => ∫ x in S, f x) h7

-- ============================================================================
-- Perimeter equals total variation
-- ============================================================================

/-- Variation of coordinate-mapped signed measure is bounded by total variation. -/
lemma mapRange_coordHom_variation_le (μ : SignedMeasure (E n)) (i : Fin n) :
    (μ.mapRange (coordHom i) (coordHom_cont i)).variation ≤ μ.totalVariation := by
  let ν := μ.mapRange (coordHom i) (coordHom_cont i)
  apply Measure.le_iff.mpr
  intro s hs
  have h1 : ∀ (E : Set (E n)), MeasurableSet E → E ⊆ s →
      ‖ν E‖ₑ ≤ μ.totalVariation E := by
    intro E hE _
    have h21 : ν E = (coordHom i) (μ E) := by rw [VectorMeasure.mapRange_apply]
    rw [h21]
    have h22 : (coordHom i) (μ E) = (μ E) • EuclideanSpace.single i (1 : ℝ) := by rfl
    rw [h22]
    have hnorm : ‖(μ E) • EuclideanSpace.single i (1 : ℝ)‖ = |μ E| := by
      simp [norm_smul, PiLp.norm_single]
    have henorm : ‖(μ E) • EuclideanSpace.single i (1 : ℝ)‖ₑ =
        ENNReal.ofReal ‖(μ E) • EuclideanSpace.single i (1 : ℝ)‖ := by
      exact Eq.symm (ofReal_norm (μ E • EuclideanSpace.single i 1))
    rw [henorm, hnorm]
    exact signed_abs_le_totalVariation μ hE
  exact VectorMeasure.variation_apply_le_of_forall_enorm_le hs h1

/-- The De Giorgi perimeter equals the total variation of `Dχ_S` on `univ`. -/
theorem perimeter_eq_variation (S : Set (E n)) (hfin : perimeter S < ⊤) :
    perimeter S = perimeterMeasure S Set.univ := by
  let D := distributionalDerivative S
  let μs : Fin n → SignedMeasure (E n) := fun i =>
    Classical.choose (distributionalDerivative_signedMeasure S i hfin)
  have hμ_bound : ∀ i : Fin n, (μs i).totalVariation Set.univ ≤ perimeter S := by
    intro i
    exact (Classical.choose_spec (distributionalDerivative_signedMeasure S i hfin)).2
  have hD : D = ∑ i : Fin n, (μs i).mapRange (coordHom i) (coordHom_cont i) :=
    distributionalDerivative_eq S hfin
  have h_int : ∀ (φ : E n → E n), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ᵛ x, φ x ∂[innerBilinear; D] = ∫ x in S, divergence φ x := by
    intro φ hφ hsupp
    exact distributionalDerivative_integral_formula S hfin φ hφ hsupp

  have h1 : perimeter S ≤ D.variation Set.univ :=
    perimeter_le_variation_of_integral_formula S hfin D μs hD hμ_bound h_int

  have h_sum_measure : D.variation ≤ ∑ i : Fin n, ((μs i).mapRange (coordHom i) (coordHom_cont i)).variation := by
    rw [hD]
    exact VectorMeasure.variation_finsetSum_le (Finset.univ) _
  have hcard_lt : (Finset.card (Finset.univ : Finset (Fin n)) : ENNReal) < ⊤ := ENNReal.natCast_lt_top _
  have hD_fin : D.variation Set.univ < ⊤ := by
    calc D.variation Set.univ
      ≤ (∑ i : Fin n, ((μs i).mapRange (coordHom i) (coordHom_cont i)).variation) Set.univ := h_sum_measure Set.univ
    _ = ∑ i : Fin n, ((μs i).mapRange (coordHom i) (coordHom_cont i)).variation Set.univ := by
        simp [Finset.sum_apply] <;> rfl
    _ ≤ ∑ i : Fin n, (μs i).totalVariation Set.univ := by
        gcongr with i _
        exact mapRange_coordHom_variation_le (μs i) i
    _ ≤ ∑ i : Fin n, perimeter S := by gcongr with i _; exact hμ_bound i
    _ = (Finset.card (Finset.univ : Finset (Fin n)) : ENNReal) * perimeter S := by
        simp [Finset.sum_const] <;> ring
    _ < ⊤ := ENNReal.mul_lt_top hcard_lt hfin

  letI : IsFiniteMeasure D.variation := ⟨hD_fin⟩

  have h2 : D.variation Set.univ ≤ perimeter S :=
    variation_le_perimeter_of_integral_formula S hfin D hD_fin h_int

  have h3 : perimeter S = D.variation Set.univ := le_antisymm h1 h2
  simpa [perimeterMeasure] using h3

-- ============================================================================
-- Reduced boundary
-- ============================================================================

def reducedBoundary (S : Set (E n)) : Set (E n) :=
  {x | ∀ r > 0, 0 < perimeterMeasure S (ball x r)}

-- ============================================================================
-- Measure-theoretic normal
-- ============================================================================

lemma coordinateSignedMeasure_absolutelyContinuous (S : Set (E n)) (i : Fin n)
    (hfin : perimeter S < ⊤) :
    (Classical.choose (distributionalDerivative_signedMeasure S i hfin)).variation
      ≪ perimeterMeasure S := by
  let μ : Fin n → SignedMeasure (E n) := fun i =>
    Classical.choose (distributionalDerivative_signedMeasure S i hfin)
  let proj_i_lm : E n →ₗ[ℝ] ℝ :=
    { toFun := fun x => x i, map_add' := by intro a b; rfl, map_smul' := by intro c a; rfl }
  let proj_i_clm : E n →L[ℝ] ℝ := proj_i_lm.toContinuousLinearMap
  let proj_i : E n →+ ℝ := proj_i_clm.toAddMonoidHom
  have hcont_proj : Continuous proj_i := proj_i_clm.continuous
  let hom (j : Fin n) : ℝ →+ E n :=
    let e_j : E n := PiLp.single 2 j (1 : ℝ)
    { toFun := fun r : ℝ => r • e_j, map_zero' := by simp, map_add' := by intro a b; simp [add_smul] }
  have hcont (j : Fin n) : Continuous (hom j) := by
    change Continuous (fun r : ℝ => r • (PiLp.single 2 j (1 : ℝ) : E n))
    fun_prop
  have h_comp_eq (j : Fin n) (hji : j = i) : proj_i.comp (hom j) = AddMonoidHom.id ℝ := by
    apply AddMonoidHom.ext; intro r
    simp [hom, proj_i, proj_i_clm, proj_i_lm, PiLp.single_apply, hji] <;> ring
  have h_comp_ne (j : Fin n) (hji : j ≠ i) : proj_i.comp (hom j) = 0 := by
    apply AddMonoidHom.ext; intro r
    simp [hom, proj_i, proj_i_clm, proj_i_lm, PiLp.single_apply, hji] <;> ring
  have h_term (j : Fin n) :
      ((μ j).mapRange (hom j) (hcont j)).mapRange proj_i hcont_proj =
        if j = i then μ j else 0 := by
    have h_eq1 : ∀ (A : Set (E n)), MeasurableSet A →
        (((μ j).mapRange (hom j) (hcont j)).mapRange proj_i hcont_proj) A =
        (proj_i.comp (hom j)) ((μ j) A) := by
      intro A hA; simp [VectorMeasure.mapRange_apply]
    by_cases hji : j = i
    · have h_goal : ∀ (A : Set (E n)) (hA : MeasurableSet A),
          (((μ j).mapRange (hom j) (hcont j)).mapRange proj_i hcont_proj) A = (μ j) A := by
        intro A hA
        rw [h_eq1 A hA, h_comp_eq j hji] <;> simp
      have h_ext : ((μ j).mapRange (hom j) (hcont j)).mapRange proj_i hcont_proj = μ j :=
        VectorMeasure.ext h_goal
      rw [h_ext, if_pos hji]
    · have h_goal : ∀ (A : Set (E n)) (hA : MeasurableSet A),
          (((μ j).mapRange (hom j) (hcont j)).mapRange proj_i hcont_proj) A = 0 := by
        intro A hA
        rw [h_eq1 A hA, h_comp_ne j hji] <;> simp
      have h_ext : ((μ j).mapRange (hom j) (hcont j)).mapRange proj_i hcont_proj = 0 :=
        VectorMeasure.ext h_goal
      rw [h_ext, if_neg hji]
  have h_mapRange_sum : ∀ (fs : Finset (Fin n)) (v : Fin n → VectorMeasure (E n) (E n)),
      (∑ j ∈ fs, v j).mapRange proj_i hcont_proj =
        ∑ j ∈ fs, (v j).mapRange proj_i hcont_proj := by
    intro fs v
    induction fs using Finset.induction with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, VectorMeasure.mapRange_add, ih]
  have h_expand : distributionalDerivative S =
      ∑ j : Fin n, (μ j).mapRange (hom j) (hcont j) := by
    rw [distributionalDerivative, dif_pos hfin] <;> rfl
  have h_eq : (distributionalDerivative S).mapRange proj_i hcont_proj = μ i := by
    rw [h_expand]
    rw [h_mapRange_sum (Finset.univ) (fun j => (μ j).mapRange (hom j) (hcont j))]
    rw [Finset.sum_congr rfl (fun j _ => h_term j)]
    rw [Finset.sum_ite_eq'] <;> simp [Finset.mem_univ]
  have h_main : ((distributionalDerivative S).mapRange proj_i hcont_proj).variation
        ≪ (distributionalDerivative S).variation := by
    apply Measure.AbsolutelyContinuous.mk
    intro A hA hμA
    have h1 : ∀ E, MeasurableSet E → E ⊆ A →
        ‖((distributionalDerivative S).mapRange proj_i hcont_proj) E‖ₑ ≤
        (distributionalDerivative S).variation E := by
      intro E hE hEA
      have h2 : ‖(distributionalDerivative S) E‖ₑ ≤
          (distributionalDerivative S).variation E :=
        VectorMeasure.enorm_measure_le_variation (distributionalDerivative S) E
      have h3 : (distributionalDerivative S).variation E ≤ (distributionalDerivative S).variation A :=
        measure_mono hEA
      have h4 : (distributionalDerivative S).variation E = 0 := by
        rw [hμA] at h3; simpa using h3
      have h5 : (distributionalDerivative S) E = 0 := by
        have h6 : ‖(distributionalDerivative S) E‖ₑ = 0 := by
          rw [h4] at h2; exact le_zero_iff.mp h2
        have h7 : ‖(distributionalDerivative S) E‖₊ = 0 := by simpa [enorm] using h6
        exact nnnorm_eq_zero.mp h7
      have h7 : ((distributionalDerivative S).mapRange proj_i hcont_proj) E = 0 := by
        have h8 : ((distributionalDerivative S).mapRange proj_i hcont_proj) E =
            proj_i ((distributionalDerivative S) E) := by
          simpa [VectorMeasure.mapRange_apply] using rfl
        rw [h8, h5] <;> simp
      rw [h7] <;> simp [h4]
    have h5 : ((distributionalDerivative S).mapRange proj_i hcont_proj).variation A ≤
        (distributionalDerivative S).variation A :=
      VectorMeasure.variation_apply_le_of_forall_enorm_le hA h1
    rw [hμA] at h5; simpa using h5
  have h_final : (μ i).variation ≪ (distributionalDerivative S).variation := by
    rw [← h_eq]; exact h_main
  exact h_final

noncomputable def measureTheoreticNormal (S : Set (E n)) (x : E n) : E n :=
  if h : perimeter S < ⊤ then
    let μ : Fin n → SignedMeasure (E n) := fun i =>
      Classical.choose (distributionalDerivative_signedMeasure S i h)
    ∑ i : Fin n,
      let e_i : E n := EuclideanSpace.single i (1 : ℝ)
      ((μ i).rnDeriv (perimeterMeasure S) x) • e_i
  else 0

end Geometry.Perimeter
