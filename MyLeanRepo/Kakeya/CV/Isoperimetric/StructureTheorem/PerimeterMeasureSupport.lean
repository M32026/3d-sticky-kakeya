import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DistributionalDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Tactic


/-!
# Perimeter Measure is Supported on the Frontier

For an open set `U`, `perimeterMeasure U` is concentrated on `frontier U`:
`perimeterMeasure U (frontier U)ᶜ = 0`.

## Proof sketch

1. **Divergence integral zero**: For smooth compactly supported `φ`, `∫ div φ = 0`.
2. **Vanishing on V**: For smooth `φ` supported in `V := (frontier U)ᶜ`,
   `χ_U · φ` is smooth, so `∫_U div φ = ∫ div(χ_U · φ) = 0`.
3. **Density**: Smooth functions supported in `V` are dense in `C_c` supported in `V`.
4. **Signed measures vanish**: Each coordinate signed measure `μ_i` integrates to zero
   against all `C_c` functions supported in `V`. By Jordan decomposition + regularity,
   `μ_i.variation(V) = 0`.
5. **Assembly**: `D.variation ≤ ∑ μ_i.variation`, so `perimeterMeasure U (V) = 0`.

## References

- Ambrosio-Fusco-Pallara, Functions of Bounded Variation, §3.2
- Maggi, Sets of Finite Perimeter, Proposition 12.5
-/

open MeasureTheory Metric Set ENNReal Filter Classical
open scoped MeasureTheory ContDiff CompactlySupported

namespace Geometry.Perimeter

variable {n : ℕ}

/-- If a point is not in the topological support of `f`, then `f x = 0`. -/
lemma eq_zero_of_not_mem_tsupport {α : Type*} [TopologicalSpace α] {β : Type*} [Zero β]
    {f : α → β} {x : α} (h : x ∉ tsupport f) : f x = 0 := by
  have h2 : x ∉ Function.support f := fun h3 => h (subset_closure h3)
  simpa [Function.mem_support] using h2

-- ============================================================================
-- Smooth cutoff lemma (local copy to avoid import conflict)
-- ============================================================================

/-- Existence of a smooth cutoff function equal to 1 on `K`, supported in `Ω`. -/
lemma exists_smooth_cutoff_local
    {K : Set (E n)} (hK : IsCompact K)
    {Ω : Set (E n)} (hΩ_open : IsOpen Ω) (hKsub : K ⊆ Ω) :
    ∃ (η : E n → ℝ), ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      (∀ x ∈ K, η x = 1) ∧ (tsupport η ⊆ Ω) ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) := by
  let C := Ωᶜ
  have hC_closed : IsClosed C := hΩ_open.isClosed_compl
  have h_disj : Disjoint K C := by
    rw [Set.disjoint_left]; intro x hx
    have h_x_in_Omega : x ∈ Ω := hKsub hx
    simpa [C] using h_x_in_Omega
  rcases h_disj.exists_thickenings hK hC_closed with ⟨δ, hδ_pos, hδ_disj⟩
  let U := Metric.thickening (δ / 2) K
  have hU_open : IsOpen U := Metric.isOpen_thickening
  have hK_U : K ⊆ U := Metric.self_subset_thickening (by linarith) K
  have hU_bounded : Bornology.IsBounded U := hK.isBounded.thickening
  have h_closure_U : closure U ⊆ Ω := by
    have h1 : closure U = Metric.cthickening (δ / 2) K := closure_thickening (by linarith) K
    rw [h1]
    have h2 : Metric.cthickening (δ / 2) K ⊆ Metric.thickening δ K :=
      Metric.cthickening_subset_thickening' (by linarith) (by linarith) K
    have h3 : Disjoint (Metric.thickening δ K) C :=
      hδ_disj.mono_right (Metric.self_subset_thickening hδ_pos C)
    have h4 : Metric.thickening δ K ⊆ Cᶜ := Set.disjoint_left.mp h3
    have h5 : Cᶜ = Ω := by ext x; simp [C]
    rw [h5] at h4; exact h2.trans h4
  have hK_closed : IsClosed K := hK.isClosed
  rcases hU_open.exists_contDiff_support_eq (n := ⊤) with ⟨f1, hf1_supp, hf1_diff, hf1_range⟩
  rcases hK_closed.isOpen_compl.exists_contDiff_support_eq (n := ⊤) with ⟨f2, hf2_supp, hf2_diff, hf2_range⟩
  have hf1_nonneg : ∀ x, 0 ≤ f1 x := fun x => (hf1_range (Set.mem_range_self x)).1
  have hf2_nonneg : ∀ x, 0 ≤ f2 x := fun x => (hf2_range (Set.mem_range_self x)).1
  have h_pos : ∀ x, 0 < f1 x + f2 x := by
    intro x
    by_cases h1 : x ∈ Function.support f1
    · have h2 : 0 < f1 x := by
        exact lt_of_le_of_ne (hf1_nonneg x) (Ne.symm h1)
      linarith [hf2_nonneg x]
    · have h2 : f1 x = 0 := by simpa [Function.mem_support] using h1
      have h3 : x ∉ U := by rwa [hf1_supp] at h1
      have h4 : x ∉ K := fun h5 => h3 (hK_U h5)
      have h5 : x ∈ Kᶜ := h4
      have h6 : x ∈ Function.support f2 := by rw [hf2_supp]; exact h5
      have h7 : 0 < f2 x := by
        exact lt_of_le_of_ne (hf2_nonneg x) (Ne.symm h6)
      linarith
  let f : E n → ℝ := fun x => f1 x / (f1 x + f2 x)
  have hf_diff : ContDiff ℝ ∞ f :=
    ContDiff.div hf1_diff (hf1_diff.add hf2_diff) (fun x => (h_pos x).ne')
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x; exact div_nonneg (hf1_nonneg x) (h_pos x).le
  have hf_le_one : ∀ x, f x ≤ 1 := by
    intro x
    apply div_le_one_of_le₀ _ (h_pos x).le
    simpa using hf2_nonneg x
  have hf_support : Function.support f ⊆ U := by
    intro x hx
    have h : f x ≠ 0 := hx
    have h5 : f1 x ≠ 0 := by
      by_contra h6
      have h7 : f x = 0 := by simp [f, h6]
      exact h h7
    exact hf1_supp ▸ h5
  have hf_one : ∀ x ∈ K, f x = 1 := by
    intro x hx
    have h2 : x ∉ Kᶜ := by simpa using hx
    have h3 : x ∉ Function.support f2 := by rw [hf2_supp]; exact h2
    have h4 : f2 x = 0 := by simpa [Function.mem_support] using h3
    have h5 : f1 x ≠ 0 := by
      have h6 : x ∈ U := hK_U hx
      have h7 : x ∈ Function.support f1 := by rwa [hf1_supp]
      exact h7
    have h8 : f x = (1 : ℝ) := by
      have h9 : f x = f1 x / (f1 x + f2 x) := by rfl
      rw [h9, h4] <;> field_simp [h5] <;> ring
    exact h8
  have hf_compact : HasCompactSupport f := by
    have h7 : tsupport f ⊆ closure U := closure_mono hf_support
    have h8 : IsCompact (closure U) := hU_bounded.isCompact_closure
    exact h8.of_isClosed_subset (isClosed_tsupport f) h7
  have h_tsupport_sub : tsupport f ⊆ Ω := by
    have h7 : tsupport f ⊆ closure U := closure_mono hf_support
    exact h7.trans h_closure_U
  exact ⟨f, hf_diff, hf_compact, hf_one, h_tsupport_sub, fun x => ⟨hf_nonneg x, hf_le_one x⟩⟩

-- ============================================================================
-- 1. Integral of divergence = 0 for compactly supported smooth vector fields
-- ============================================================================

/-- **Integral of divergence of compactly supported smooth vector field is zero.** -/
lemma integral_divergence_eq_zero
    {φ : E n → E n} (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    ∫ x, divergence φ x = 0 := by
  by_cases h0 : n = 0
  · subst h0
    simp [divergence, Finset.sum_empty]
  · rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨m, rfl⟩
    let e : E (m + 1) ≃ₗ[ℝ] (Fin (m + 1) → ℝ) := WithLp.linearEquiv 2 ℝ (Fin (m + 1) → ℝ)
    let e_clm : E (m + 1) ≃L[ℝ] (Fin (m + 1) → ℝ) := e.toContinuousLinearEquiv
    have he_cont : Continuous e := e_clm.continuous
    have hesymm_cont : Continuous e.symm := e_clm.symm.continuous
    let e_me : E (m + 1) ≃ᵐ (Fin (m + 1) → ℝ) := (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm
    have h_eq_fun : (e : E (m + 1) → (Fin (m + 1) → ℝ)) = e_me := by
      funext x
      have h : e x = e_me x := by
        simp [e, e_me, WithLp.linearEquiv] <;> rfl
      exact h
    have he_mp_me : MeasurePreserving e_me volume volume :=
      EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin (m + 1))
    have he_mp : MeasurePreserving e volume volume := by
      rw [h_eq_fun]; exact he_mp_me
    have he_mp_symm_me : MeasurePreserving e_me.symm volume volume :=
      PiLp.volume_preserving_toLp (ι := Fin (m + 1))
    have he_mp_symm : MeasurePreserving e.symm volume volume := by
      have h_eq_symm : (e.symm : (Fin (m + 1) → ℝ) → E (m + 1)) = e_me.symm := by
        funext x
        apply e.injective
        have h1 : e (e.symm x) = x := e.apply_symm_apply x
        have h2 : e (e_me.symm x) = x := by
          have h21 : e (e_me.symm x) = e_me (e_me.symm x) := by rw [←h_eq_fun]
          rw [h21, e_me.apply_symm_apply]
        rw [h1, h2]
      rw [h_eq_symm]; exact he_mp_symm_me
    let K : Set (E (m + 1)) := tsupport φ
    have hK_compact : IsCompact K := hsupp
    rcases hK_compact.isBounded.subset_ball_lt 0 (0 : E (m + 1)) with ⟨R, hR_pos, hK_ball⟩
    let a : Fin (m + 1) → ℝ := fun _ => -R
    let b : Fin (m + 1) → ℝ := fun _ => R
    have hle : a ≤ b := by intro i; linarith
    let K' : Set (Fin (m + 1) → ℝ) := e '' K
    have hK'_compact : IsCompact K' := hK_compact.image he_cont
    have hK'_openbox : K' ⊆ Set.univ.pi (fun i : Fin (m + 1) => Set.Ioo (a i) (b i)) := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have h2 : ‖x‖ < R := by simpa [mem_ball] using hK_ball hx
      intro i
      have h3 : |x i| ≤ ‖x‖ := by
        have h4 : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
        have h5 : |x i| = ‖x i‖ := by
          exact (Real.norm_eq_abs (x i)).symm
        rw [h5]
        exact h4
      have h4 : |x i| < R := by linarith
      intro _
      have h7 : e x i = x i := by simp [e]
      rw [h7]
      exact ⟨by linarith [abs_lt.mp h4], by linarith [abs_lt.mp h4]⟩
    let ψ : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) := fun z => e (φ (e.symm z))
    let f : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ := fun i z => ψ z i
    let f' : Fin (m + 1) → (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) →L[ℝ] ℝ := fun i z =>
      fderiv ℝ (f i) z
    have hHc : ∀ i, ContinuousOn (f i) (Set.Icc a b) := by
      intro i
      have h1 : Continuous ψ := he_cont.comp (hφ.continuous.comp hesymm_cont)
      have h2 : Continuous (f i) := (continuous_apply i).comp h1
      exact h2.continuousOn
    let e_clm : E (m + 1) →L[ℝ] (Fin (m + 1) → ℝ) := ⟨e, he_cont⟩
    let esymm_clm : (Fin (m + 1) → ℝ) →L[ℝ] E (m + 1) := ⟨e.symm, hesymm_cont⟩
    have hesymm_diff : Differentiable ℝ e.symm := esymm_clm.differentiable
    have h_f_eq : ∀ i z, f i z = φ (e.symm z) i := by
      intro i z
      simp [f, ψ]
      <;> rfl
    have hHd : ∀ z ∈ (Set.univ.pi (fun i : Fin (m + 1) => Set.Ioo (a i) (b i))) \ (∅ : Set (Fin (m + 1) → ℝ)),
        ∀ i, HasFDerivAt (f i) (f' i z) z := by
      intro z _ i
      have h3 : DifferentiableAt ℝ (f i) z := by
        have h4 : f i = (fun y : E (m + 1) => φ y i) ∘ e.symm := by
          funext z
          exact h_f_eq i z
        rw [h4]
        have hproj : ContDiff ℝ ∞ (fun z : E (m + 1) => z i) := contDiff_piLp_apply 2
        have hfi_diff : Differentiable ℝ (fun y : E (m + 1) => φ y i) :=
          (hproj.comp hφ).differentiable (by norm_num)
        have h_inner : DifferentiableAt ℝ e.symm z := hesymm_diff z
        have h_outer : DifferentiableAt ℝ (fun y : E (m + 1) => φ y i) (e.symm z) := hfi_diff (e.symm z)
        exact DifferentiableAt.comp z h_outer h_inner
      exact h3.hasFDerivAt
    have h_chain : ∀ z i, (f' i z) (Pi.single i 1) =
        fderiv ℝ (fun y : E (m + 1) => φ y i) (e.symm z) (esymm_clm (Pi.single i 1)) := by
      intro z i
      have h4 : f i = (fun y : E (m + 1) => φ y i) ∘ e.symm := by
        funext z; exact h_f_eq i z
      have h5 : HasFDerivAt (f i) ((fderiv ℝ (fun y : E (m + 1) => φ y i) (e.symm z)).comp esymm_clm) z := by
        rw [h4]
        have hproj : ContDiff ℝ ∞ (fun z : E (m + 1) => z i) := contDiff_piLp_apply 2
        have hfi_diff : DifferentiableAt ℝ (fun y : E (m + 1) => φ y i) (e.symm z) :=
          (hproj.comp hφ).differentiable (by norm_num) (e.symm z)
        have hesymm_at : HasFDerivAt e.symm esymm_clm z := by
          convert esymm_clm.hasFDerivAt using 1 <;> rfl
        exact HasFDerivAt.comp z hfi_diff.hasFDerivAt hesymm_at
      have h6 : f' i z = (fderiv ℝ (fun y : E (m + 1) => φ y i) (e.symm z)).comp
          esymm_clm := by
        have h_diff_at : DifferentiableAt ℝ (f i) z := by
          rw [h4]
          have hproj : ContDiff ℝ ∞ (fun z : E (m + 1) => z i) := contDiff_piLp_apply 2
          have hfi_diff : Differentiable ℝ (fun y : E (m + 1) => φ y i) :=
            (hproj.comp hφ).differentiable (by norm_num)
          have h_inner : DifferentiableAt ℝ e.symm z := hesymm_diff.differentiableAt
          have h_outer : DifferentiableAt ℝ (fun y : E (m + 1) => φ y i) (e.symm z) :=
            hfi_diff.differentiableAt
          exact DifferentiableAt.comp z h_outer h_inner
        exact (h5.unique h_diff_at.hasFDerivAt).symm
      rw [h6]
      have h7 : ((fderiv ℝ (fun y : E (m + 1) => φ y i) (e.symm z)).comp esymm_clm) (Pi.single i 1) =
          (fderiv ℝ (fun y : E (m + 1) => φ y i) (e.symm z)) (esymm_clm (Pi.single i 1)) := by
        rfl
      rw [h7]
      <;> rfl
    have h_single : ∀ i, esymm_clm (Pi.single i 1) = EuclideanSpace.single i (1 : ℝ) := by
      intro i
      simp [e, esymm_clm]
      <;> rfl
    have h_div_eq : ∀ z, (∑ i : Fin (m + 1), (f' i z) (Pi.single i 1)) = divergence φ (e.symm z) := by
      intro z
      have h4 : ∀ i : Fin (m + 1), (f' i z) (Pi.single i 1) =
          fderiv ℝ (fun y : E (m + 1) => φ y i) (e.symm z) (EuclideanSpace.single i 1) := by
        intro i
        rw [h_chain z i, h_single i]
      simp [divergence, h4]
      <;> rfl
    have h1_div : ∀ x, x ∉ K → divergence φ x = 0 := by
      intro x hx
      have h2 : ∃ (U : Set (E (m + 1))), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, φ y = 0 := by
        refine ⟨Kᶜ, hK_compact.isClosed.isOpen_compl, hx, fun y hy => ?_⟩
        have h5 : y ∉ Function.support φ := fun h6 => hy (subset_closure h6)
        simpa [Function.mem_support] using h5
      rcases h2 with ⟨U, hU_open, hxU, hφ_zero⟩
      have h3 : ∀ y ∈ U, divergence φ y = 0 := by
        intro y hy
        have h4 : φ =ᶠ[nhds y] 0 := by
          filter_upwards [hU_open.mem_nhds hy] with z hz
          exact hφ_zero z hz
        have h5 : ∀ i, (fun x : E (m + 1) => φ x i) =ᶠ[nhds y] (0 : E (m + 1) → ℝ) := by
          intro i
          filter_upwards [h4] with z hz
          have hz' : φ z = 0 := hz
          have h_coord : (φ z) i = 0 := by rw [hz'] <;> simp
          exact h_coord
        have h6 : ∀ i, fderiv ℝ (fun x : E (m + 1) => φ x i) y = 0 := by
          intro i
          have h7 : fderiv ℝ (fun x : E (m + 1) => φ x i) y = fderiv ℝ (0 : E (m + 1) → ℝ) y :=
            (h5 i).fderiv_eq
          rw [h7]
          simp
        simp [divergence, h6] <;> rfl
      exact h3 x hxU
    have hdiv_supp : HasCompactSupport (divergence φ) := by
      have h4 : Function.support (divergence φ) ⊆ K := by
        intro x hx; by_contra h5; exact hx (h1_div x h5)
      have h5 : tsupport (divergence φ) ⊆ K := closure_minimal h4 hK_compact.isClosed
      exact IsCompact.of_isClosed_subset hK_compact (isClosed_tsupport (divergence φ)) h5
    have hdiv_cont : Continuous (divergence φ) := by
      have h : ∀ i : Fin (m + 1), Continuous (fun x : E (m + 1) => fderiv ℝ (fun y => φ y i) x (EuclideanSpace.single i 1)) := by
        intro i
        have hci : ContDiff ℝ ∞ (fun y : E (m + 1) => φ y i) := by
          have hproj : ContDiff ℝ ∞ (fun z : E (m + 1) => z i) := by fun_prop
          exact hproj.comp hφ
        have hfd : Continuous (fun x => fderiv ℝ (fun y => φ y i) x) :=
          ContDiff.continuous_fderiv hci (by norm_num)
        have h_eval : Continuous (fun x : E (m + 1) => (fderiv ℝ (fun y => φ y i) x) (EuclideanSpace.single i 1)) := by
          fun_prop
        exact h_eval
      have hsum : Continuous (fun x : E (m + 1) => ∑ i : Fin (m + 1), (fderiv ℝ (fun y => φ y i) x) (EuclideanSpace.single i 1)) :=
        continuous_finset_sum Finset.univ (fun i _ => h i)
      have h_eq : (divergence φ) = (fun x : E (m + 1) => ∑ i : Fin (m + 1), (fderiv ℝ (fun y => φ y i) x) (EuclideanSpace.single i 1)) := by
        funext x
        simp [divergence] <;> rfl
      rw [h_eq]
      exact hsum
    let div_trans : (Fin (m + 1) → ℝ) → ℝ := fun z => divergence φ (e.symm z)
    have hdiv_trans_cont : Continuous div_trans := hdiv_cont.comp hesymm_cont
    have hdiv_trans_supp : HasCompactSupport div_trans := by
      have h_supp_div : Function.support (divergence φ) ⊆ K := by
        intro x hx; by_contra h5; exact hx (h1_div x h5)
      have h1 : Function.support div_trans ⊆ K' := by
        intro z hz
        have h2 : divergence φ (e.symm z) ≠ 0 := hz
        have h3 : e.symm z ∈ Function.support (divergence φ) := by
          simpa [Function.mem_support] using h2
        have h4 : e.symm z ∈ K := h_supp_div h3
        exact ⟨e.symm z, h4, rfl⟩
      have h6 : tsupport div_trans ⊆ K' := closure_minimal h1 hK'_compact.isClosed
      exact IsCompact.of_isClosed_subset hK'_compact (isClosed_tsupport div_trans) h6
    have hHi : IntegrableOn div_trans (Set.Icc a b) volume :=
      hdiv_trans_cont.integrable_of_hasCompactSupport hdiv_trans_supp |>.integrableOn
    have hHi' : IntegrableOn (fun z : Fin (m + 1) → ℝ => (∑ i : Fin (m + 1), (f' i z) (Pi.single i 1))) (Set.Icc a b) volume :=
      hHi.congr (ae_of_all _ (fun z => (h_div_eq z).symm))
    have h_main : ∫ (z : Fin (m + 1) → ℝ) in Set.Icc a b,
        (∑ i : Fin (m + 1), (f' i z) (Pi.single i 1)) =
        ∑ i : Fin (m + 1), ((∫ (x : Fin m → ℝ) in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            f i (i.insertNth (b i) x)) -
          ∫ (x : Fin m → ℝ) in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            f i (i.insertNth (a i) x)) :=
      MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'
        (E := ℝ) a b hle f f' (∅ : Set (Fin (m + 1) → ℝ)) (by simp) hHc hHd
        (by exact hHi')
    have h_boundary : ∀ i : Fin (m + 1),
        (∫ (x : Fin m → ℝ) in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
           f i (i.insertNth (b i) x)) = 0 ∧
        (∫ (x : Fin m → ℝ) in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
           f i (i.insertNth (a i) x)) = 0 := by
      intro i
      have h1 : ∀ x, f i (i.insertNth (b i) x) = 0 := by
        intro x
        have h5 : (i.insertNth (b i) x) ∉ K' := by
          intro h6; have h7 := hK'_openbox h6; have h8 := h7 i
          simp [a, b, Fin.insertNth] at h8 <;> linarith
        have h9 : e.symm (i.insertNth (b i) x) ∉ K := by
          intro h10; exact h5 (by exact ⟨e.symm (i.insertNth (b i) x), h10, rfl⟩)
        have h10 : φ (e.symm (i.insertNth (b i) x)) = 0 := by
          have h11 : (e.symm (i.insertNth (b i) x)) ∉ Function.support φ := fun h12 => h9 (subset_closure h12)
          simpa [Function.mem_support] using h11
        have h_eq : f i (i.insertNth (b i) x) = φ (e.symm (i.insertNth (b i) x)) i := h_f_eq i (i.insertNth (b i) x)
        rw [h_eq, h10] <;> simp
      have h2 : ∀ x, f i (i.insertNth (a i) x) = 0 := by
        intro x
        have h5 : (i.insertNth (a i) x) ∉ K' := by
          intro h6; have h7 := hK'_openbox h6; have h8 := h7 i
          simp [a, b, Fin.insertNth] at h8 <;> linarith
        have h9 : e.symm (i.insertNth (a i) x) ∉ K := by
          intro h10; exact h5 (by exact ⟨e.symm (i.insertNth (a i) x), h10, rfl⟩)
        have h10 : φ (e.symm (i.insertNth (a i) x)) = 0 := by
          have h11 : (e.symm (i.insertNth (a i) x)) ∉ Function.support φ := fun h12 => h9 (subset_closure h12)
          simpa [Function.mem_support] using h11
        have h_eq : f i (i.insertNth (a i) x) = φ (e.symm (i.insertNth (a i) x)) i := h_f_eq i (i.insertNth (a i) x)
        rw [h_eq, h10] <;> simp
      constructor
      · have h3 : (fun x : Fin m → ℝ => f i (i.insertNth (b i) x)) = 0 := funext h1
        change ∫ (x : Fin m → ℝ) in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), (fun x : Fin m → ℝ => f i (i.insertNth (b i) x)) x = 0
        rw [h3] <;> simp
      · have h4 : (fun x : Fin m → ℝ => f i (i.insertNth (a i) x)) = 0 := funext h2
        change ∫ (x : Fin m → ℝ) in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), (fun x : Fin m → ℝ => f i (i.insertNth (a i) x)) x = 0
        rw [h4] <;> simp
    have h_sum : ∑ i : Fin (m + 1), ((∫ (x : Fin m → ℝ) in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        f i (i.insertNth (b i) x)) -
      ∫ (x : Fin m → ℝ) in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        f i (i.insertNth (a i) x)) = 0 := by
      apply Finset.sum_eq_zero; intro i _
      have h := h_boundary i; rw [h.1, h.2] <;> ring
    rw [h_sum] at h_main
    have h_outside : ∀ z, z ∉ Set.Icc a b → (∑ i, (f' i z) (Pi.single i 1)) = 0 := by
      intro z hz
      have h6 : e.symm z ∉ K := by
        intro h7; have h8 := hK'_openbox (by exact ⟨e.symm z, h7, rfl⟩)
        have h9 : z ∈ Set.Icc a b := by
          have h8' : ∀ i, z i ∈ Set.Ioo (a i) (b i) := by simpa [Set.mem_univ_pi] using h8
          exact ⟨fun i => (h8' i).1.le, fun i => (h8' i).2.le⟩
        exact hz h9
      rw [h_div_eq]
      exact h1_div (e.symm z) h6
    have h_eq1 : ∫ (z : Fin (m + 1) → ℝ), (∑ i, (f' i z) (Pi.single i 1)) =
        ∫ (z : Fin (m + 1) → ℝ) in Set.Icc a b, (∑ i, (f' i z) (Pi.single i 1)) := by
      rw [← integral_indicator (isClosed_Icc.measurableSet)]
      congr with z; by_cases h : z ∈ Set.Icc a b <;> simp [h, h_outside] <;> tauto
    have h_eq2 : ∫ (x : E (m + 1)), divergence φ x =
        ∫ (z : Fin (m + 1) → ℝ), (∑ i, (f' i z) (Pi.single i 1)) := by
      have h3 : ∀ (z : Fin (m + 1) → ℝ), (∑ i, (f' i z) (Pi.single i 1)) = divergence φ (e.symm z) := h_div_eq
      have h4 : ∫ (z : Fin (m + 1) → ℝ), (∑ i, (f' i z) (Pi.single i 1)) =
          ∫ (z : Fin (m + 1) → ℝ), divergence φ (e.symm z) := by
        congr with z; exact h3 z
      rw [h4]
      have h_eq_symm2 : (e.symm : (Fin (m + 1) → ℝ) → E (m + 1)) = e_me.symm := by
        funext x
        apply e.injective
        have h1 : e (e.symm x) = x := e.apply_symm_apply x
        have h2 : e (e_me.symm x) = x := by
          have h21 : e (e_me.symm x) = e_me (e_me.symm x) := by rw [←h_eq_fun]
          rw [h21, e_me.apply_symm_apply]
        rw [h1, h2]
      have h5 : ∫ (z : Fin (m + 1) → ℝ), divergence φ (e.symm z) = ∫ (x : E (m + 1)), divergence φ x := by
        have h6 : (fun z : Fin (m + 1) → ℝ => divergence φ (e.symm z)) = (divergence φ) ∘ e_me.symm :=
          congr_arg ((divergence φ) ∘ ·) h_eq_symm2
        rw [h6]
        exact he_mp_symm_me.integral_comp' (g := divergence φ)
      exact h5.symm
    rw [h_eq2, h_eq1, h_main]

-- ============================================================================
-- 2. χ_U · φ is smooth when φ vanishes near frontier U
-- ============================================================================

/-- If `φ` is smooth and supported away from `frontier U`, then `indicator U φ` is smooth. -/
lemma smooth_indicator_mul {U : Set (E n)} (hU : IsOpen U)
    {φ : E n → E n} (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ (frontier U)ᶜ) :
    ContDiff ℝ ∞ (Set.indicator U φ) := by
  let ψ : E n → E n := Set.indicator U φ
  have h_main : ∀ (x : E n), ∃ (Ux : Set (E n)), IsOpen Ux ∧ x ∈ Ux ∧
      ContDiffOn ℝ ∞ ψ Ux := by
    intro x
    by_cases hxU : x ∈ U
    · refine ⟨U, hU, hxU, ?_⟩
      have h_eq : ∀ y ∈ U, ψ y = φ y := by
        intro y hy; simp [ψ, Set.indicator_apply, hy]
      exact hφ.contDiffOn.congr h_eq
    · by_cases hxF : x ∈ frontier U
      · have h1 : x ∉ tsupport φ := by
          intro h2; exact hsub h2 hxF
        have h2 : ∃ (Vx : Set (E n)), IsOpen Vx ∧ x ∈ Vx ∧ ∀ y ∈ Vx, φ y = 0 := by
          let K := tsupport φ
          have hK_closed : IsClosed K := hsupp.isClosed
          refine ⟨Kᶜ, hK_closed.isOpen_compl, h1, fun y hy => ?_⟩
          have h4 : y ∉ Function.support φ := fun h5 => hy (subset_closure h5)
          simpa [Function.mem_support] using h4
        rcases h2 with ⟨Vx, hVx_open, hxV, hφ_zero⟩
        refine ⟨Vx, hVx_open, hxV, ?_⟩
        have h_eq : ∀ y ∈ Vx, ψ y = 0 := by
          intro y hy
          have h3 : φ y = 0 := hφ_zero y hy
          simp [ψ, Set.indicator_apply, h3]
        exact contDiff_const.contDiffOn.congr h_eq
      · have h_notin_U : x ∉ U := hxU
        have h_notin_interior : x ∉ interior U := fun h_int => h_notin_U (interior_subset h_int)
        have h_notin_closure : x ∉ closure U := by
          intro h
          exact hxF ⟨h, h_notin_interior⟩
        let W := (closure U)ᶜ
        have hW_open : IsOpen W := isClosed_closure.isOpen_compl
        have hxW : x ∈ W := h_notin_closure
        have hW_sub : W ⊆ Uᶜ := by
          intro y hy
          have h5 : y ∉ closure U := hy
          have h6 : y ∉ U := fun h7 => h5 (subset_closure h7)
          exact h6
        refine ⟨W, hW_open, hxW, ?_⟩
        have h_eq : ∀ y ∈ W, ψ y = 0 := by
          intro y hy
          have h4 : y ∉ U := hW_sub hy
          simp [ψ, Set.indicator_apply, h4]
        exact contDiff_const.contDiffOn.congr h_eq
  have h_main' : ∀ (x : E n), x ∈ Set.univ →
      ∃ (u : Set (E n)), IsOpen u ∧ x ∈ u ∧ ContDiffOn ℝ ∞ ψ (Set.univ ∩ u) := by
    intro x _
    rcases h_main x with ⟨Ux, hUx_open, hxUx, h_diff⟩
    refine ⟨Ux, hUx_open, hxUx, ?_⟩
    simpa using h_diff
  have h_on_univ : ContDiffOn ℝ ∞ ψ Set.univ :=
    contDiffOn_of_locally_contDiffOn (h := h_main')
  exact contDiffOn_univ.mp h_on_univ

/-- `div(indicator U φ) = indicator U (div φ)`. -/
lemma divergence_indicator_mul {U : Set (E n)} (hU : IsOpen U)
    {φ : E n → E n} (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ (frontier U)ᶜ) :
    ∀ x, divergence (Set.indicator U φ) x = Set.indicator U (divergence φ) x := by
  let ψ : E n → E n := Set.indicator U φ
  have hψ : ContDiff ℝ ∞ ψ := smooth_indicator_mul hU hφ hsupp hsub
  intro x
  by_cases hxU : x ∈ U
  · have h_loc : ∀ᶠ y in nhds x, ψ y = φ y := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      simp [ψ, Set.indicator_apply, hy]
    have h_eq : ∀ (i : Fin n), fderiv ℝ (fun y => ψ y i) x = fderiv ℝ (fun y => φ y i) x := by
      intro i
      have h_loc_i : ∀ᶠ y in nhds x, (ψ y i) = (φ y i) := by
        filter_upwards [h_loc] with y hy
        rw [hy]
      exact EventuallyEq.fderiv_eq h_loc_i
    have h_main : divergence ψ x = divergence φ x := by
      simp only [divergence, h_eq]
      <;> simp
    have h_ind : Set.indicator U (divergence φ) x = divergence φ x := by
      rw [Set.indicator_apply, if_pos hxU]
    rw [h_main, h_ind]
  · by_cases hxF : x ∈ frontier U
    · have h1 : x ∉ tsupport φ := by
        intro h2; exact hsub h2 hxF
      have h2 : ∃ (Vx : Set (E n)), IsOpen Vx ∧ x ∈ Vx ∧ ∀ y ∈ Vx, φ y = 0 := by
        let K := tsupport φ
        have hK_closed : IsClosed K := hsupp.isClosed
        refine ⟨Kᶜ, hK_closed.isOpen_compl, h1, fun y hy => ?_⟩
        have h4 : y ∉ Function.support φ := fun h5 => hy (subset_closure h5)
        simpa [Function.mem_support] using h4
      rcases h2 with ⟨Vx, hVx_open, hxV, hφ_zero⟩
      have h3 : ∀ᶠ y in nhds x, ψ y = 0 := by
        filter_upwards [hVx_open.mem_nhds hxV] with y hy
        have h4 : φ y = 0 := hφ_zero y hy
        simp [ψ, Set.indicator_apply, h4]
      have h_eq : ∀ (i : Fin n), fderiv ℝ (fun y => ψ y i) x = 0 := by
        intro i
        have h3_i : ∀ᶠ y in nhds x, (ψ y i) = (0 : ℝ) := by
          filter_upwards [h3] with y hy
          rw [hy] <;> simp
        have h4 : fderiv ℝ (fun y => ψ y i) x = fderiv ℝ (fun _ : E n => (0 : ℝ)) x :=
          EventuallyEq.fderiv_eq h3_i
        rw [h4]
        simp
      have h_main : divergence ψ x = 0 := by
        simp only [divergence, h_eq]
        <;> simp
      have h_ind : Set.indicator U (divergence φ) x = 0 := by
        rw [Set.indicator_apply, if_neg hxU] <;> simp
      rw [h_main, h_ind]
    · have h_notin_U : x ∉ U := hxU
      have h_notin_closure : x ∉ closure U := by
        intro h
        have h_int_U : interior U = U := hU.interior_eq
        have h_in_frontier : x ∈ frontier U := by
          have h_def : frontier U = closure U \ interior U := by
            exact Eq.symm (closure_sdiff_interior U)
          rw [h_def, h_int_U]
          exact ⟨h, h_notin_U⟩
        exact hxF h_in_frontier
      let W := (closure U)ᶜ
      have hW_open : IsOpen W := isClosed_closure.isOpen_compl
      have hxW : x ∈ W := h_notin_closure
      have h3 : ∀ᶠ y in nhds x, ψ y = 0 := by
        filter_upwards [hW_open.mem_nhds hxW] with y hy
        have h4 : y ∉ U := by
          have h5 : y ∉ closure U := hy
          exact fun h6 => h5 (subset_closure h6)
        simp [ψ, Set.indicator_apply, h4]
      have h_eq : ∀ (i : Fin n), fderiv ℝ (fun y => ψ y i) x = 0 := by
        intro i
        have h3_i : ∀ᶠ y in nhds x, (ψ y i) = (0 : ℝ) := by
          filter_upwards [h3] with y hy
          rw [hy] <;> simp
        have h4 : fderiv ℝ (fun y => ψ y i) x = fderiv ℝ (fun _ : E n => (0 : ℝ)) x :=
          EventuallyEq.fderiv_eq h3_i
        rw [h4] <;> simp
      have h_main : divergence ψ x = 0 := by
        simp only [divergence, h_eq] <;> simp
      have h_ind : Set.indicator U (divergence φ) x = 0 := by
        rw [Set.indicator_apply, if_neg hxU] <;> simp
      rw [h_main, h_ind]

-- ============================================================================
-- 3. Density of smooth functions in C_c supported in an open set
-- ============================================================================

/-- Smooth functions supported in `V` are uniformly dense in `C_c` supported in `V`. -/
lemma smooth_dense_in_cc_supported {V : Set (E n)} (hV : IsOpen V)
    (f : C_c(E n, ℝ)) (hsub : tsupport (f : E n → ℝ) ⊆ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : E n → ℝ), ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ V ∧ ∀ x, |g x - f x| < ε := by
  let f' : E n → ℝ := f
  have hf_uniform : UniformContinuous f' :=
    CompactlySupportedContinuousMapClass.uniformContinuous f
  rcases hf_uniform.exists_contDiff_dist_le hε with ⟨h, hh_diff, hh_approx⟩
  have hK_compact : IsCompact (tsupport f') := f.hasCompactSupport'
  rcases exists_smooth_cutoff_local hK_compact hV hsub with ⟨η, hη_diff, hη_supp, hη_one, hη_sub, hη_range⟩
  let g : E n → ℝ := fun x => η x * h x
  have hg_diff : ContDiff ℝ ∞ g := hη_diff.mul hh_diff
  have hg_supp : HasCompactSupport g := by
    have h1 : Function.support g ⊆ tsupport η := by
      intro x hx; by_contra h2
      have h3 : η x = 0 := by
        have h4 : x ∉ Function.support η := fun h5 => h2 (subset_closure h5)
        simpa [Function.mem_support] using h4
      have h4 : g x = 0 := by simp [g, h3]
      exact hx h4
    have h5 : tsupport g ⊆ tsupport η := closure_minimal h1 hη_supp.isClosed
    exact IsCompact.of_isClosed_subset hη_supp (isClosed_tsupport g) h5
  have h5 : tsupport g ⊆ tsupport η := by
    have h1 : Function.support g ⊆ tsupport η := by
      intro x hx; by_contra h2
      have h3 : η x = 0 := by
        have h4 : x ∉ Function.support η := fun h5 => h2 (subset_closure h5)
        simpa [Function.mem_support] using h4
      have h4 : g x = 0 := by simp [g, h3]
      exact hx h4
    exact closure_minimal h1 hη_supp.isClosed
  have hg_tsub : tsupport g ⊆ V := Set.Subset.trans h5 hη_sub
  have h_approx : ∀ x, |g x - f x| < ε := by
    intro x
    by_cases hx : x ∈ tsupport f'
    · have hη1 : η x = 1 := hη_one x hx
      rw [show g x = h x by simp [g, hη1]]
      exact hh_approx x
    · have h4 : x ∉ Function.support f := fun h5 => hx (subset_closure h5)
      have hf0 : f x = 0 := by
        simp only [Function.mem_support] at h4
        exact Classical.not_not.mp h4
      rw [hf0]
      have h_goal : |g x - (0 : ℝ)| = |g x| := by simp
      rw [h_goal]
      have h5 : |g x| = |η x| * |h x| := by simp [g, abs_mul] <;> ring
      rw [h5]
      have h6 : |η x| ≤ 1 := by
        have h61 : 0 ≤ η x := (hη_range x).1
        rw [abs_of_nonneg h61]
        exact (hη_range x).2
      have h7 : |h x| < ε := by
        have h8 : |h x - f x| < ε := hh_approx x
        rw [hf0] at h8
        simpa using h8
      calc |η x| * |h x| ≤ 1 * |h x| := by gcongr
        _ = |h x| := by ring
        _ < ε := h7
  exact ⟨g, hg_diff, hg_supp, hg_tsub, h_approx⟩

-- ============================================================================
-- 4. Signed measure variation vanishes on open set
-- ============================================================================

/-- If `∫ f dμ = 0` for all `f ∈ C_c` supported in open `V`, then `μ.totalVariation V = 0`. -/
lemma signedMeasure_variation_zero_of_forall_integral_eq_zero
    {μ : SignedMeasure (E n)} {V : Set (E n)} (hV : IsOpen V)
    (hfin : μ.totalVariation Set.univ < ⊤)
    (h : ∀ (f : C_c(E n, ℝ)), tsupport (f : E n → ℝ) ⊆ V →
        (∫ x, f x ∂μ.toJordanDecomposition.posPart) -
        (∫ x, f x ∂μ.toJordanDecomposition.negPart) = 0) :
    μ.totalVariation V = 0 := by
  let μpos := μ.toJordanDecomposition.posPart
  let μneg := μ.toJordanDecomposition.negPart
  have h_total : μpos Set.univ + μneg Set.univ = μ.totalVariation Set.univ := by
    simp [SignedMeasure.totalVariation] <;> rfl
  have hpos_fin : μpos Set.univ < ⊤ := by
    have h : μpos Set.univ ≤ μpos Set.univ + μneg Set.univ := le_self_add
    rw [h_total] at h; exact h.trans_lt hfin
  have hneg_fin : μneg Set.univ < ⊤ := by
    have h : μneg Set.univ ≤ μpos Set.univ + μneg Set.univ := le_add_self
    rw [h_total] at h; exact h.trans_lt hfin
  letI : IsFiniteMeasure μpos := ⟨hpos_fin⟩
  letI : IsFiniteMeasure μneg := ⟨hneg_fin⟩
  have h_eq : ∀ (f : C_c(E n, ℝ)), tsupport (f : E n → ℝ) ⊆ V →
      ∫ x, f x ∂μpos = ∫ x, f x ∂μneg := by
    intro f hf; have h1 := h f hf; linarith
  have h_reg_pos : μpos.Regular := by infer_instance
  have h_reg_neg : μneg.Regular := by infer_instance

  -- Helper: μ K ≤ ENNReal.ofReal (∫ f ∂μ) when indicator K 1 ≤ f
  have h_lower : ∀ (μ : Measure (E n)) [IsFiniteMeasure μ] (K : Set (E n)) (hK : IsCompact K)
      (f : C_c(E n, ℝ)) (h_one : ∀ x ∈ K, (f : E n → ℝ) x = 1) (h_nonneg : ∀ x, 0 ≤ f x),
      μ K ≤ ENNReal.ofReal (∫ x, f x ∂μ) := by
    intro μ _ K hK f h_one h_nonneg
    let ind : E n → ℝ := K.indicator 1
    have h9 : ∀ x, ind x ≤ f x := by
      intro x
      by_cases hx : x ∈ K
      · have h10 : ind x = 1 := by simp [ind, hx, Set.indicator_apply]
        have h11 : f x = 1 := h_one x hx
        rw [h10, h11] <;> norm_num
      · have h10 : ind x = 0 := by simp [ind, hx, Set.indicator_apply]
        have h11 : 0 ≤ f x := h_nonneg x
        rw [h10] <;> exact h11
    have h_ae_nonneg : 0 ≤ᵐ[μ] ind := by
      filter_upwards with x
      have h_ind : 0 ≤ ind x := by
        exact Set.indicator_nonneg (fun _ _ => by norm_num) x
      exact h_ind
    have h_ae_le : ind ≤ᵐ[μ] (f : E n → ℝ) := by
      filter_upwards with x; exact h9 x
    have h_int_f : Integrable f μ := CompactlySupportedContinuousMap.integrable f
    have h_int_ind : Integrable ind μ :=
      h_int_f.mono_nonneg (measurable_const.indicator hK.measurableSet).aestronglyMeasurable h_ae_nonneg h_ae_le
    have h_int1 : ∫ x, ind x ∂μ ≤ ∫ x, f x ∂μ :=
      integral_mono_of_nonneg h_ae_nonneg h_int_f h_ae_le
    have h_indicator : ∫ x, ind x ∂μ = μ.real K := integral_indicator_one hK.measurableSet
    rw [h_indicator] at h_int1
    have hK_fin : μ K < ⊤ := by
      have h_univ : μ Set.univ < ⊤ := by
        exact measure_lt_top μ Set.univ
      exact (measure_mono (Set.subset_univ K)).trans_lt h_univ
    have h_eq1 : μ K = ENNReal.ofReal (μ.real K) := by
      have h1 : μ.real K = (μ K).toReal := by rfl
      rw [h1]
      exact (ENNReal.ofReal_toReal hK_fin.ne).symm
    rw [h_eq1]
    exact ENNReal.ofReal_le_ofReal h_int1

  -- Helper: ENNReal.ofReal (∫ f ∂μ) ≤ μ O' when f ≤ indicator O' 1
  have h_upper : ∀ (μ : Measure (E n)) [IsFiniteMeasure μ] (O' : Set (E n))
      (hO'_open : IsOpen O') (f : C_c(E n, ℝ))
      (h_bound : ∀ x, (f : E n → ℝ) x ≤ O'.indicator 1 x) (h_nonneg : ∀ x, 0 ≤ f x),
      ENNReal.ofReal (∫ x, f x ∂μ) ≤ μ O' := by
    intro μ _ O' hO'_open f h_bound h_nonneg
    let ind : E n → ℝ := O'.indicator 1
    have h_ae_nonneg : 0 ≤ᵐ[μ] (f : E n → ℝ) := by
      filter_upwards with x; exact h_nonneg x
    have h_ae_le : (f : E n → ℝ) ≤ᵐ[μ] ind := by
      filter_upwards with x; exact h_bound x
    have h_int_ind : Integrable ind μ :=
      (integrable_const (1 : ℝ)).indicator hO'_open.measurableSet
    have h_int2 : ∫ x, f x ∂μ ≤ ∫ x, ind x ∂μ :=
      integral_mono_of_nonneg h_ae_nonneg h_int_ind h_ae_le
    have h_indicator : ∫ x, ind x ∂μ = μ.real O' := integral_indicator_one hO'_open.measurableSet
    rw [h_indicator] at h_int2
    have hO'_fin : μ O' < ⊤ := by
      have h_univ : μ Set.univ < ⊤ := by
        exact measure_lt_top μ Set.univ
      exact (measure_mono (Set.subset_univ O')).trans_lt h_univ
    have h_eq2 : ENNReal.ofReal (μ.real O') = μ O' := by
      have h1 : μ.real O' = (μ O').toReal := by rfl
      rw [h1]
      exact ENNReal.ofReal_toReal hO'_fin.ne
    calc ENNReal.ofReal (∫ x, f x ∂μ)
      ≤ ENNReal.ofReal (μ.real O') := ENNReal.ofReal_le_ofReal h_int2
      _ = μ O' := h_eq2

  -- Step 1: μpos(K) = μneg(K) for compact K ⊆ V
  have h_step1 : ∀ K, IsCompact K → K ⊆ V → μpos K = μneg K := by
    intro K hK hKsub
    have h1 : μpos K ≤ μneg K := by
      by_cases h_top : μneg K = ⊤
      · rw [h_top] <;> exact le_top
      · apply ENNReal.le_of_forall_pos_le_add
        intro ε hε _hbt
        have hε' : (↑ε : ENNReal) ≠ 0 := by exact_mod_cast hε.ne'
        rcases Set.exists_isOpen_lt_add K h_top hε' with ⟨O, hKO, hO_open, hOl⟩
        let O' := O ∩ V
        have hO'_open : IsOpen O' := hO_open.inter hV
        have hKO' : K ⊆ O' := fun x hx => ⟨hKO hx, hKsub hx⟩
        have hOl' : μneg O' < μneg K + (↑ε : ENNReal) :=
          (measure_mono Set.inter_subset_left).trans_lt hOl
        rcases exists_smooth_cutoff_local hK hO'_open hKO' with ⟨η, hη_diff, hη_supp, hη_one, hη_sub, hη_range⟩
        let η_c : C(E n, ℝ) := ⟨η, hη_diff.continuous⟩
        let f_cc : C_c(E n, ℝ) := ⟨η_c, hη_supp⟩
        have hf_sub : tsupport (f_cc : E n → ℝ) ⊆ V := hη_sub.trans Set.inter_subset_right
        have h_int_eq : ∫ x, f_cc x ∂μpos = ∫ x, f_cc x ∂μneg := h_eq f_cc hf_sub
        have h_nonneg : ∀ x, 0 ≤ f_cc x := fun x => (hη_range x).1
        have h_one : ∀ x ∈ K, f_cc x = 1 := by
          intro x hx; have h := hη_one x hx; simpa [f_cc, η_c] using h
        have h_bound : ∀ x, f_cc x ≤ O'.indicator 1 x := by
          intro x
          by_cases hx : x ∈ O'
          · calc f_cc x ≤ 1 := (hη_range x).2
              _ = O'.indicator 1 x := by
                simp [Set.indicator_apply, hx]
          · have h10 : x ∉ tsupport η := fun h => hx (hη_sub h)
            have h11 : η x = 0 := by
              by_contra h12
              have h13 : x ∈ Function.support η := by simpa [Function.mem_support] using h12
              have h14 : x ∈ tsupport η := subset_closure h13
              exact h10 h14
            have h15 : f_cc x = 0 := by
              have h16 : f_cc x = η x := by rfl
              rw [h16, h11]
            have h_eq : f_cc x = O'.indicator 1 x := by
              calc f_cc x = 0 := h15
                _ = O'.indicator 1 x := by simp [Set.indicator_apply, hx]
            exact h_eq.le
        have h_pos_le : μpos K ≤ ENNReal.ofReal (∫ x, f_cc x ∂μpos) :=
          h_lower μpos K hK f_cc h_one h_nonneg
        have h_neg_le : ENNReal.ofReal (∫ x, f_cc x ∂μneg) ≤ μneg O' :=
          h_upper μneg O' hO'_open f_cc h_bound h_nonneg
        have h_calc : μpos K < μneg K + (↑ε : ENNReal) := calc
          μpos K
            ≤ ENNReal.ofReal (∫ x, f_cc x ∂μpos) := h_pos_le
          _ = ENNReal.ofReal (∫ x, f_cc x ∂μneg) := by rw [h_int_eq]
          _ ≤ μneg O' := h_neg_le
          _ < μneg K + (↑ε : ENNReal) := hOl'
        exact le_of_lt h_calc
    have h2 : μneg K ≤ μpos K := by
      by_cases h_top : μpos K = ⊤
      · rw [h_top] <;> exact le_top
      · apply ENNReal.le_of_forall_pos_le_add
        intro ε hε _hbt
        have hε' : (↑ε : ENNReal) ≠ 0 := by exact_mod_cast hε.ne'
        rcases Set.exists_isOpen_lt_add K h_top hε' with ⟨O, hKO, hO_open, hOl⟩
        let O' := O ∩ V
        have hO'_open : IsOpen O' := hO_open.inter hV
        have hKO' : K ⊆ O' := fun x hx => ⟨hKO hx, hKsub hx⟩
        have hOl' : μpos O' < μpos K + (↑ε : ENNReal) :=
          (measure_mono Set.inter_subset_left).trans_lt hOl
        rcases exists_smooth_cutoff_local hK hO'_open hKO' with ⟨η, hη_diff, hη_supp, hη_one, hη_sub, hη_range⟩
        let η_c : C(E n, ℝ) := ⟨η, hη_diff.continuous⟩
        let f_cc : C_c(E n, ℝ) := ⟨η_c, hη_supp⟩
        have hf_sub : tsupport (f_cc : E n → ℝ) ⊆ V := hη_sub.trans Set.inter_subset_right
        have h_int_eq : ∫ x, f_cc x ∂μpos = ∫ x, f_cc x ∂μneg := h_eq f_cc hf_sub
        have h_nonneg : ∀ x, 0 ≤ f_cc x := fun x => (hη_range x).1
        have h_one : ∀ x ∈ K, f_cc x = 1 := by
          intro x hx; have h := hη_one x hx; simpa [f_cc, η_c] using h
        have h_bound : ∀ x, f_cc x ≤ O'.indicator 1 x := by
          intro x
          by_cases hx : x ∈ O'
          · calc f_cc x ≤ 1 := (hη_range x).2
              _ = O'.indicator 1 x := by
                simp [Set.indicator_apply, hx]
          · have h10 : x ∉ tsupport η := fun h => hx (hη_sub h)
            have h11 : η x = 0 := by
              by_contra h12
              have h13 : x ∈ Function.support η := by simpa [Function.mem_support] using h12
              have h14 : x ∈ tsupport η := subset_closure h13
              exact h10 h14
            have h15 : f_cc x = 0 := by
              have h16 : f_cc x = η x := by rfl
              rw [h16, h11]
            have h_eq : f_cc x = O'.indicator 1 x := by
              calc f_cc x = 0 := h15
                _ = O'.indicator 1 x := by simp [Set.indicator_apply, hx]
            exact h_eq.le
        have h_neg_le : μneg K ≤ ENNReal.ofReal (∫ x, f_cc x ∂μneg) :=
          h_lower μneg K hK f_cc h_one h_nonneg
        have h_pos_le : ENNReal.ofReal (∫ x, f_cc x ∂μpos) ≤ μpos O' :=
          h_upper μpos O' hO'_open f_cc h_bound h_nonneg
        have h_calc : μneg K < μpos K + (↑ε : ENNReal) := calc
          μneg K
            ≤ ENNReal.ofReal (∫ x, f_cc x ∂μneg) := h_neg_le
          _ = ENNReal.ofReal (∫ x, f_cc x ∂μpos) := by rw [h_int_eq]
          _ ≤ μpos O' := h_pos_le
          _ < μpos K + (↑ε : ENNReal) := hOl'
        exact le_of_lt h_calc
    exact le_antisymm h1 h2

  -- Step 2: μpos(W) = μneg(W) for open W ⊆ V
  have h_step2 : ∀ W, IsOpen W → W ⊆ V → μpos W = μneg W := by
    intro W hW_open hWsub
    have h1 : μpos W = ⨆ (K : Set (E n)) (_ : K ⊆ W) (_ : IsCompact K), μpos K :=
      IsOpen.measure_eq_iSup_isCompact hW_open μpos
    have h2 : μneg W = ⨆ (K : Set (E n)) (_ : K ⊆ W) (_ : IsCompact K), μneg K :=
      IsOpen.measure_eq_iSup_isCompact hW_open μneg
    rw [h1, h2]; congr with K; congr with hKsub; congr with hK
    exact h_step1 K hK (hKsub.trans hWsub)

  -- Step 3: μpos(E) = μneg(E) for all measurable E ⊆ V
  have h_step3 : ∀ E, MeasurableSet E → E ⊆ V → μpos E = μneg E := by
    intro E hE hEsub
    have h1 : μpos E ≤ μneg E := by
      by_cases h_top : μneg E = ⊤
      · rw [h_top] <;> exact le_top
      · apply ENNReal.le_of_forall_pos_le_add
        intro ε hε _hbt
        have hε' : (↑ε : ENNReal) ≠ 0 := by exact_mod_cast hε.ne'
        rcases Set.exists_isOpen_lt_add E h_top hε' with ⟨O, hEO, hO_open, hOl⟩
        let O' := O ∩ V
        have hO'_open : IsOpen O' := hO_open.inter hV
        have hEO' : E ⊆ O' := fun x hx => ⟨hEO hx, hEsub hx⟩
        have hOl' : μneg O' < μneg E + (↑ε : ENNReal) :=
          (measure_mono Set.inter_subset_left).trans_lt hOl
        have h_eq2 : μpos O' = μneg O' := h_step2 O' hO'_open Set.inter_subset_right
        have h_calc : μpos E < μneg E + (↑ε : ENNReal) := calc
          μpos E ≤ μpos O' := measure_mono hEO'
          _ = μneg O' := h_eq2
          _ < μneg E + (↑ε : ENNReal) := hOl'
        exact le_of_lt h_calc
    have h2 : μneg E ≤ μpos E := by
      by_cases h_top : μpos E = ⊤
      · rw [h_top] <;> exact le_top
      · apply ENNReal.le_of_forall_pos_le_add
        intro ε hε _hbt
        have hε' : (↑ε : ENNReal) ≠ 0 := by exact_mod_cast hε.ne'
        rcases Set.exists_isOpen_lt_add E h_top hε' with ⟨O, hEO, hO_open, hOl⟩
        let O' := O ∩ V
        have hO'_open : IsOpen O' := hO_open.inter hV
        have hEO' : E ⊆ O' := fun x hx => ⟨hEO hx, hEsub hx⟩
        have hOl' : μpos O' < μpos E + (↑ε : ENNReal) :=
          (measure_mono Set.inter_subset_left).trans_lt hOl
        have h_eq2 : μpos O' = μneg O' := h_step2 O' hO'_open Set.inter_subset_right
        have h_calc : μneg E < μpos E + (↑ε : ENNReal) := calc
          μneg E ≤ μneg O' := measure_mono hEO'
          _ = μpos O' := h_eq2.symm
          _ < μpos E + (↑ε : ENNReal) := hOl'
        exact le_of_lt h_calc
    exact le_antisymm h1 h2

  -- Step 4: Mutual singularity gives μpos(V) = μneg(V) = 0
  have h_sing : μpos ⟂ₘ μneg := μ.toJordanDecomposition.mutuallySingular
  rcases h_sing with ⟨A, hA_meas, hApos, hAneg⟩
  have hV_meas : MeasurableSet V := hV.measurableSet
  have hAcompl_meas : MeasurableSet Aᶜ := hA_meas.compl
  have h4 : μpos (V ∩ A) = 0 := by
    exact measure_mono_null (show (V ∩ A) ⊆ A from Set.inter_subset_right) hApos
  have h5 : μneg (V ∩ Aᶜ) = 0 := by
    exact measure_mono_null (show (V ∩ Aᶜ) ⊆ Aᶜ from Set.inter_subset_right) hAneg
  have h6 : μpos (V ∩ A) = μneg (V ∩ A) :=
    h_step3 (V ∩ A) (hV_meas.inter hA_meas) Set.inter_subset_left
  have h7 : μneg (V ∩ A) = 0 := by
    have h71 : μpos (V ∩ A) = μneg (V ∩ A) := h6
    rw [←h71]; exact h4
  have h8 : μpos (V ∩ Aᶜ) = μneg (V ∩ Aᶜ) :=
    h_step3 (V ∩ Aᶜ) (hV_meas.inter hAcompl_meas) Set.inter_subset_left
  have h9 : μpos (V ∩ Aᶜ) = 0 := by
    have h91 : μpos (V ∩ Aᶜ) = μneg (V ∩ Aᶜ) := h8
    rw [h91]; exact h5
  letI hVA_meas : MeasurableSet (V ∩ A) := hV_meas.inter hA_meas
  letI hVAcompl_meas : MeasurableSet (V ∩ Aᶜ) := hV_meas.inter hAcompl_meas
  have h_disj : Disjoint (V ∩ A) (V ∩ Aᶜ) := by
    rw [Set.disjoint_left]
    intro x hx
    intro h2
    exact h2.2 hx.2
  have h10 : μpos V = 0 := by
    have h11 : V = (V ∩ A) ∪ (V ∩ Aᶜ) := by ext x; simp [Classical.em] <;> tauto
    have h_union : μpos ((V ∩ A) ∪ (V ∩ Aᶜ)) = μpos (V ∩ A) + μpos (V ∩ Aᶜ) :=
      measure_union h_disj (hV_meas.inter hAcompl_meas)
    rw [h11, h_union, h4, h9] <;> norm_num
  have h12 : μneg V = 0 := by
    have h13 : V = (V ∩ A) ∪ (V ∩ Aᶜ) := by ext x; simp [Classical.em] <;> tauto
    have h_union2 : μneg ((V ∩ A) ∪ (V ∩ Aᶜ)) = μneg (V ∩ A) + μneg (V ∩ Aᶜ) :=
      measure_union h_disj (hV_meas.inter hAcompl_meas)
    rw [h13, h_union2, h7, h5] <;> norm_num
  have h14 : μ.totalVariation V = μpos V + μneg V := by
    simp [SignedMeasure.totalVariation] <;> rfl
  rw [h14, h10, h12] <;> simp

-- ============================================================================
-- 5. Main theorem
-- ============================================================================



-- ============================================================================
-- 4b. Extend vanishing from smooth to C_c functions by density
-- ============================================================================

/-- Helper: if a `C_c` function satisfies `|f x| < ε` everywhere, its sup norm is `< ε`. -/
lemma cc_norm_strict_lt_of_forall_abs_lt {f : C_c(E n, ℝ)} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x, |f x| < ε) : ‖Cc.toC₀ f‖ < ε := by
  let K := tsupport (f : E n → ℝ)
  have hK : IsCompact K := f.hasCompactSupport'
  let hfunc : E n → ℝ := fun x => |f x|
  have hfunc_cont : Continuous hfunc := by continuity
  by_cases hK_empty : K = ∅
  · have h0 : f = 0 := by
      ext x
      have h11 : x ∉ K := by rw [hK_empty]; simp
      have h12 : x ∉ Function.support (f : E n → ℝ) := fun h13 => h11 (subset_closure h13)
      simpa [Function.mem_support] using h12
    have h_norm0 : ‖Cc.toC₀ f‖ = 0 := by
      have h12 : Cc.toC₀ f = 0 := by
        exact congr_arg Cc.toC₀ h0
      rw [h12]
      exact norm_zero
    rw [h_norm0] <;> linarith
  · have hK_nonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
    rcases hK.exists_isMaxOn hK_nonempty (hfunc_cont.continuousOn) with ⟨x, hxK, hx_max⟩
    have hmax : hfunc x < ε := h x
    have h4' : ∀ y ∈ K, hfunc y ≤ hfunc x := hx_max
    have h4 : ∀ y, hfunc y ≤ hfunc x := by
      intro y
      by_cases hy : y ∈ K
      · exact h4' y hy
      · have hfy : f y = 0 := by
          have h13 : y ∉ Function.support (f : E n → ℝ) := fun h14 => hy (subset_closure h14)
          simpa [Function.mem_support] using h13
        have h5 : hfunc y = 0 := by
          simp only [hfunc, hfy, abs_zero]
        rw [h5] <;> exact abs_nonneg _
    have h61 : ‖(Cc.toC₀ f).toBCF‖ = ⨆ y, hfunc y := by
      rw [BoundedContinuousFunction.norm_eq_iSup_norm]
      <;> rfl
    have h6 : ‖Cc.toC₀ f‖ ≤ hfunc x := by
      have h62 : ‖Cc.toC₀ f‖ = ‖(Cc.toC₀ f).toBCF‖ := ZeroAtInftyContinuousMap.norm_toBCF_eq_norm.symm
      rw [h62, h61]
      exact ciSup_le h4
    have h7 : hfunc x ≤ ‖Cc.toC₀ f‖ := by
      have h8 : hfunc x ≤ ‖(Cc.toC₀ f).toBCF‖ :=
        BoundedContinuousFunction.norm_coe_le_norm (Cc.toC₀ f).toBCF x
      simpa [hfunc, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using h8
    have h9 : ‖Cc.toC₀ f‖ = hfunc x := by linarith
    rw [h9] <;> exact hmax

/-- Extend vanishing of integrals from smooth functions to all `C_c` functions by density.

Given a signed measure `μ` of finite total variation and an open set `V`, if
`∫ ψ ∂μ = 0` for every smooth compactly supported `ψ` with `tsupport ψ ⊆ V`, then
the same holds for every `f ∈ C_c` supported in `V`. -/
lemma signedMeasure_integral_zero_extend
    {V : Set (E n)} (hV : IsOpen V)
    {μ : SignedMeasure (E n)} (hfin : μ.totalVariation Set.univ < ⊤)
    (h_smooth : ∀ (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ V →
        (∫ x, ψ x ∂μ.toJordanDecomposition.posPart) -
        (∫ x, ψ x ∂μ.toJordanDecomposition.negPart) = 0) :
    ∀ (f : C_c(E n, ℝ)), tsupport (f : E n → ℝ) ⊆ V →
        (∫ x, f x ∂μ.toJordanDecomposition.posPart) -
        (∫ x, f x ∂μ.toJordanDecomposition.negPart) = 0 := by
  let μpos := μ.toJordanDecomposition.posPart
  let μneg := μ.toJordanDecomposition.negPart
  let C : ℝ := (μ.totalVariation Set.univ).toReal
  have hC_nonneg : 0 ≤ C := by positivity
  have hpos_le : μpos Set.univ ≤ μ.totalVariation Set.univ := by
    simpa [SignedMeasure.totalVariation] using le_self_add
  have hneg_le : μneg Set.univ ≤ μ.totalVariation Set.univ := by
    simpa [SignedMeasure.totalVariation] using le_add_self
  have hpos_fin : μpos Set.univ < ⊤ := hpos_le.trans_lt hfin
  have hneg_fin : μneg Set.univ < ⊤ := hneg_le.trans_lt hfin
  letI : IsFiniteMeasure μpos := ⟨hpos_fin⟩
  letI : IsFiniteMeasure μneg := ⟨hneg_fin⟩
  have h_cont : ∀ (g : C_c(E n, ℝ)),
      |(∫ x, g x ∂μpos) - (∫ x, g x ∂μneg)| ≤ C * ‖Cc.toC₀ g‖ := by
    intro g
    have h1 : |(∫ x, g x ∂μpos) - (∫ x, g x ∂μneg)| ≤
        (∫ x, |g x| ∂μpos) + (∫ x, |g x| ∂μneg) := by
      have h2 : |(∫ x, g x ∂μpos) - (∫ x, g x ∂μneg)| ≤
          |(∫ x, g x ∂μpos)| + |(∫ x, g x ∂μneg)| := abs_sub _ _
      have h3 : |(∫ x, g x ∂μpos)| ≤ ∫ x, |g x| ∂μpos :=
        MeasureTheory.abs_integral_le_integral_abs
      have h4 : |(∫ x, g x ∂μneg)| ≤ ∫ x, |g x| ∂μneg :=
        MeasureTheory.abs_integral_le_integral_abs
      linarith
    have h9 : ∀ x, |g x| ≤ ‖Cc.toC₀ g‖ := by
      intro x
      have h10 : |g x| ≤ ‖(Cc.toC₀ g).toBCF‖ :=
        BoundedContinuousFunction.norm_coe_le_norm (Cc.toC₀ g).toBCF x
      rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at h10
      exact h10
    have h_nonneg_pos : 0 ≤ᵐ[μpos] (fun x : E n => |g x|) := by
      filter_upwards with x; exact abs_nonneg (g x)
    have h_le_pos : (fun x : E n => |g x|) ≤ᵐ[μpos] (fun x : E n => ‖Cc.toC₀ g‖) := by
      filter_upwards with x; exact h9 x
    have h_int_g_pos : Integrable g μpos := CompactlySupportedContinuousMap.integrable g
    have hfi_pos : Integrable (fun x : E n => |g x|) μpos := h_int_g_pos.abs
    have hgi_pos : Integrable (fun x : E n => ‖Cc.toC₀ g‖) μpos := integrable_const _
    have h6 : ∫ x, |g x| ∂μpos ≤ (μpos Set.univ).toReal * ‖Cc.toC₀ g‖ := by
      have h10 : ∫ x, |g x| ∂μpos ≤ ∫ x, ‖Cc.toC₀ g‖ ∂μpos :=
        integral_mono_of_nonneg h_nonneg_pos hgi_pos h_le_pos
      have h11 : ∫ x, ‖Cc.toC₀ g‖ ∂μpos = (μpos Set.univ).toReal * ‖Cc.toC₀ g‖ := by
        simpa [Measure.real_def, smul_eq_mul] using integral_const (‖Cc.toC₀ g‖)
      rw [h11] at h10; exact h10
    have h_nonneg_neg : 0 ≤ᵐ[μneg] (fun x : E n => |g x|) := by
      filter_upwards with x; exact abs_nonneg (g x)
    have h_le_neg : (fun x : E n => |g x|) ≤ᵐ[μneg] (fun x : E n => ‖Cc.toC₀ g‖) := by
      filter_upwards with x; exact h9 x
    have h_int_g_neg : Integrable g μneg := CompactlySupportedContinuousMap.integrable g
    have hfi_neg : Integrable (fun x : E n => |g x|) μneg := h_int_g_neg.abs
    have hgi_neg : Integrable (fun x : E n => ‖Cc.toC₀ g‖) μneg := integrable_const _
    have h7 : ∫ x, |g x| ∂μneg ≤ (μneg Set.univ).toReal * ‖Cc.toC₀ g‖ := by
      have h10 : ∫ x, |g x| ∂μneg ≤ ∫ x, ‖Cc.toC₀ g‖ ∂μneg :=
        integral_mono_of_nonneg h_nonneg_neg hgi_neg h_le_neg
      have h11 : ∫ x, ‖Cc.toC₀ g‖ ∂μneg = (μneg Set.univ).toReal * ‖Cc.toC₀ g‖ := by
        simpa [Measure.real_def, smul_eq_mul] using integral_const (‖Cc.toC₀ g‖)
      rw [h11] at h10; exact h10
    have h8' : (μpos Set.univ).toReal + (μneg Set.univ).toReal = C := by
      have h9 : (μpos Set.univ + μneg Set.univ).toReal = (μpos Set.univ).toReal + (μneg Set.univ).toReal := by
        rw [ENNReal.toReal_add hpos_fin.ne hneg_fin.ne]
      have h10 : μpos Set.univ + μneg Set.univ = μ.totalVariation Set.univ := by
        simp [SignedMeasure.totalVariation] <;> rfl
      rw [←h9, h10] <;> rfl
    have h5 : (∫ x, |g x| ∂μpos) + (∫ x, |g x| ∂μneg) ≤ C * ‖Cc.toC₀ g‖ := by
      calc (∫ x, |g x| ∂μpos) + (∫ x, |g x| ∂μneg)
          ≤ (μpos Set.univ).toReal * ‖Cc.toC₀ g‖ + (μneg Set.univ).toReal * ‖Cc.toC₀ g‖ := by gcongr
        _ = ((μpos Set.univ).toReal + (μneg Set.univ).toReal) * ‖Cc.toC₀ g‖ := by ring
        _ = C * ‖Cc.toC₀ g‖ := by rw [h8'] <;> ring
    exact h1.trans h5
  intro f hsub
  by_contra h_ne
  set Df := (∫ x, f x ∂μpos) - (∫ x, f x ∂μneg) with hDf
  have h_pos : 0 < |Df| := abs_pos.mpr h_ne
  let ε : ℝ := |Df| / (C + 1)
  have hε_pos : 0 < ε := by
    apply div_pos h_pos; linarith
  rcases smooth_dense_in_cc_supported hV f hsub hε_pos with ⟨g, hg_diff, hg_supp, hg_sub, hg_approx⟩
  let g_cont : C(E n, ℝ) := ⟨g, hg_diff.continuous⟩
  let g_cc : C_c(E n, ℝ) := ⟨g_cont, hg_supp⟩
  have hg_eq : (∫ x, g_cc x ∂μpos) - (∫ x, g_cc x ∂μneg) = 0 := by
    have h_eq1 : (∫ x, g_cc x ∂μpos) = (∫ x, g x ∂μpos) := by rfl
    have h_eq2 : (∫ x, g_cc x ∂μneg) = (∫ x, g x ∂μneg) := by rfl
    rw [h_eq1, h_eq2]
    exact h_smooth g hg_diff hg_supp hg_sub
  have h1 : ∀ x, |(f - g_cc) x| < ε := by
    intro x
    have h2 : |g x - f x| < ε := hg_approx x
    have h3 : (f - g_cc) x = f x - g x := by rfl
    rw [h3]
    have h4 : |f x - g x| = |g x - f x| := by
      rw [show f x - g x = -(g x - f x) by ring, abs_neg]
    rw [h4]; exact h2
  have h_norm : ‖Cc.toC₀ (f - g_cc)‖ < ε :=
    cc_norm_strict_lt_of_forall_abs_lt hε_pos h1
  have h_eq_sub : (fun x : E n => (f - g_cc) x) = (fun x => f x) - (fun x => g_cc x) := by funext x; rfl
  have h_int_sub_pos : ∫ x, (f - g_cc) x ∂μpos = (∫ x, f x ∂μpos) - (∫ x, g_cc x ∂μpos) := by
    exact integral_sub (CompactlySupportedContinuousMap.integrable f) (CompactlySupportedContinuousMap.integrable g_cc)
  have h_int_sub_neg : ∫ x, (f - g_cc) x ∂μneg = (∫ x, f x ∂μneg) - (∫ x, g_cc x ∂μneg) := by
    exact integral_sub (CompactlySupportedContinuousMap.integrable f) (CompactlySupportedContinuousMap.integrable g_cc)
  set Dfg := (∫ x, (f - g_cc) x ∂μpos) - (∫ x, (f - g_cc) x ∂μneg) with hDfg
  have h9 : Dfg = Df := by
    simp only [hDfg, hDf, h_int_sub_pos, h_int_sub_neg]
    have h10 : (∫ x, g_cc x ∂μpos) - (∫ x, g_cc x ∂μneg) = 0 := hg_eq
    linarith
  have h10 : |Dfg| ≤ C * ‖Cc.toC₀ (f - g_cc)‖ := h_cont (f - g_cc)
  rw [h9] at h10
  have h11 : C * ε < |Df| := by
    have h : C * ε = C * |Df| / (C + 1) := by
      dsimp only [ε] <;> ring
    rw [h]
    have h_pos2 : 0 < C + 1 := by linarith
    have h2 : C * |Df| / (C + 1) < |Df| := by
      have h3 : C * |Df| < |Df| * (C + 1) := by
        have h4 : 0 < |Df| := h_pos
        nlinarith
      calc C * |Df| / (C + 1)
          < |Df| * (C + 1) / (C + 1) := by gcongr
        _ = |Df| := by
          field_simp [h_pos2.ne'] <;> ring
    exact h2
  have h12 : C * ‖Cc.toC₀ (f - g_cc)‖ < |Df| := by
    calc C * ‖Cc.toC₀ (f - g_cc)‖ ≤ C * ε := by gcongr
      _ < |Df| := h11
  exact not_le.mpr h12 h10

-- ============================================================================
-- 5. Main theorem
-- ============================================================================

/-- **Perimeter measure is supported on the frontier.**

For an open set `U`, `perimeterMeasure U (frontier U)ᶜ = 0`. -/
theorem perimeterMeasure_support_frontier
    {U : Set (E n)} (hU : IsOpen U) :
    perimeterMeasure U (frontier U)ᶜ = 0 := by
  by_cases hfin : perimeter U < ⊤
  · -- Finite perimeter case
    let V := (frontier U)ᶜ
    have hV_open : IsOpen V := isClosed_frontier.isOpen_compl

    let μ : Fin n → SignedMeasure (E n) := fun i =>
      Classical.choose (distributionalDerivative_signedMeasure U i hfin)
    have hμ_main : ∀ i,
        (∀ (ψ : E n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hsupp : HasCompactSupport ψ),
          (∫ x in U, fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) =
            (∫ x, ψ x ∂(μ i).toJordanDecomposition.posPart) -
            (∫ x, ψ x ∂(μ i).toJordanDecomposition.negPart)) ∧
        ((μ i).totalVariation Set.univ ≤ perimeter U) := by
      intro i; exact Classical.choose_spec (distributionalDerivative_signedMeasure U i hfin)

    -- Step A: For smooth scalar ψ supported in V, ∫_U ∂_i ψ = 0
    have hA : ∀ (i : Fin n) (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ V → ∫ x in U, fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) = 0 := by
      intro i ψ hψ hsupp hsub
      let e_i : E n := EuclideanSpace.single i (1 : ℝ)
      let φ : E n → E n := fun x => ψ x • e_i
      have h_e_i : ContDiff ℝ ∞ (fun (_ : E n) => e_i) := contDiff_const
      have hφ : ContDiff ℝ ∞ φ := hψ.smul h_e_i
      have hφ_supp : HasCompactSupport φ := by
        have h_supp_incl : Function.support φ ⊆ Function.support ψ := by
          intro x hx; by_contra h2
          have h3 : ψ x = 0 := by simpa [Function.mem_support] using h2
          have h4 : φ x = 0 := by simp [φ, h3]
          exact hx h4
        exact HasCompactSupport.mono hsupp h_supp_incl
      have hφ_sub : tsupport φ ⊆ V := by
        have h1_supp : Function.support φ ⊆ Function.support ψ := by
          intro x hx; by_contra h2
          have h3 : ψ x = 0 := by simpa [Function.mem_support] using h2
          have h4 : φ x = 0 := by simp [φ, h3]
          exact hx h4
        have h1' : Function.support φ ⊆ tsupport ψ := h1_supp.trans subset_closure
        have h2 : tsupport φ ⊆ tsupport ψ := closure_minimal h1' hsupp.isClosed
        exact h2.trans hsub
      let ψU : E n → E n := Set.indicator U φ
      have hψU : ContDiff ℝ ∞ ψU := smooth_indicator_mul hU hφ hφ_supp hφ_sub
      have hψU_supp : HasCompactSupport ψU := by
        have h1 : Function.support ψU ⊆ tsupport φ := by
          intro x hx; by_contra h2
          have h3 : x ∉ Function.support φ := fun h4 => h2 (subset_closure h4)
          have h4 : φ x = 0 := by simpa [Function.mem_support] using h3
          have h5 : ψU x = 0 := by simp [ψU, Set.indicator_apply, h4]
          exact hx h5
        have h5 : tsupport ψU ⊆ tsupport φ := closure_minimal h1 hφ_supp.isClosed
        exact IsCompact.of_isClosed_subset hφ_supp (isClosed_tsupport ψU) h5
      have hdiv : ∀ x, divergence ψU x = Set.indicator U (divergence φ) x :=
        divergence_indicator_mul hU hφ hφ_supp hφ_sub
      have h_main : ∫ x, divergence ψU x = 0 := integral_divergence_eq_zero hψU hψU_supp
      have h_eq : ∫ x, divergence ψU x = ∫ x in U, divergence φ x := by
        have h1 : ∫ x, divergence ψU x = ∫ x, Set.indicator U (divergence φ) x := by
          have h_eq_fun : (divergence ψU) = Set.indicator U (divergence φ) := by
            funext x
            exact hdiv x
          rw [h_eq_fun]
        rw [h1]
        exact integral_indicator (hU.measurableSet)
      rw [h_eq] at h_main
      have hdiv_smul : divergence φ = fun x => fderiv ℝ ψ x e_i := divergence_smul_const hψ
      have h_goal : ∫ x in U, divergence φ x = ∫ x in U, fderiv ℝ ψ x e_i := by
        rw [hdiv_smul]
      rw [h_goal] at h_main
      exact h_main

    -- Step B: For smooth scalar ψ supported in V, ∫ ψ dμ_i = 0
    have hB : ∀ (i : Fin n) (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ V →
        (∫ x, ψ x ∂(μ i).toJordanDecomposition.posPart) -
        (∫ x, ψ x ∂(μ i).toJordanDecomposition.negPart) = 0 := by
      intro i ψ hψ hsupp hsub
      have h1 := (hμ_main i).1 ψ hψ hsupp
      have h2 : ∫ x in U, fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) = 0 :=
        hA i ψ hψ hsupp hsub
      rw [h2] at h1
      exact h1.symm

    -- Step C: Extend to all f ∈ C_c supported in V by density
    have hC : ∀ (i : Fin n), ∀ (f : CompactlySupportedContinuousMap (E n) ℝ), tsupport (f : E n → ℝ) ⊆ V →
        (∫ x, f x ∂(μ i).toJordanDecomposition.posPart) -
        (∫ x, f x ∂(μ i).toJordanDecomposition.negPart) = 0 := by
      intro i
      have hfin_i : (μ i).totalVariation Set.univ < ⊤ :=
        (hμ_main i).2.trans_lt hfin
      exact signedMeasure_integral_zero_extend hV_open hfin_i (hB i)

    -- Step D: Each μ_i.totalVariation(V) = 0
    have hD_tv : ∀ i, (μ i).totalVariation V = 0 := by
      intro i
      have hfin_i : (μ i).totalVariation Set.univ < ⊤ := (hμ_main i).2.trans_lt hfin
      exact signedMeasure_variation_zero_of_forall_integral_eq_zero hV_open hfin_i (hC i)

    -- Step D': Each μ_i.variation(V) = 0 (from totalVariation V = 0)
    have hD_var : ∀ i, (μ i).variation V = 0 := by
      intro i
      have hTV : (μ i).totalVariation V = 0 := hD_tv i
      have hV_meas : MeasurableSet V := hV_open.measurableSet
      have h_restrict_zero : (μ i).restrict V = 0 := by
        ext A hA
        have h1 : (μ i).totalVariation (A ∩ V) = 0 := by
          apply measure_mono_null _ hTV
          exact Set.inter_subset_right
        have h2 : (μ i) (A ∩ V) = 0 := SignedMeasure.null_of_totalVariation_zero (μ i) h1
        have h3 : (μ i).restrict V A = (μ i) (A ∩ V) := by
          exact VectorMeasure.restrict_apply (μ i) hV_meas hA
        rw [h3]
        exact h2
      have h2 : ((μ i).restrict V).variation = 0 := by
        rw [VectorMeasure.variation_eq_zero.mpr h_restrict_zero]
      have h3 : ((μ i).restrict V).variation = (μ i).variation.restrict V :=
        VectorMeasure.variation_restrict hV_meas
      rw [h3] at h2
      have h4 : (μ i).variation.restrict V = 0 := h2
      have h5 : (μ i).variation V = 0 := by
        have h6 : (μ i).variation.restrict V Set.univ = (μ i).variation V := by
          simp [Measure.restrict_apply, hV_meas]
        rw [←h6, h4] <;> simp
      exact h5

    -- Step E: D.variation(V) = 0
    let D := distributionalDerivative U
    have hD_eq : D = ∑ i : Fin n, (μ i).mapRange (coordHom i) (coordHom_cont i) :=
      distributionalDerivative_eq U hfin
    have h_var_sum : D.variation ≤ ∑ i : Fin n, ((μ i).mapRange (coordHom i) (coordHom_cont i)).variation := by
      rw [hD_eq]
      exact VectorMeasure.variation_finsetSum_le (Finset.univ) _
    have h_each : ∀ i, ((μ i).mapRange (coordHom i) (coordHom_cont i)).variation V = 0 := by
      intro i
      have h_eq_var : ((μ i).mapRange (coordHom i) (coordHom_cont i)).variation = (μ i).variation :=
        mapRange_coordHom_variation_eq
      rw [h_eq_var]
      exact hD_var i
    have h_sum : (∑ i : Fin n, ((μ i).mapRange (coordHom i) (coordHom_cont i)).variation) V = 0 := by
      have h : ∀ i ∈ Finset.univ, ((μ i).mapRange (coordHom i) (coordHom_cont i)).variation V = 0 := by
        intro i _
        exact h_each i
      simpa [Finset.sum_apply] using Finset.sum_congr rfl h
    have h_final : D.variation V = 0 := by
      have h1 : D.variation V ≤ (∑ i : Fin n, ((μ i).mapRange (coordHom i) (coordHom_cont i)).variation) V :=
        h_var_sum V
      rw [h_sum] at h1
      exact le_zero_iff.mp h1
    simpa [perimeterMeasure] using h_final

  · -- Infinite perimeter case
    have hD_zero : distributionalDerivative U = 0 := by
      rw [distributionalDerivative, dif_neg hfin]
    have hμ_zero : perimeterMeasure U = 0 := by
      simp [perimeterMeasure, hD_zero]
    rw [hμ_zero] <;> simp

end Geometry.Perimeter
