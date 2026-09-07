module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.Defs
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.LocalStraightening
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.PositiveRankLocal
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section


namespace ForMathlib.Analysis.Calculus.Sard.General

open MeasureTheory Module
open scoped ContDiff

/-- The j-th derivative stratification: points where all derivatives up to
    order j vanish. -/
def flatStratum {m n : ℕ} (f : E m → E n) (j : ℕ) : Set (E m) :=
  {x | ∀ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ j →
    iteratedFDeriv ℝ ℓ f x = 0}

lemma exists_scalar_nonzero_deriv_corrected {m n : ℕ} (f : E m → E n)
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (hj : j ≥ 1) (x : E m)
    (hx1 : x ∈ flatStratum f j)
    (hx2 : x ∉ flatStratum f (j + 1)) :
    ∃ (h : E m → ℝ) (_ : ContDiff ℝ ∞ h),
      (∀ y ∈ flatStratum f j, h y = 0) ∧
      (fderiv ℝ h x ≠ 0) := by
  let g : E m → _ := fun y => iteratedFDeriv ℝ j f y
  set a : WithTop ℕ∞ := ∞
  set b : WithTop ℕ∞ := (j : WithTop ℕ∞)
  have hmn : a + b ≤ a := by
    exact le_refl (a + b)
  have hg_diff : ContDiff ℝ ∞ g := by
    exact ContDiff.iteratedFDeriv_right hf hmn
  have h1 : iteratedFDeriv ℝ (j + 1) f x ≠ 0 := by
    by_contra h
    have h_contra : x ∈ flatStratum f (j + 1) := by
      intro ℓ hℓ
      by_cases h_lower : ℓ ≤ j
      · exact hx1 ℓ ⟨hℓ.1, h_lower⟩
      · have h_eq : ℓ = j + 1 := by omega
        rw [h_eq]
        exact h
    exact hx2 h_contra
  let e : (_ ≃ₗᵢ[ℝ] _) := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E m) (E n)
  have h_eq_fun : iteratedFDeriv ℝ (j + 1) f = e.symm ∘ fderiv ℝ g :=
    iteratedFDeriv_succ_eq_comp_left (f := f) (n := j)
  have h2 : fderiv ℝ g x ≠ 0 := by
    intro h
    have h4 : iteratedFDeriv ℝ (j + 1) f x = e.symm (fderiv ℝ g x) := by
      rw [h_eq_fun]
      rfl
    have h5 : e.symm (fderiv ℝ g x) = e.symm 0 := by rw [h]
    have h6 : e.symm (0) = 0 := by
      exact e.symm.map_zero
    have h3 : iteratedFDeriv ℝ (j + 1) f x = 0 := by
      rw [h4, h5, h6]
    exact h1 h3
  let v : _ := fderiv ℝ g x
  have hv_ne_zero : v ≠ 0 := h2
  have h_exists_vec : ∃ (e_vec : E m), v e_vec ≠ 0 := by
    by_contra h
    push Not at h
    have h4 : v = 0 := by
      exact ContinuousLinearMap.ext h
    exact hv_ne_zero h4
  rcases h_exists_vec with ⟨e_vec, he⟩
  let z := v e_vec
  have hz_ne_zero : z ≠ 0 := he
  have hnz_norm : ‖z‖ ≠ 0 := by
    simpa [norm_ne_zero_iff] using hz_ne_zero
  have h_exists_L : ∃ (L : (_) →L[ℝ] ℝ), L z ≠ 0 := by
    have h_main : ∃ (g' : StrongDual ℝ (_)), ‖g'‖ = 1 ∧ g' z = ‖z‖ :=
      exists_dual_vector (𝕜 := ℝ) (E := _) (x := z) hnz_norm
    rcases h_main with ⟨L, _, hLz⟩
    refine ⟨L, ?_⟩
    rw [hLz]
    exact hnz_norm
  rcases h_exists_L with ⟨L, hL⟩
  let h : E m → ℝ := fun y => L (g y)
  have hL_diff : ContDiff ℝ ∞ (L : _ → ℝ) := L.contDiff
  have hh : ContDiff ℝ ∞ h := hL_diff.comp hg_diff
  have h_vanish : ∀ y ∈ flatStratum f j, h y = 0 := by
    intro y hy
    have h4 : iteratedFDeriv ℝ j f y = 0 := hy j ⟨hj, by linarith⟩
    have h5 : g y = 0 := by simpa [g] using h4
    simp [h, h5]
  have h_g_diffentiable : Differentiable ℝ g := hg_diff.differentiable (by simp)
  have h1_gdiff : DifferentiableAt ℝ g x := h_g_diffentiable.differentiableAt
  have h_has_fderiv_g : HasFDerivAt g v x := h1_gdiff.hasFDerivAt
  have h_has_fderiv : HasFDerivAt h (L.comp v) x :=
    L.hasFDerivAt.comp x h_has_fderiv_g
  have h_fderiv : fderiv ℝ h x = L.comp v := h_has_fderiv.fderiv
  have h_main : fderiv ℝ h x ≠ 0 := by
    rw [h_fderiv]
    intro h_contra
    have h6 : (L.comp v) e_vec = 0 := by
      rw [h_contra]
      simp
    have h7 : (L.comp v) e_vec = L (v e_vec) := by rfl
    rw [h7] at h6
    exact hL h6
  exact ⟨h, hh, h_vanish, h_main⟩

/-- Lemma 10 (Existence of scalar function with nonzero derivative).
    If j ≥ 1 and x ∈ C_j \ C_{j+1}, then not all (j+1)-th derivatives vanish.
    In particular, there exists a scalar component h : E m → ℝ
    (a coordinate of the j-th derivative) such that h = 0 on C_j and dh_x ≠ 0.
    (Note: j ≥ 1 is needed; j = 0 is false since C_0 = univ.) -/
theorem exists_scalar_nonzero_deriv {m n : ℕ} (f : E m → E n)
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (hj : j ≥ 1) (x : E m)
    (hx1 : x ∈ flatStratum f j)
    (hx2 : x ∉ flatStratum f (j + 1)) :
    ∃ (h : E m → ℝ) (_ : ContDiff ℝ ∞ h),
      (∀ y ∈ flatStratum f j, h y = 0) ∧
      (fderiv ℝ h x ≠ 0) :=
  exists_scalar_nonzero_deriv_corrected f hf j hj x hx1 hx2

lemma range_surjective_of_nonzero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : E →L[ℝ] ℝ) (hl : l ≠ 0) : LinearMap.range l.toLinearMap = ⊤ := by
  have h1 : ∃ (x0 : E), l x0 ≠ 0 := by
    by_contra h
    push Not at h
    have h2 : l = 0 := by
      ext x
      exact h x
    exact hl h2
  rcases h1 with ⟨x0, hx0⟩
  have h_main : Function.Surjective l.toLinearMap := by
    intro r
    use (r / l x0) • x0
    simp [hx0]
  exact LinearMap.range_eq_top.mpr h_main

lemma case_hx_ne_zero {m : ℕ}
    (h : E m → ℝ) (hh : ContDiff ℝ ∞ h) (x : E m) (h_x_ne_zero : h x ≠ 0) :
    ∃ (N : Set (E m)) (_ : IsOpen N) (_ : x ∈ N)
      (ψ : E (m - 1) → E m) (_ : ContDiff ℝ ∞ ψ),
      {y ∈ N | h y = 0} ⊆ Set.range ψ := by
  have h_cont : Continuous h := hh.continuous
  have h3 : IsOpen {y : E m | h y ≠ 0} := isOpen_ne.preimage h_cont
  have h4 : x ∈ {y : E m | h y ≠ 0} := h_x_ne_zero
  have h2 : {y : E m | h y ≠ 0} ∈ nhds x := h3.mem_nhds h4
  rcases mem_nhds_iff.mp h2 with ⟨N, hNsub, hNopen, hxN⟩
  have hN_prop : ∀ y ∈ N, h y ≠ 0 := fun y hy => hNsub hy
  have h_empty : ∀ z, z ∉ {y ∈ N | h y = 0} := by
    intro z hz
    have h1 : z ∈ N := hz.1
    have h2 : h z = 0 := hz.2
    have h3 : h z ≠ 0 := hN_prop z h1
    exact h3 h2
  have h_subset : {y ∈ N | h y = 0} ⊆ Set.range (fun (_ : E (m - 1)) => (0 : E m)) := by
    intro z hz
    exfalso
    exact h_empty z hz
  let ψ : E (m - 1) → E m := fun (_ : E (m - 1)) => (0 : E m)
  have hψ : ContDiff ℝ ∞ ψ := by
    fun_prop
  exact ⟨N, hNopen, hxN, ψ, hψ, h_subset⟩

lemma smooth_bump_annihilate {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (φ₀ : V → E) (U : Set V) (hU : IsOpen U) (h1 : ContDiffOn ℝ ∞ φ₀ U)
  (b : V → ℝ) (hb : ContDiff ℝ ∞ b) (hbsub : tsupport b ⊆ U) (x : E) :
  ContDiff ℝ ∞ (fun z : V => b z • φ₀ z + (1 - b z) • x) := by
  have h_main : ∀ (z0 : V), ContDiffAt ℝ ∞ (fun z : V => b z • φ₀ z + (1 - b z) • x) z0 := by
    intro z0
    by_cases h : z0 ∈ tsupport b
    ·
      have h2 : z0 ∈ U := hbsub h
      have h3 : ContDiffAt ℝ ∞ φ₀ z0 := h1.contDiffAt (hU.mem_nhds h2)
      have h4 : ContDiffAt ℝ ∞ b z0 := hb.contDiffAt
      have h5 : ContDiffAt ℝ ∞ (fun z : V => b z • φ₀ z) z0 := by
        exact h4.smul h3
      have h6 : ContDiffAt ℝ ∞ (fun z : V => (1 - b z) • x) z0 := by
        have h7 : ContDiffAt ℝ ∞ (fun z : V => (1 - b z)) z0 := by
          exact contDiffAt_const.sub h4
        exact h7.smul contDiffAt_const
      exact h5.add h6
    ·
      have h_tsupport_closed : IsClosed (tsupport b) := isClosed_tsupport b
      have h_compl_open : IsOpen (tsupport b)ᶜ := h_tsupport_closed.isOpen_compl
      have h3 : (tsupport b)ᶜ ∈ nhds z0 := h_compl_open.mem_nhds h
      rcases mem_nhds_iff.mp h3 with ⟨W, hWsub, hWopen, hzW⟩
      have hW_prop : ∀ z ∈ W, b z = 0 := by
        intro z hz
        have h4 : z ∉ tsupport b := hWsub hz
        exact image_eq_zero_of_notMem_tsupport (hWsub hz)
      have h_eq : ∀ z ∈ W, (b z • φ₀ z + (1 - b z) • x) = x := by
        intro z hz
        have hbz : b z = 0 := hW_prop z hz
        simp [hbz]
      have h_ev : ∀ᶠ z in nhds z0, (b z • φ₀ z + (1 - b z) • x) = x := by
        filter_upwards [hWopen.mem_nhds hzW] with z hz
        exact h_eq z hz
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const h_ev
  have h : ContDiff ℝ ∞ (fun z : V => b z • φ₀ z + (1 - b z) • x) := by
    exact contDiff_iff_contDiffAt.mpr h_main
  exact h

lemma finrank_ker_eq {m : ℕ} (hm_pos : 0 < m) {f' : E m →L[ℝ] ℝ} (hf' : LinearMap.range f'.toLinearMap = ⊤) :
    Module.finrank ℝ f'.ker = m - 1 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f'.toLinearMap
  have h2 : Module.finrank ℝ (E m) = m := by simp [E]
  have h3 : Module.finrank ℝ (LinearMap.range f'.toLinearMap) = 1 := by
    rw [hf']
    simp
  rw [h3, h2] at h1
  have h4 : 1 + Module.finrank ℝ f'.ker = m := h1
  have h5 : Module.finrank ℝ f'.ker = m - 1 := by
    omega
  exact h5

lemma helper_get_open_nhds {X : Type*} [TopologicalSpace X] {x : X} {P : X → Prop}
    {N : Set X} (hN : N ∈ nhds x) (hP : ∀ᶠ y in nhds x, P y) :
    ∃ (N2 : Set X), IsOpen N2 ∧ x ∈ N2 ∧ N2 ⊆ N ∧ (∀ y ∈ N2, P y) := by
  let s : Set X := N ∩ {y | P y}
  have hs : s ∈ nhds x := Filter.inter_mem hN hP
  have h_main : ∃ (t : Set X), t ⊆ s ∧ IsOpen t ∧ x ∈ t := (mem_nhds_iff).mp hs
  rcases h_main with ⟨N2, hN2_sub, hN2_open, hxN2⟩
  refine' ⟨N2, hN2_open, hxN2, _ , _⟩
  · intro y hy
    have h : y ∈ s := hN2_sub hy
    exact h.1
  · intro y hy
    have h : y ∈ s := hN2_sub hy
    exact h.2

lemma helper_full_rank_to_equiv {m : ℕ} (hm_pos : 0 < m) (y : E m) (H : E m → ℝ × E (m - 1))
  (_ : ContDiffAt ℝ ∞ H y) (h_rank : Module.finrank ℝ (LinearMap.range (fderiv ℝ H y).toLinearMap) = m) :
  ∃ (f'_y : (E m) ≃L[ℝ] (ℝ × E (m - 1))),
    (f'_y : (E m) →L[ℝ] (ℝ × E (m - 1))) = fderiv ℝ H y := by
  let L := (fderiv ℝ H y).toLinearMap
  have h_finrank_Em : Module.finrank ℝ (E m) = m := by
    simp [E]
  have h_finrank_prod : Module.finrank ℝ (ℝ × E (m - 1)) = m := by
    simp [E, Module.finrank_prod]
    omega
  have h5 : Module.finrank ℝ (LinearMap.range L) = Module.finrank ℝ (ℝ × E (m - 1)) := by
    calc
      Module.finrank ℝ (LinearMap.range L) = m := h_rank
      _ = Module.finrank ℝ (ℝ × E (m - 1)) := h_finrank_prod.symm
  have h_range_top : LinearMap.range L = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    exact h5
  have h_surj : Function.Surjective L := by
    rwa [LinearMap.range_eq_top] at h_range_top
  have h_finrank_eq2 : Module.finrank ℝ (E m) = Module.finrank ℝ (ℝ × E (m - 1)) := by
    rw [h_finrank_Em, h_finrank_prod]
  have h_inj : Function.Injective L := by
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank_eq2).mpr h_surj
  have h_bij : Function.Bijective L := ⟨h_inj, h_surj⟩
  let eL_y : (E m) ≃ₗ[ℝ] (ℝ × E (m - 1)) := LinearEquiv.ofBijective L h_bij
  refine ⟨eL_y.toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  change (eL_y z) = (fderiv ℝ H y) z
  rfl

/-- Lemma 11 (Hypersurface containment via implicit function theorem).
    Given h : E m → ℝ with C^∞ smoothness and dh_x ≠ 0, there exists
    a neighborhood N of x and a C^∞ parametrization ψ : E (m-1) → E m
    such that {y ∈ N | h y = 0} ⊆ range ψ.
    (This is the implicit function theorem: h(y) = 0 defines a smooth
    hypersurface near x.) -/
theorem hypersurface_containment {m : ℕ} (hm_pos : 0 < m)
    (h : E m → ℝ) (hh : ContDiff ℝ ∞ h) (x : E m)
    (h_deriv_nonzero : fderiv ℝ h x ≠ 0) :
    ∃ (N : Set (E m)) (_ : IsOpen N) (_ : x ∈ N)
      (ψ : E (m - 1) → E m) (_ : ContDiff ℝ ∞ ψ),
      {y ∈ N | h y = 0} ⊆ Set.range ψ := by
  by_cases h_x_zero : h x = 0
  · -- Case h x = 0: apply implicit function theorem
    let l : (E m) →L[ℝ] ℝ := fderiv ℝ h x
    have hl_nonzero : l ≠ 0 := h_deriv_nonzero
    have hl_range : LinearMap.range l.toLinearMap = ⊤ := range_surjective_of_nonzero l hl_nonzero
    have h1_surj : Function.Surjective l.toLinearMap := LinearMap.range_eq_top.mp hl_range
    have h_finrank_ker : Module.finrank ℝ l.ker = m - 1 := finrank_ker_eq hm_pos hl_range
    have h_finrank_eq : Module.finrank ℝ (E (m - 1)) = Module.finrank ℝ l.ker := by
      simp [E, h_finrank_ker]
    have h_nonempty : Nonempty ( (E (m - 1)) ≃ₗ[ℝ] l.ker) :=
      FiniteDimensional.nonempty_linearEquiv_of_finrank_eq h_finrank_eq
    let e_K : (E (m - 1)) ≃ₗ[ℝ] l.ker := Classical.choice h_nonempty
    haveI : PolynormableSpace ℝ (E m) :=
      (norm_withSeminorms ℝ (E m)).toPolynormableSpace
    have hK_closed : l.ker.ClosedComplemented := Submodule.ClosedComplemented.of_finiteDimensional l.ker
    have h4 : ∃ (q : Submodule ℝ (E m)), IsCompl l.ker q := hK_closed.exists_isClosed_isCompl.imp (fun q hq => hq.2)
    rcases h4 with ⟨q, hq_isCompl⟩
    let proj : (E m) →ₗ[ℝ] l.ker := Submodule.projectionOnto l.ker q hq_isCompl
    let p2 : (E m) →ₗ[ℝ] (E (m - 1)) := e_K.symm.comp proj
    let T : (E m) →ₗ[ℝ] (ℝ × E (m - 1)) := {
      toFun := fun y : E m => (l y, p2 y),
      map_add' := by
        intro y z
        ext <;> simp [map_add]
      map_smul' := by
        intro c y
        ext <;> simp [map_smul] }
    have h_inj : Function.Injective T := by
      intro y z hyz
      have h5 : l y = l z := by
        exact congrArg Prod.fst hyz
      have h6 : p2 y = p2 z := by
        exact congrArg Prod.snd hyz
      let w := y - z
      have hw1 : l w = 0 := by
        simpa [w, map_sub] using sub_eq_zero.mpr h5
      have hwK : w ∈ l.ker := hw1
      let w_K : l.ker := ⟨w, hwK⟩
      have h_proj_w : proj w = w_K := by
        exact Submodule.projectionOnto_apply_left hq_isCompl w_K
      have h7 : p2 w = 0 := by
        simpa [w, map_sub] using sub_eq_zero.mpr h6
      have h8 : e_K.symm (proj w) = 0 := h7
      have h9 : proj w = 0 := by
        have h91 : e_K.symm (proj w) = e_K.symm 0 := by
          rw [h8, map_zero]
        exact e_K.symm.injective h91
      have h10 : w_K = 0 := by
        have h101 : (proj w : l.ker) = w_K := h_proj_w
        have h102 : (proj w : l.ker) = 0 := by
          exact_mod_cast h9
        rw [←h101, h102]
      have h11 : w = 0 := Subtype.ext_iff.mp h10
      exact sub_eq_zero.mp h11
    have h_finrank_eq2 : Module.finrank ℝ (E m) = Module.finrank ℝ (ℝ × E (m - 1)) := by
      simp [E]
      omega
    have h_surj : Function.Surjective T :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank_eq2).mp h_inj
    have h_bij : Function.Bijective T := ⟨h_inj, h_surj⟩
    let eL : (E m) ≃ₗ[ℝ] (ℝ × E (m - 1)) := LinearEquiv.ofBijective T h_bij
    let eL' : (E m) ≃L[ℝ] (ℝ × E (m - 1)) := eL.toContinuousLinearEquiv
    let H : E m → ℝ × E (m - 1) := fun y => (h y, p2 y)
    have hp2_diff : ContDiff ℝ ∞ (fun y : E m => p2 y) := by
      exact p2.toContinuousLinearMap.contDiff
    have hH_diff : ContDiff ℝ ∞ H := by
      exact ContDiff.prodMk hh hp2_diff
    have h_ne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
    have h_diff : Differentiable ℝ h := hh.differentiable h_ne
    have h_diff_at : DifferentiableAt ℝ h x := h_diff.differentiableAt
    have h_hasFDeriv : HasFDerivAt h l x := h_diff_at.hasFDerivAt
    have h_p2_hasFDeriv : HasFDerivAt (fun y : E m => p2 y) p2.toContinuousLinearMap x :=
      p2.toContinuousLinearMap.hasFDerivAt
    have h_H_hasFDeriv : HasFDerivAt H (eL' : (E m) →L[ℝ] (ℝ × E (m - 1))) x :=
      HasFDerivAt.prodMk h_hasFDeriv h_p2_hasFDeriv
    have hH_at : ContDiffAt ℝ ∞ H x := hH_diff.contDiffAt
    have h_fderiv_eq : fderiv ℝ H x = (eL' : (E m) →L[ℝ] (ℝ × E (m - 1))) :=
      h_H_hasFDeriv.fderiv
    have h_H_hasStrictFDeriv : HasStrictFDerivAt H (eL' : (E m) →L[ℝ] (ℝ × E (m - 1))) x := by
      have h1 : HasStrictFDerivAt H (fderiv ℝ H x) x := hH_at.hasStrictFDerivAt h_ne
      rw [h_fderiv_eq] at h1
      exact h1
    let e : OpenPartialHomeomorph (E m) (ℝ × E (m - 1)) :=
      (hH_at.toOpenPartialHomeomorph (𝕂 := ℝ) (hf' := h_H_hasFDeriv) (hn := h_ne))
    let N : Set (E m) := e.source
    let V : Set (ℝ × E (m - 1)) := e.target
    have hN_open : IsOpen N := e.open_source
    have hV_open : IsOpen V := e.open_target
    have hxN : x ∈ N := by
      exact HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source h_H_hasStrictFDeriv
    have h_left_inv : ∀ y ∈ N, e.symm (e y) = y := fun y hy => e.left_inv hy
    have h_right_inv : ∀ z ∈ V, e (e.symm z) = z := fun z hz => e.right_inv hz
    have h_eq1 : ∀ y ∈ N, e y = H y := by
      intro y _
      rfl
    let z0 : E (m - 1) := (H x).2
    have hz0_in_V : (0, z0) ∈ V := by
      have h1 : H x = e x := by rfl
      have h2 : e x ∈ V := e.mapsTo hxN
      have h3 : H x ∈ V := by
        rw [h1]
        exact h2
      have h4 : (H x).1 = h x := by rfl
      have h5 : (H x).1 = (0, z0).1 := by
        simp [h4, h_x_zero]
      have h6 : (H x).2 = (0, z0).2 := by
        simp [z0]
      have h7 : H x = (0, z0) := Prod.ext h5 h6
      rw [h7] at h3
      exact h3
    let V2 : Set (E (m - 1)) := {z | (0, z) ∈ V}
    have hV2_open : IsOpen V2 := by
      let f : E (m - 1) → (ℝ × E (m - 1)) := fun z => (0, z)
      have h_cont : Continuous f := by fun_prop
      have h_eq : V2 = f ⁻¹' V := by rfl
      rw [h_eq]
      exact h_cont.isOpen_preimage V hV_open
    have hz0_in_V2 : z0 ∈ V2 := hz0_in_V
    have h_inv_diff : ContDiffAt ℝ ∞ e.symm (e x) :=
      (hH_at.to_localInverse (𝕂 := ℝ) (hf' := h_H_hasFDeriv) (hn := h_ne))
    have h1_cont : Continuous (fun y : E m => fderiv ℝ H y) :=
      hH_diff.continuous_fderiv (by simp)
    let hrank : (E m) → ℕ := fun y => Module.finrank ℝ (LinearMap.range (fderiv ℝ H y).toLinearMap)
    have h_rank_cont : IsOpen {L : (E m) →L[ℝ] (ℝ × E (m - 1)) | (m - 1) < Module.finrank ℝ (LinearMap.range L.toLinearMap)} :=
      rank_lower_semicontinuous (r := m - 1)
    let S : Set (E m) := (fun y : E m => fderiv ℝ H y) ⁻¹' {L : (E m) →L[ℝ] (ℝ × E (m - 1)) | (m - 1) < Module.finrank ℝ (LinearMap.range L.toLinearMap)}
    have hS_open : IsOpen S := h_rank_cont.preimage h1_cont
    have h_rank_x : hrank x = m := by
      dsimp only [hrank]
      rw [h_fderiv_eq]
      have h_range : LinearMap.range (eL' : (E m) →L[ℝ] (ℝ × E (m - 1))).toLinearMap = ⊤ :=
        LinearMap.range_eq_top.mpr eL'.toLinearEquiv.surjective
      have h : Module.finrank ℝ (LinearMap.range (eL' : (E m) →L[ℝ] (ℝ × E (m - 1))).toLinearMap) = m := by
        rw [h_range]
        simp [E]
        omega
      exact h
    have h_x_in_S : x ∈ S := by
      have h : (m - 1) < hrank x := by
        rw [h_rank_x]
        omega
      exact h
    have hS_nhds : S ∈ nhds x := hS_open.mem_nhds h_x_in_S
    rcases mem_nhds_iff.mp hS_nhds with ⟨U', hU'_sub, hU'_open, hxU'⟩
    have h_rank_full : ∀ y ∈ U', hrank y = m := by
      intro y hy
      have h2 : (m - 1) < hrank y := hU'_sub hy
      let L := (fderiv ℝ H y).toLinearMap
      have h3 : Module.finrank ℝ (LinearMap.range L) ≤ Module.finrank ℝ (ℝ × E (m - 1)) :=
        Submodule.finrank_le (LinearMap.range L)
      have h4 : hrank y ≤ m := by
        dsimp only [hrank] at *
        have h5 : Module.finrank ℝ (ℝ × E (m - 1)) = m := by
          simp [E, Module.finrank_prod]
          omega
        rw [h5] at h3
        exact h3
      omega
    let U'' := N ∩ U'
    have hU''_open : IsOpen U'' := hN_open.inter hU'_open
    have hxU'' : x ∈ U'' := ⟨hxN, hxU'⟩
    let V'' := e '' U''
    have hV''_open : IsOpen V'' := by
      have h_sub : U'' ⊆ e.source := fun x hx => hx.1
      have h_eq : e.source ∩ U'' = U'' := by
        ext x
        simp only [Set.mem_inter_iff]
        constructor
        · intro h
          exact h.2
        · intro h
          exact ⟨h_sub h, h⟩
      have h_goal : IsOpen (e '' (e.source ∩ U'')) := OpenPartialHomeomorph.isOpen_image_source_inter e hU''_open
      have h_eq2 : e '' (e.source ∩ U'') = e '' U'' := by
        rw [h_eq]
      rw [h_eq2] at h_goal
      exact h_goal
    have hex_V'' : e x ∈ V'' := ⟨x, hxU'', rfl⟩
    have h_main : ContDiffOn ℝ ∞ e.symm V'' := by
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      have hy_N : y ∈ N := hy.1
      have hy_U' : y ∈ U' := hy.2
      have hry : hrank y = m := h_rank_full y hy_U'
      have hH_at_y : ContDiffAt ℝ ∞ H y := hH_diff.contDiffAt
      have h_diff_at_y : DifferentiableAt ℝ H y := hH_at_y.differentiableAt h_ne
      have h_H_hasFDeriv_y : HasFDerivAt H (fderiv ℝ H y) y :=
        h_diff_at_y.hasFDerivAt
      have h_finrank_eq : Module.finrank ℝ (E m) = Module.finrank ℝ (ℝ × E (m - 1)) := by
        simp [E]
        omega
      let L := (fderiv ℝ H y).toLinearMap
      rcases helper_full_rank_to_equiv hm_pos y H hH_at_y hry with ⟨f'_y, h_eq_map⟩
      have h_H_hasFDeriv_y' : HasFDerivAt H (f'_y : (E m) →L[ℝ] (ℝ × E (m - 1))) y := by
        rw [h_eq_map]
        exact h_H_hasFDeriv_y
      let g := hH_at_y.localInverse h_H_hasFDeriv_y' h_ne
      have h_inv_diff_y : ContDiffAt ℝ ∞ g (H y) :=
        hH_at_y.to_localInverse (𝕂 := ℝ) (hf' := h_H_hasFDeriv_y') (hn := h_ne)
      have h_g_cont : ContinuousAt g (H y) := h_inv_diff_y.continuousAt
      have h_strict_y : HasStrictFDerivAt H (f'_y : (E m) →L[ℝ] (ℝ × E (m - 1))) y := by
        have h_raw : HasStrictFDerivAt H (fderiv ℝ H y) y := hH_at_y.hasStrictFDerivAt h_ne
        rw [h_eq_map]
        exact h_raw
      have h_right_inv : ∀ᶠ (w : ℝ × E (m - 1)) in nhds (H y), H (g w) = w :=
        h_strict_y.eventually_right_inverse
      have h1 : H y ∈ V := e.mapsTo hy_N
      have h_g_Hy_in_N : g (H y) ∈ N := by
        have h_g_Hy : g (H y) = y := ContDiffAt.localInverse_apply_image hH_at_y h_H_hasFDeriv_y' h_ne
        rw [h_g_Hy]
        exact hy_N
      have h_g_in_N : ∀ᶠ (w : ℝ × E (m - 1)) in nhds (H y), g w ∈ N :=
        h_g_cont (hN_open.mem_nhds h_g_Hy_in_N)
      have h_eq_on : ∀ᶠ (w : ℝ × E (m - 1)) in nhds (H y), g w = e.symm w := by
        filter_upwards [hV_open.mem_nhds h1, h_right_inv, h_g_in_N] with w hw hw2 hw3
        have h2 : e.symm w ∈ N := e.map_target hw
        have h3 : e (g w) = w := by
          have h4 : e (g w) = H (g w) := by
            rw [h_eq1 (g w) hw3]
          rw [h4, hw2]
        have h5 : e (g w) = e (e.symm w) := by
          rw [h3, e.right_inv hw]
        have h6 : g w = e.symm w := e.injOn hw3 h2 h5
        exact h6
      have h_eq_on' : e.symm =ᶠ[nhds (H y)] g := by
        filter_upwards [h_eq_on] with w hw
        exact hw.symm
      have h_final : ContDiffAt ℝ ∞ e.symm (H y) := h_inv_diff_y.congr_of_eventuallyEq h_eq_on'
      have h_ey_eq : e y = H y := by rfl
      rw [h_ey_eq] at *
      simpa [V''] using h_final.contDiffWithinAt
    have hV''_in_nhds : V'' ∈ nhds (e x) := hV''_open.mem_nhds hex_V''
    have h_exists : ∃ (W : Set (ℝ × E (m - 1))), W ∈ nhds (e x) ∧ ContDiffOn ℝ ∞ e.symm W :=
      ⟨V'', hV''_in_nhds, h_main⟩
    rcases h_exists with ⟨W_nhds, hW_in_nhds, hW_diff⟩
    have hV_in_nhds : V ∈ nhds (e x) := hV_open.mem_nhds (e.mapsTo hxN)
    have h_inter_in_nhds : W_nhds ∩ V ∈ nhds (e x) := Filter.inter_mem hW_in_nhds hV_in_nhds
    rcases mem_nhds_iff.mp h_inter_in_nhds with ⟨W_int, hW_int_sub, hW_int_open, hW_int_in⟩
    have hW_int_sub_V : W_int ⊆ V := by
      intro z hz
      have h2 : z ∈ W_nhds ∩ V := hW_int_sub hz
      exact h2.2
    have hW_int_sub_Wnhds : W_int ⊆ W_nhds := fun x hx => (hW_int_sub hx).1
    let W' : Set (ℝ × E (m - 1)) := W_int
    have hW'_open : IsOpen W' := hW_int_open
    have hex_W' : e x ∈ W' := hW_int_in
    have hW'_diff : ContDiffOn ℝ ∞ e.symm W' := hW_diff.mono hW_int_sub_Wnhds
    have hW'_sub_V : W' ⊆ V := hW_int_sub_V
    let g : E (m - 1) → E m := fun z => e.symm (0, z)
    let W2 : Set (E (m - 1)) := {z | (0, z) ∈ W'}
    have hW2_open : IsOpen W2 := by
      let f : E (m - 1) → (ℝ × E (m - 1)) := fun z => (0, z)
      have h_cont : Continuous f := by fun_prop
      have h_eq : W2 = f ⁻¹' W' := by rfl
      rw [h_eq]
      exact h_cont.isOpen_preimage W' hW'_open
    have hz0_in_W2 : z0 ∈ W2 := by
      have h1 : e x = H x := by rfl
      have h2 : H x = (0, z0) := by
        exact Prod.ext h_x_zero (by simp [z0])
      have h3 : (0, z0) ∈ W' := by
        rw [←h2, ←h1]
        exact hex_W'
      exact h3
    have hW2_sub_V2 : W2 ⊆ V2 := by
      intro z hz
      have h4 : (0, z) ∈ W' := hz
      have h5 : (0, z) ∈ V := hW'_sub_V h4
      simpa [W2, V2] using h5
    have h_eq_fun : (fun z : E (m - 1) => (0, z)) = Prod.mk (0 : ℝ) := by
      funext z
      rfl
    have h_mapsTo : Set.MapsTo (Prod.mk (0 : ℝ)) (W2 ∩ V2) W' := by
      intro z hz
      have h1 : z ∈ W2 := hz.1
      exact h1
    have h_local_diff : ContDiffOn ℝ ∞ g (W2 ∩ V2) := by
      have h_comp1 : ContDiffOn ℝ ∞ e.symm W' := hW'_diff
      have h_cont2 : ContDiffOn ℝ ∞ (Prod.mk (0 : ℝ)) (W2 ∩ V2) := by
        have h : ContDiff ℝ ∞ (fun z : E (m - 1) => ((0 : ℝ), z)) := by fun_prop
        have h' : (Prod.mk (0 : ℝ)) = (fun z : E (m - 1) => ((0 : ℝ), z)) := by
          funext z
          rfl
        rw [h']
        exact h.contDiffOn
      exact h_comp1.comp h_cont2 h_mapsTo
    have h_inter_nonempty : W2 ∩ V2 = W2 := by
      exact Set.inter_eq_left.mpr hW2_sub_V2
    rw [h_inter_nonempty] at h_local_diff
    rcases local_smooth_extension hW2_open hz0_in_W2 h_local_diff with ⟨Vψ, hVψ_open, hzv, hVV, ψ, hψ, h_eq_on_V⟩
    have h_continuous_e : Continuous e := hH_diff.continuous
    have h_preimage_snd : IsOpen ((fun p : ℝ × E (m - 1) => p.2) ⁻¹' Vψ) :=
      hVψ_open.preimage continuous_snd
    have h_preimage : IsOpen (e ⁻¹' ((fun p : ℝ × E (m - 1) => p.2) ⁻¹' Vψ)) :=
      h_preimage_snd.preimage h_continuous_e
    have h_x_in_preimage : x ∈ e ⁻¹' ((fun p : ℝ × E (m - 1) => p.2) ⁻¹' Vψ) := by
      change (H x).2 ∈ Vψ
      simpa [z0] using hzv
    let N' : Set (E m) := N ∩ e ⁻¹' ((fun p : ℝ × E (m - 1) => p.2) ⁻¹' Vψ)
    have hN'_open : IsOpen N' := hN_open.inter h_preimage
    have hx_in_N' : x ∈ N' := ⟨hxN, h_x_in_preimage⟩
    have h_final_goal : ∀ y ∈ {y ∈ N' | h y = 0}, y ∈ Set.range ψ := by
      intro y hy
      have hyN' : y ∈ N' := hy.1
      have hyN : y ∈ N := hyN'.1
      have hy_h : h y = 0 := hy.2
      have h10 : e y ∈ V := e.mapsTo hyN
      have h11 : (e y).1 = h y := by
        rw [h_eq1 y hyN]
      have h12 : (e y).1 = 0 := by
        rw [h11, hy_h]
      let z : E (m - 1) := (e y).2
      have hz_in_Vψ : z ∈ Vψ := by
        have h : (e y).2 ∈ Vψ := hyN'.2
        exact h
      have h13 : e y = (0, z) := by
        ext <;> simp [z, h12]
      have h14 : y = e.symm (0, z) := by
        calc
          y = e.symm (e y) := (h_left_inv y hyN).symm
          _ = e.symm (0, z) := by rw [h13]
      have h15 : ψ z = e.symm (0, z) := h_eq_on_V z hz_in_Vψ
      have h16 : y = ψ z := by
        rw [h14, h15]
      have h17 : y ∈ Set.range ψ := by
        refine ⟨z, ?_⟩
        exact h16.symm
      exact h17
    exact ⟨N', hN'_open, hx_in_N', ψ, hψ, h_final_goal⟩
  · -- Case h x ≠ 0: trivial, the set is empty
    exact case_hx_ne_zero h hh x h_x_zero

end ForMathlib.Analysis.Calculus.Sard.General
