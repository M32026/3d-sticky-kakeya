module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Tactic.SetNotationForOrder
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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

lemma local_smooth_extension {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V₀ : Set F} (hV₀ : IsOpen V₀) {z₀ : F} (hz₀ : z₀ ∈ V₀)
  {g : F → E} (hg : ContDiffOn ℝ ∞ g V₀) :
  ∃ (V : Set F) (_ : IsOpen V) (_ : z₀ ∈ V) (_ : V ⊆ V₀) (ψ : F → E),
    ContDiff ℝ ∞ ψ ∧ ∀ z ∈ V, ψ z = g z := by
  have h_main : ∃ (R' : ℝ), 0 < R' ∧ Metric.ball z₀ R' ⊆ V₀ := by
    exact Metric.isOpen_iff.mp hV₀ z₀ hz₀
  rcases h_main with ⟨R', hR'pos, hW'_in_V₀⟩
  let R : ℝ := R' / 2
  have hR_pos : 0 < R := half_pos hR'pos
  have hR_lt_R' : R < R' := half_lt_self hR'pos
  let b : ContDiffBump z₀ := ⟨R / 2, R, by linarith, by linarith⟩
  have hb : ContDiff ℝ ∞ (b : F → ℝ) := b.contDiff
  have h_supp : Function.support (b : F → ℝ) = Metric.ball z₀ R := b.support_eq
  have h_b_eq1 : ∀ z ∈ Metric.ball z₀ (R / 2), (b : F → ℝ) z = 1 := by
    intro z hz
    have h9 : z ∈ Metric.closedBall z₀ (R / 2) := by
      exact Metric.ball_subset_closedBall hz
    exact b.one_of_mem_closedBall h9
  let V : Set F := Metric.ball z₀ (R / 2)
  have hV_open : IsOpen V := Metric.isOpen_ball
  have hz0_in_V : z₀ ∈ V := by
    simp [V, hR_pos]
  have hV_sub : V ⊆ Metric.ball z₀ R' := by
    intro x hx
    have h1 : dist x z₀ < R / 2 := hx
    have h2 : dist x z₀ < R' := by linarith
    exact h2
  have hV_in_V0 : V ⊆ V₀ := hV_sub.trans hW'_in_V₀
  let f1 : F → E := fun z => (b : F → ℝ) z • g z
  let f2 : F → E := fun z => (1 - (b : F → ℝ) z) • (g z₀)
  let ψ : F → E := f1 + f2
  have h_psi_eq_on_V : ∀ z ∈ V, ψ z = g z := by
    intro z hz
    have h1 : (b : F → ℝ) z = 1 := h_b_eq1 z hz
    have h_goal : ψ z = g z := by
      have h9 : ψ z = f1 z + f2 z := by rfl
      rw [h9]
      dsimp only [f1, f2]
      rw [h1]
      simp
    exact h_goal
  have h_psi_smooth : ContDiff ℝ ∞ ψ := by
    have h1 : ∀ (z : F), ContDiffAt ℝ ∞ ψ z := by
      intro z
      by_cases h : z ∈ Metric.ball z₀ R'
      · have h2 : z ∈ V₀ := hW'_in_V₀ h
        have h3 : ContDiffAt ℝ ∞ g z := hg.contDiffAt (hV₀.mem_nhds h2)
        have h4 : ContDiffAt ℝ ∞ f1 z := (hb.contDiffAt).smul h3
        have h5 : ContDiffAt ℝ ∞ f2 z := by
          have h51 : ContDiffAt ℝ ∞ (fun w : F => 1 - (b : F → ℝ) w) z := by
            exact contDiffAt_const.sub hb.contDiffAt
          exact h51.smul contDiffAt_const
        exact h4.add h5
      · have h4 : dist z z₀ ≥ R' := by simpa [Metric.mem_ball] using h
        let ε : ℝ := R' - R
        have hε_pos : 0 < ε := by linarith
        have h5 : ∀ w ∈ Metric.ball z ε, (b : F → ℝ) w = 0 := by
          intro w hw
          have h6 : dist w z < ε := hw
          have h7 : dist z z₀ ≤ dist z w + dist w z₀ := dist_triangle z w z₀
          have h8 : dist w z₀ > R := by
            have h9 : dist z w = dist w z := by exact dist_comm z w
            linarith
          have h10 : w ∉ Metric.ball z₀ R := by
            simpa [Metric.mem_ball] using not_lt.mpr (by linarith)
          have h11 : w ∉ Function.support (b : F → ℝ) := by
            rw [h_supp]
            exact h10
          simpa [Function.mem_support] using h11
        have h6 : ∀ᶠ (w : F) in nhds z, ψ w = g z₀ := by
          filter_upwards [Metric.ball_mem_nhds z hε_pos] with w hw
          have h7 : (b : F → ℝ) w = 0 := h5 w hw
          have h_goal : ψ w = g z₀ := by
            have h9 : ψ w = f1 w + f2 w := by rfl
            rw [h9]
            dsimp only [f1, f2]
            rw [h7]
            simp
          exact h_goal
        have h_const : ContDiffAt ℝ ∞ (fun (_ : F) => g z₀) z := by exact contDiffAt_const
        exact h_const.congr_of_eventuallyEq h6
    exact contDiff_iff_contDiffAt.mpr h1
  exact ⟨V, hV_open, hz0_in_V, hV_in_V0, ψ, h_psi_smooth, h_psi_eq_on_V⟩

lemma round1_finrank_E (n : ℕ) : Module.finrank ℝ (E n) = n := by
  exact finrank_euclideanSpace_fin
lemma round1_h1 {m n r : ℕ} (f : E m → E n) (p : E m) (hp_rank : fderivRank f p = r) : r ≤ m := by
  let f' : (E m) →ₗ[ℝ] (E n) := (fderiv ℝ f p).toLinearMap
  have h_def : fderivRank f p = Module.finrank ℝ (LinearMap.range f') := by rfl
  have h21 : Module.finrank ℝ (LinearMap.range f') ≤ Module.finrank ℝ (E m) := LinearMap.finrank_range_le f'
  have hm : Module.finrank ℝ (E m) = m := round1_finrank_E m
  have : fderivRank f p ≤ m := by
    calc
      fderivRank f p = Module.finrank ℝ (LinearMap.range f') := h_def
      _ ≤ Module.finrank ℝ (E m) := h21
      _ = m := hm
  rw [hp_rank] at this
  exact this
lemma round1_h2 {m n r : ℕ} (f : E m → E n) (p : E m) (hp_rank : fderivRank f p = r) : r ≤ n := by
  let f' : (E m) →ₗ[ℝ] (E n) := (fderiv ℝ f p).toLinearMap
  have h_def : fderivRank f p = Module.finrank ℝ (LinearMap.range f') := by rfl
  let S : Submodule ℝ (E n) := LinearMap.range f'
  have h1 : Module.finrank ℝ S ≤ Module.finrank ℝ (E n) := Submodule.finrank_le S
  have h2 : Module.finrank ℝ (E n) = n := round1_finrank_E n
  have h4 : fderivRank f p ≤ n := by
    calc
      fderivRank f p = Module.finrank ℝ S := h_def
      _ ≤ Module.finrank ℝ (E n) := h1
      _ = n := h2
  have h5 : r ≤ n := by
    rw [hp_rank] at h4
    exact h4
  exact h5

lemma round1_lemma_A {m n r : ℕ} (f' : (E m) →ₗ[ℝ] (E n))
    (hrank : Module.finrank ℝ (LinearMap.range f') = r) :
    ∃ (π : (E n) →ₗ[ℝ] (E r)), Function.Surjective (π.comp f') := by
  let R : Submodule ℝ (E n) := LinearMap.range f'
  have hR_finrank : Module.finrank ℝ R = r := hrank
  have hE_finrank : Module.finrank ℝ (E r) = r := round1_finrank_E r
  have h_nonempty : Nonempty (R ≃ₗ[ℝ] (E r)) :=
    FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by rw [hR_finrank, hE_finrank])
  rcases h_nonempty with ⟨e_R₀⟩
  let e_R : R ≃L[ℝ] (E r) := e_R₀.toContinuousLinearEquiv
  have h_main : ∃ (q : Submodule ℝ (E n)), IsCompl R q := Submodule.exists_isCompl R
  rcases h_main with ⟨q, hq⟩
  let p : (E n) →ₗ[ℝ] R := Submodule.projectionOnto R q hq
  let π : (E n) →ₗ[ℝ] (E r) := e_R.comp p
  use π
  intro z
  have h1 : ∃ (w : R), e_R w = z := e_R.surjective z
  rcases h1 with ⟨w, hw⟩
  have h3 : ∃ (v : E m), f' v = (w : E n) := w.prop
  rcases h3 with ⟨v, hv⟩
  have h4 : p (f' v) = w := by
    rw [hv]
    exact Submodule.projectionOnto_apply_left hq w
  have h5 : π (f' v) = z := by
    dsimp only [π]
    have h6 : (e_R.comp p) (f' v) = e_R (p (f' v)) := by rfl
    rw [h6, h4]
    exact hw
  exact ⟨v, h5⟩

lemma helper_linear_equiv_split {V W V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
  (p₁ : V →ₗ[ℝ] W) (hp₁_surj : Function.Surjective p₁)
  (h_finrank : Module.finrank ℝ V' = Module.finrank ℝ V - Module.finrank ℝ W) :
  ∃ (p₂ : V →ₗ[ℝ] V'),
    Function.Bijective (fun x : V => (p₁ x, p₂ x)) := by
  let K := LinearMap.ker p₁
  have h_range_eq_top : LinearMap.range p₁ = ⊤ := LinearMap.range_eq_top.mpr hp₁_surj
  have h_rank_range : Module.finrank ℝ (LinearMap.range p₁) = Module.finrank ℝ W := by
    rw [h_range_eq_top]
    simp
  have h1 : Module.finrank ℝ W + Module.finrank ℝ K = Module.finrank ℝ V := by
    have h := LinearMap.finrank_range_add_finrank_ker p₁
    rw [h_rank_range] at h
    exact h
  have h_finrank_K : Module.finrank ℝ K = Module.finrank ℝ V - Module.finrank ℝ W := by
    omega
  have h2 : Module.finrank ℝ K = Module.finrank ℝ V' := by
    rw [h_finrank_K, h_finrank]
  have h3 : Nonempty (K ≃ₗ[ℝ] V') := by
    exact FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq.mpr h2
  let e_K : K ≃ₗ[ℝ] V' := Classical.choice h3
  have hK_closed : K.ClosedComplemented := Submodule.ClosedComplemented.of_finiteDimensional K
  have h4 : ∃ (q : Submodule ℝ V), IsCompl K q := hK_closed.exists_isClosed_isCompl.imp (fun q hq => hq.2)
  rcases h4 with ⟨q, hq_isCompl⟩
  let proj : V →ₗ[ℝ] K := Submodule.projectionOnto K q hq_isCompl
  have hproj : ∀ (x : K), proj (x : V) = x := by
    intro x
    exact Submodule.projectionOnto_apply_left hq_isCompl x
  let p₂ : V →ₗ[ℝ] V' := e_K.comp proj
  let T : V →ₗ[ℝ] (W × V') := {
    toFun := fun x : V => (p₁ x, p₂ x),
    map_add' := by
      intro x y
      simp [p₂]
    map_smul' := by
      intro c x
      simp [p₂] }
  have h_inj : Function.Injective T := by
    intro x y hxy
    have h_eq : T x = T y := hxy
    have h5 : p₁ x = p₁ y := by
      exact congrArg Prod.fst h_eq
    have h6 : p₂ x = p₂ y := by
      exact congrArg Prod.snd h_eq
    let z := x - y
    have hz1 : p₁ z = 0 := by
      simpa [z, map_sub] using sub_eq_zero.mpr h5
    have hzK : z ∈ K := hz1
    let z_K : K := ⟨z, hzK⟩
    have h_proj_z : proj z = z_K := by
      exact hproj z_K
    have h7 : p₂ z = 0 := by
      simpa [z, map_sub] using sub_eq_zero.mpr h6
    have h8 : e_K z_K = 0 := by
      have h9 : p₂ z = e_K (proj z) := by rfl
      rw [h9, h_proj_z] at h7
      exact h7
    have h10 : e_K z_K = e_K 0 := by
      simpa using h8
    have h11 : z_K = 0 := e_K.injective h10
    have h12 : z = 0 := Subtype.ext_iff.mp h11
    exact sub_eq_zero.mp h12
  have h_finrank_eq : Module.finrank ℝ V = Module.finrank ℝ (W × V') := by
    have h4 : Module.finrank ℝ (W × V') = Module.finrank ℝ W + Module.finrank ℝ V' := by
      exact finrank_prod
    rw [h4, h_finrank]
    omega
  have h_surj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank_eq).mp h_inj
  have h_main : Function.Bijective T := ⟨h_inj, h_surj⟩
  exact ⟨p₂, h_main⟩

lemma helper_surjective_of_comp {A B C : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
  (f' : A →ₗ[ℝ] B) (π : B →ₗ[ℝ] C) (h : Function.Surjective (π.comp f')) :
  Function.Surjective π := by
  intro z
  rcases h z with ⟨x, hx⟩
  refine ⟨f' x, ?_⟩
  exact hx

lemma helper_fderiv_H {m n r : ℕ}
  (f : E m → E n) (hf : ContDiff ℝ ∞ f) (p : E m)
  (π : (E n) →ₗ[ℝ] (E r))
  (p₂ : (E m) →ₗ[ℝ] (E (m - r))) :
  let l1 : (E m) →L[ℝ] (E r) := (π.comp (fderiv ℝ f p).toLinearMap).toContinuousLinearMap
  let l2 : (E m) →L[ℝ] (E (m - r)) := p₂.toContinuousLinearMap
  let L : (E m) →L[ℝ] (E r × E (m - r)) := l1.prod l2
  HasFDerivAt (fun x : E m => (π (f x), p₂ x)) L p := by
  let l1 : (E m) →L[ℝ] (E r) := (π.comp (fderiv ℝ f p).toLinearMap).toContinuousLinearMap
  let l2 : (E m) →L[ℝ] (E (m - r)) := p₂.toContinuousLinearMap
  let L : (E m) →L[ℝ] (E r × E (m - r)) := l1.prod l2
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have h_diff : Differentiable ℝ f := hf.differentiable hne
  have h_diff_at : DifferentiableAt ℝ f p := h_diff p
  have h1 : HasFDerivAt (fun x : E m => π (f x)) l1 p := by
    have hfa : HasFDerivAt f (fderiv ℝ f p) p := h_diff_at.hasFDerivAt
    exact π.toContinuousLinearMap.hasFDerivAt.comp p hfa
  have h2 : HasFDerivAt (fun x : E m => p₂ x) l2 p := by
    exact p₂.toContinuousLinearMap.hasFDerivAt
  exact HasFDerivAt.prodMk h1 h2

lemma helper_final_linear_eq {m r : ℕ}
  (L : (E m) →L[ℝ] (E r × E (m - r)))
  (hL_bij' : Function.Bijective (L : (E m) → (E r × E (m - r)))) :
  ∃ (eL : (E m) ≃L[ℝ] (E r × E (m - r))),
    (eL : (E m) →L[ℝ] (E r × E (m - r))) = L := by
  let eL' : (E m) ≃ₗ[ℝ] (E r × E (m - r)) := LinearEquiv.ofBijective L hL_bij'
  let eL : (E m) ≃L[ℝ] (E r × E (m - r)) := eL'.toContinuousLinearEquiv
  have h : ∀ (x : E m), (eL : (E m) → (E r × E (m - r))) x = L x := by
    intro x
    simp [eL, eL', LinearEquiv.ofBijective_apply]
  have h_goal : (eL : (E m) →L[ℝ] (E r × E (m - r))) = L := by
    exact ContinuousLinearMap.coe_inj.mp rfl
  exact ⟨eL, h_goal⟩

lemma helper_main_equivalence {n r : ℕ} (π : (E n) →ₗ[ℝ] (E r)) (hπ : Function.Surjective π) :
    ∃ (e : (E r × E (n - r)) ≃L[ℝ] E n), ∀ (z : E n), (e.symm z).1 = π z := by
  let π' : (E n) →L[ℝ] (E r) := π.toContinuousLinearMap
  have hπ' : Function.Surjective π' := hπ
  have h1 : π'.HasRightInverse := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hπ'
  rcases h1 with ⟨s, hs⟩
  have hs_id' : ∀ (x : E r), π (s x) = x := by
    intro x
    have h : π' (s x) = x := hs x
    exact h
  let K : Submodule ℝ (E n) := LinearMap.ker π
  have h_range_eq_top : LinearMap.range π = ⊤ := by
    exact LinearMap.range_eq_top.mpr hπ
  have h_rank_nullity : Module.finrank ℝ (LinearMap.range π) + Module.finrank ℝ K = Module.finrank ℝ (E n) :=
    LinearMap.finrank_range_add_finrank_ker π
  have h_finrank_K1 : Module.finrank ℝ (LinearMap.range π) = Module.finrank ℝ (E r) := by
    rw [h_range_eq_top]
    simp
  have h_eq : Module.finrank ℝ (E r) + Module.finrank ℝ K = Module.finrank ℝ (E n) := by
    rw [h_finrank_K1] at h_rank_nullity
    exact h_rank_nullity
  have h_eq2 : r + Module.finrank ℝ K = n := by
    simp at h_eq ⊢
    exact h_eq
  have h_finrank_K : Module.finrank ℝ K = n - r := by omega
  have h_finrank_E2 : Module.finrank ℝ (E (n - r)) = n - r := round1_finrank_E (n - r)
  have h_equiv_K : Nonempty (K ≃L[ℝ] (E (n - r))) :=
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by
      rw [h_finrank_K, h_finrank_E2])
  let eK : K ≃L[ℝ] (E (n - r)) := Classical.choice h_equiv_K
  let Φ : (E r × E (n - r)) → E n := fun p => s p.1 + (eK.symm p.2 : E n)
  have h_ker_val : ∀ (z : E n), z - s (π z) ∈ K := by
    intro z
    have h4 : π (z - s (π z)) = 0 := by
      have h5 : π (s (π z)) = π z := hs_id' (π z)
      simp [h5]
    exact h4
  let Ψ : E n → (E r × E (n - r)) := fun z =>
    (π z, eK ⟨z - s (π z), h_ker_val z⟩)
  have h1 : ∀ z, Φ (Ψ z) = z := by
    intro z
    simp [Φ, Ψ]
  have h2 : ∀ p, Ψ (Φ p) = p := by
    intro ⟨a, b⟩
    have h5 : π (s a + (eK.symm b : E n)) = a := by
      have h6 : π (eK.symm b : E n) = 0 := (eK.symm b).property
      have h7 : π (s a) = a := hs_id' a
      simp [h6, h7]
    simp [Φ, Ψ, h5]
  let e_linear : (E r × E (n - r)) →ₗ[ℝ] E n :=
    { toFun := Φ
      map_add' := by
        intro x y
        simp [Φ]
        abel
      map_smul' := by
        intro c x
        simp [Φ] }
  let e_linear_equiv : (E r × E (n - r)) ≃ₗ[ℝ] E n :=
    { toFun := Φ
      invFun := Ψ
      left_inv := h2
      right_inv := h1
      map_add' := e_linear.map_add'
      map_smul' := e_linear.map_smul' }
  let e_equiv : (E r × E (n - r)) ≃L[ℝ] E n := e_linear_equiv.toContinuousLinearEquiv
  have h3 : ∀ (z : E n), (e_equiv.symm z).1 = π z := by
    intro z
    have h4 : e_equiv.symm z = Ψ z := by rfl
    rw [h4]
  exact ⟨e_equiv, h3⟩

lemma round1_last_helper {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {f : E → F} (h : ContDiffOn ℝ ω f s) : ContDiffOn ℝ ∞ f s := by
  exact h.of_le le_top

/-- Lemma 6 (Local straightening at positive rank).
    If f : E m → E n is C^∞ and rank(Df_p) = r > 0 at a point p, then there
    exist open neighborhoods U of p, V of f(p), and a local diffeomorphism
    H : U → E r × E (m - r) (change of coordinates in the source)
    such that for all (a, b) in the image of H:
      f (H⁻¹ (a, b)) = (a, G(a, b))
    where G : E r × E (m - r) → E (n - r) is C^∞.

    This is proved by applying the inverse function theorem to
      H(x) := (π_R (f(x)), π_B (x))
    where R is the range of Df_p and B is a complementary subspace. -/
theorem local_straightening_positive_rank {m n r : ℕ}
    (f : E m → E n) (hf : ContDiff ℝ ∞ f) (p : E m)
    (hp_rank : fderivRank f p = r) :
    ∃ (U : Set (E m)) (_ : IsOpen U) (_ : p ∈ U)
      (V : Set (E r × E (m - r))) (_ : IsOpen V)
      (H : E m → E r × E (m - r))
      (_ : ContDiff ℝ ∞ H)
      (_ : ∀ x ∈ U, H x ∈ V ∧ ∃ Hinv : E r × E (m - r) → E m,
        (∀ y ∈ V, H (Hinv y) = y) ∧ (∀ y ∈ V, Hinv y ∈ U) ∧
        (∀ x ∈ U, Hinv (H x) = x) ∧ ContDiff ℝ ∞ Hinv)
      (G : (E r × E (m - r)) → E (n - r))
      (_ : ContDiff ℝ ∞ G)
      (e : (E r × E (n - r)) ≃L[ℝ] E n),
      ∀ x ∈ U, e ( (H x).1, G (H x) ) = f x := by
  let f' : (E m) →ₗ[ℝ] (E n) := (fderiv ℝ f p).toLinearMap
  rcases round1_lemma_A f' hp_rank with ⟨π, hπ_surj_comp⟩
  have hπ_surj : Function.Surjective π := helper_surjective_of_comp f' π hπ_surj_comp
  let p₁ : (E m) →ₗ[ℝ] (E r) := π.comp f'
  have hp₁_surj : Function.Surjective p₁ := hπ_surj_comp
  have h_finrank_eq : Module.finrank ℝ (E (m - r)) = Module.finrank ℝ (E m) - Module.finrank ℝ (E r) := by
    simp
  rcases helper_linear_equiv_split p₁ hp₁_surj h_finrank_eq with ⟨p₂, hp₂_bij⟩
  let H : E m → E r × E (m - r) := fun x => (π (f x), p₂ x)
  have h1 : ContDiff ℝ ∞ (fun x : E m => π (f x)) := by
    have hπ_smooth : ContDiff ℝ ∞ π := π.toContinuousLinearMap.contDiff
    exact hπ_smooth.comp hf
  have h2 : ContDiff ℝ ∞ (fun x : E m => p₂ x) := p₂.toContinuousLinearMap.contDiff
  have hH : ContDiff ℝ ∞ H := ContDiff.prodMk h1 h2
  let h_ne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have h_diff : ∀ (x : E m), DifferentiableAt ℝ H x := fun x => (hH.differentiable h_ne).differentiableAt
  let l1 : (E m) →L[ℝ] (E r) := p₁.toContinuousLinearMap
  let l2 : (E m) →L[ℝ] (E (m - r)) := p₂.toContinuousLinearMap
  let L : (E m) →L[ℝ] (E r × E (m - r)) := l1.prod l2
  have h_H_hasFDeriv : HasFDerivAt H L p := helper_fderiv_H f hf p π p₂
  have hL_bij : Function.Bijective (L : E m → E r × E (m - r)) := hp₂_bij
  rcases helper_final_linear_eq L hL_bij with ⟨eL, h_eL_eq⟩
  have h_H_hasFDeriv_eL : HasFDerivAt H (eL : (E m) →L[ℝ] (E r × E (m - r))) p := by
    have h : (eL : (E m) →L[ℝ] (E r × E (m - r))) = L := h_eL_eq
    rw [h]
    exact h_H_hasFDeriv
  have h_fderiv_eq : fderiv ℝ H p = (eL : (E m) →L[ℝ] (E r × E (m - r))) := by
    exact h_H_hasFDeriv_eL.fderiv
  have hH_at_p : ContDiffAt ℝ ∞ H p := ContDiff.contDiffAt hH
  have h_strict_raw : HasStrictFDerivAt H (fderiv ℝ H p) p := hH_at_p.hasStrictFDerivAt h_ne
  let h_strict : HasStrictFDerivAt H (eL : (E m) →L[ℝ] (E r × E (m - r))) p := by
    rw [h_fderiv_eq] at h_strict_raw
    exact h_strict_raw
  let e_oph : OpenPartialHomeomorph (E m) (E r × E (m - r)) :=
    hH_at_p.toOpenPartialHomeomorph (𝕂 := ℝ) (hf' := h_H_hasFDeriv_eL) (hn := h_ne)
  let S : Set (E m) := e_oph.source
  let T : Set (E r × E (m - r)) := e_oph.target
  have hS_open : IsOpen S := e_oph.open_source
  have hT_open : IsOpen T := e_oph.open_target
  have hpS : p ∈ S := h_strict.mem_toOpenPartialHomeomorph_source
  let z₀ : E r × E (m - r) := H p
  have hz₀T : z₀ ∈ T := e_oph.mapsTo hpS
  let Z : Set ((E m) →L[ℝ] (E r × E (m - r))) := Set.range (fun (e : (E m) ≃L[ℝ] (E r × E (m - r))) => (e : (E m) →L[ℝ] (E r × E (m - r))))
  have hZ_open : IsOpen Z := ContinuousLinearEquiv.isOpen
  let fderiv_H : (E m) → (E m) →L[ℝ] (E r × E (m - r)) := fun x => fderiv ℝ H x
  have h_fderiv_H_cont : Continuous fderiv_H := by
    exact hH.continuous_fderiv h_ne
  let S' : Set (E m) := fderiv_H ⁻¹' Z
  have hS'_open : IsOpen S' := hZ_open.preimage h_fderiv_H_cont
  have hp_S' : p ∈ S' := by
    dsimp only [S', fderiv_H, Z]
    exact ⟨eL, h_fderiv_eq.symm⟩
  let Ugood : Set (E m) := S ∩ S'
  have hUgood_open : IsOpen Ugood := hS_open.inter hS'_open
  have hp_Ugood : p ∈ Ugood := ⟨hpS, hp_S'⟩
  have h1_nhds : Ugood ∈ nhds p := hUgood_open.mem_nhds hp_Ugood
  have h3 : Filter.map e_oph (nhds p) = nhds z₀ := e_oph.map_nhds_eq hpS
  have h4 : H '' Ugood ∈ Filter.map e_oph (nhds p) := Filter.image_mem_map h1_nhds
  have h2_nhds : H '' Ugood ∈ nhds z₀ := by
    have h5 : Filter.map e_oph (nhds p) = nhds z₀ := h3
    rw [h5] at h4
    exact h4
  rcases mem_nhds_iff.mp h2_nhds with ⟨Vgood, hVgood_sub, hVgood_open, hz₀_Vgood⟩
  have hVgood_sub_image : Vgood ⊆ H '' Ugood := hVgood_sub
  have hVgood_sub_T : Vgood ⊆ T := by
    intro z hz
    have h4 : z ∈ H '' Ugood := hVgood_sub_image hz
    rcases h4 with ⟨x, hx, rfl⟩
    exact e_oph.mapsTo hx.1
  have h_main_contDiffAt : ∀ (z : E r × E (m - r)), z ∈ Vgood → ContDiffAt ℝ ∞ e_oph.symm z := by
    intro z hz
    have hz_in_image : z ∈ H '' Ugood := hVgood_sub_image hz
    rcases hz_in_image with ⟨x, hx, rfl⟩
    have hx1 : x ∈ S := hx.1
    have hx2 : fderiv ℝ H x ∈ Z := hx.2
    rcases hx2 with ⟨e_x, he_x_eq⟩
    have h9 : (e_x : (E m) →L[ℝ] (E r × E (m - r))) = fderiv ℝ H x := he_x_eq
    have h10 : HasFDerivAt H (fderiv ℝ H x) x := (h_diff x).hasFDerivAt
    have h_hasFDeriv : HasFDerivAt H (e_x : (E m) →L[ℝ] (E r × E (m - r))) x := by
      rw [h9]
      exact h10
    have h11 : e_oph.symm (H x) = x := e_oph.left_inv hx1
    have h_hasFDeriv' : HasFDerivAt (e_oph) (e_x : (E m) →L[ℝ] (E r × E (m - r))) (e_oph.symm (H x)) := by
      rw [h11]
      change HasFDerivAt H (e_x : (E m) →L[ℝ] (E r × E (m - r))) x
      exact h_hasFDeriv
    have hH_at_x : ContDiffAt ℝ ∞ H x := ContDiff.contDiffAt hH
    have h_contDiffAt' : ContDiffAt ℝ ∞ (e_oph) (e_oph.symm (H x)) := by
      rw [h11]
      change ContDiffAt ℝ ∞ H x
      exact hH_at_x
    exact e_oph.contDiffAt_symm (e_oph.mapsTo hx1) h_hasFDeriv' h_contDiffAt'
  have h_contDiffOn_Vgood : ContDiffOn ℝ ∞ e_oph.symm Vgood := by
    rw [hVgood_open.contDiffOn_iff]
    exact h_main_contDiffAt
  rcases helper_main_equivalence π hπ_surj with ⟨e, he_prop⟩
  let g : (E r × E (m - r)) → E (n - r) := fun z => (e.symm (f (e_oph.symm z))).2
  have h2' : ContDiff ℝ ∞ f := hf
  have h3' : ContDiff ℝ ∞ e.symm := e.symm.contDiff
  have h4' : ContDiffOn ℝ ∞ (fun z => f (e_oph.symm z)) Vgood := h2'.comp_contDiffOn h_contDiffOn_Vgood
  have h5' : ContDiffOn ℝ ∞ (fun z => e.symm (f (e_oph.symm z))) Vgood := h3'.comp_contDiffOn h4'
  have hgW : ContDiffOn ℝ ∞ g Vgood := by
    change ContDiffOn ℝ ∞ (ContinuousLinearMap.snd ℝ (E r) (E (n - r)) ∘
      (fun z => e.symm (f (e_oph.symm z)))) Vgood
    exact ContDiffOn.continuousLinearMap_comp (ContinuousLinearMap.snd ℝ (E r) (E (n - r))) h5'
  rcases local_smooth_extension hVgood_open hz₀_Vgood h_contDiffOn_Vgood with ⟨Vinv, hVinv_open, hz₀Vinv, hVinv_sub_Vgood, Φ, hΦ, hΦ_eq⟩
  rcases local_smooth_extension hVgood_open hz₀_Vgood hgW with ⟨VG, hVG_open, hz₀VG, hVG_sub_Vgood, G, hG, hG_eq⟩
  let V_final : Set (E r × E (m - r)) := Vinv ∩ VG
  have hV_final_open : IsOpen V_final := hVinv_open.inter hVG_open
  have hz₀_V_final : z₀ ∈ V_final := ⟨hz₀Vinv, hz₀VG⟩
  have hV_sub_Vgood : V_final ⊆ Vgood := fun z hz => hVinv_sub_Vgood hz.1
  have hV_sub_T : V_final ⊆ T := hV_sub_Vgood.trans hVgood_sub_T
  have hV_sub_Vinv : V_final ⊆ Vinv := fun z hz => hz.1
  have hV_sub_VG : V_final ⊆ VG := fun z hz => hz.2
  let U : Set (E m) := S ∩ H ⁻¹' V_final
  have hU_open : IsOpen U := hS_open.inter (hV_final_open.preimage hH.continuous)
  have hpU : p ∈ U := by
    constructor
    · exact hpS
    · simpa [U, z₀] using hz₀_V_final
  have h_main1 : ∀ x ∈ U, H x ∈ V_final := fun x hx => hx.2
  refine' ⟨U, hU_open, hpU, V_final, hV_final_open, H, hH, _ , G, hG, e, _⟩
  · intro x hx
    refine' ⟨h_main1 x hx, ⟨Φ, _ , _ , _ , hΦ⟩⟩
    · intro y hy
      have hyVinv : y ∈ Vinv := hV_sub_Vinv hy
      have hyT : y ∈ T := hV_sub_T hy
      have h7 : Φ y = e_oph.symm y := hΦ_eq y hyVinv
      rw [h7]
      exact e_oph.right_inv hyT
    · intro y hy
      have hyVinv : y ∈ Vinv := hV_sub_Vinv hy
      have hyT : y ∈ T := hV_sub_T hy
      have h7 : Φ y = e_oph.symm y := hΦ_eq y hyVinv
      have h8 : e_oph.symm y ∈ e_oph.source := e_oph.map_target hyT
      have h9 : H (e_oph.symm y) = y := e_oph.right_inv hyT
      have h10 : H (e_oph.symm y) ∈ V_final := by
        rw [h9]
        exact hy
      have h11 : e_oph.symm y ∈ U := ⟨h8, h10⟩
      rw [h7]
      exact h11
    · intro x' hx'
      have h8 : x' ∈ S := hx'.1
      have h9 : H x' ∈ V_final := h_main1 x' hx'
      have h10 : Φ (H x') = e_oph.symm (H x') := hΦ_eq (H x') (hV_sub_Vinv h9)
      rw [h10]
      exact e_oph.left_inv h8
  · intro x hx
    have h_x_in_S : x ∈ S := hx.1
    have h_Hx_in_V : H x ∈ V_final := h_main1 x hx
    have h11 : G (H x) = g (H x) := hG_eq (H x) (hV_sub_VG h_Hx_in_V)
    have h12 : G (H x) = (e.symm (f (e_oph.symm (H x)))).2 := by
      rw [h11]
    have h13 : e_oph.symm (H x) = x := e_oph.left_inv h_x_in_S
    have h14 : G (H x) = (e.symm (f x)).2 := by
      rw [h12, h13]
    have h15 : (H x).1 = π (f x) := by rfl
    have h16 : (e.symm (f x)).1 = π (f x) := he_prop (f x)
    have h17 : ((H x).1, G (H x)) = e.symm (f x) := by
      ext <;> simp [h15, h14, h16]
    rw [h17]
    exact e.apply_symm_apply (f x)

end ForMathlib.Analysis.Calculus.Sard.General
