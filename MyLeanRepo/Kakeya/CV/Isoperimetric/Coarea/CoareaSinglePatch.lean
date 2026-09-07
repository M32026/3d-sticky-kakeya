import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaSliceLocal
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.ImplicitDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphAreaSmooth
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.BrunnMinkowski.PrekopaLeindler
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Tactic

/-!
# Single-Patch Coarea Formula

Given a C¹ function `f : E(m+1) → ℝ` and an `OpenPartialHomeomorph φ`
with `φ(y) = projHCL(y) + f(y)·eLast`, for any compact `A ⊆ φ.source`
where `∂_last f ≠ 0`, we prove:

  `∫⁻ t, μHE[m](A ∩ {f = t}) = ∫⁻ y in A, ‖∇f(y)‖`

## Proof

1. `coarea_graph_slice_local` gives, for each `t`:
   `μHE[m](A ∩ {f = t}) = ∫⁻ z in B_t, J(z,t)`

2. Define `h : E(m+1) → ENNReal` by `h(p) = J(p) · 1_{φ '' A}(p)`.

3. Fubini (via measure-preserving `unsplitEquiv`):
   `∫⁻ p, h(p) = ∫⁻ t, ∫⁻ z, h(unsplit(z,t)) = ∫⁻ t, μHE[m](A ∩ {f = t})`

4. Change of variables `φ : A → φ '' A`:
   `∫⁻ p, h(p) = ∫⁻ y in A, |det Dφ(y)| · h(φ(y)) = ∫⁻ y in A, ‖∇f(y)‖`
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {m : ℕ} [Nonempty (Fin m)]

-- ============================================================================
-- Smooth indicator and C¹ extension lemmas
-- ============================================================================

/-- Helper: finite product of ContDiff functions is ContDiff. -/
lemma contDiff_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → E m → ℝ)
    (h : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f i)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : E m => ∏ i ∈ s, f i z) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using contDiff_const
  | @insert i s hi ih =>
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (f i) := h i (Finset.mem_insert_self i s)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : E m => ∏ j ∈ s, f j z) :=
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have h3 : (fun z : E m => ∏ j ∈ insert i s, f j z) =
        (fun z : E m => f i z * ∏ j ∈ s, f j z) := by
      funext z
      rw [Finset.prod_insert hi] <;> rfl
    rw [h3]
    exact h1.mul h2

/-- Given compact `K ⊆ V` open, there exists a `C^∞` function `ψ`
that is `1` on an open neighborhood `W` of `K` and has support contained in `V`.
Moreover, `closure (support ψ) ⊆ V`. -/
lemma exists_smooth_indicator
    {K V : Set (E m)} (hK : IsCompact K) (hV_open : IsOpen V) (hK_sub : K ⊆ V) :
    ∃ (ψ : E m → ℝ) (W : Set (E m)),
      IsOpen W ∧ K ⊆ W ∧ closure (Function.support ψ) ⊆ V ∧
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ EqOn ψ 1 W := by
  classical
  have h1 : ∀ (x : E m), x ∈ K → ∃ (r : ℝ), 0 < r ∧ ball x r ⊆ V := by
    intro x hx
    have h2 : x ∈ V := hK_sub hx
    rcases Metric.isOpen_iff.mp hV_open x h2 with ⟨r, hr_pos, hr_sub⟩
    exact ⟨r, hr_pos, hr_sub⟩
  choose r hr_pos hr_sub using h1

  let r' : E m → ℝ := fun x => if h : x ∈ K then (r x h) / 3 else 1
  have hr'_pos : ∀ x, 0 < r' x := by
    intro x; by_cases h : x ∈ K <;> simp [r', h] <;> linarith [hr_pos x h]
  have hr'_sub : ∀ x ∈ K, closedBall x (2 * r' x) ⊆ V := by
    intro x hx
    have h2 : r' x = (r x hx) / 3 := by simp [r', hx]
    rw [h2]
    have h_pos : 0 < r x hx := hr_pos x hx
    have h3 : closedBall x (2 * ((r x hx) / 3)) ⊆ ball x (r x hx) := by
      intro y hy
      have h4 : dist y x ≤ 2 * ((r x hx) / 3) := by simpa [closedBall] using hy
      have h5 : dist y x < r x hx := by
        calc dist y x ≤ 2 * ((r x hx) / 3) := h4
          _ = (2 / 3 : ℝ) * (r x hx) := by ring
          _ < r x hx := by nlinarith
      simpa [ball] using h5
    exact h3.trans (hr_sub x hx)

  let I : Type _ := {x : E m // x ∈ K}
  let cover : I → Set (E m) := fun i => ball i.val (r' i.val)
  have hcover : K ⊆ ⋃ (i : I), cover i := by
    intro y hy
    let i : I := ⟨y, hy⟩
    have h_i_val : (i : E m) = y := by exact Subtype.coe_mk y hy
    have h4 : y ∈ cover i := by
      have h5 : dist y i.val = 0 := by rw [h_i_val] <;> simp
      have h6 : dist y i.val < r' i.val := by rw [h5] <;> exact hr'_pos i.val
      simpa [cover, ball] using h6
    exact Set.mem_iUnion.mpr ⟨i, h4⟩
  rcases hK.elim_finite_subcover cover (fun _ => isOpen_ball) hcover with ⟨s, hs⟩

  let bump : I → (E m → ℝ) := fun i =>
    let b : ContDiffBump i.val := default
    fun y => b (i.val + (1 / r' i.val) • (y - i.val))

  have hbump_diff : ∀ (i : I), i ∈ s → ContDiff ℝ (⊤ : ℕ∞) (bump i) := by
    intro i _
    let x : E m := i.val
    let b : ContDiffBump x := default
    have h_inner : ContDiff ℝ (⊤ : ℕ∞) (fun y : E m => x + (1 / r' x) • (y - x)) := by fun_prop
    have h_b : ContDiff ℝ (⊤ : ℕ∞) (b : E m → ℝ) := b.contDiff (n := ⊤)
    exact h_b.comp h_inner

  have hbump_one : ∀ (i : I), i ∈ s → ∀ (y : E m), y ∈ ball i.val (r' i.val) → bump i y = 1 := by
    intro i _ y hy
    let x : E m := i.val
    let b : ContDiffBump x := default
    have h_rIn : b.rIn = 1 := by rfl
    have h6 : dist y x < r' x := by simpa [ball] using hy
    have h7 : ‖(1 / r' x) • (y - x)‖ ≤ 1 := by
      have h_norm : ‖(1 / r' x) • (y - x)‖ = |(1 / r' x)| * ‖y - x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      rw [h_norm]
      have h9 : 0 < 1 / r' x := by exact div_pos zero_lt_one (hr'_pos x)
      rw [abs_of_pos h9]
      have h10 : ‖y - x‖ < r' x := by simpa [dist_eq_norm] using h6
      have h11 : (1 / r' x) * ‖y - x‖ < 1 := by
        have h_eq : (1 / r' x) * ‖y - x‖ = ‖y - x‖ / r' x := by
          field_simp [(hr'_pos x).ne'] <;> ring
        rw [h_eq]
        exact (div_lt_one (hr'_pos x)).mpr h10
      linarith
    have h12 : (x + (1 / r' x) • (y - x)) ∈ closedBall x b.rIn := by
      rw [h_rIn]; simpa [closedBall, dist_eq_norm] using h7
    exact b.one_of_mem_closedBall h12

  have hbump_support : ∀ (i : I), i ∈ s → Function.support (bump i) ⊆ ball i.val (2 * r' i.val) := by
    intro i _
    let x : E m := i.val
    let b : ContDiffBump x := default
    have h_rOut : b.rOut = 2 := by rfl
    intro y hy
    have h2 : bump i y ≠ 0 := hy
    by_contra h3
    have h4 : ‖y - x‖ ≥ 2 * r' x := by
      by_contra h5
      have h6 : ‖y - x‖ < 2 * r' x := by linarith
      have h7 : y ∈ ball x (2 * r' x) := by simpa [ball, dist_eq_norm] using h6
      exact h3 h7
    have h9 : 0 < 1 / r' x := by exact div_pos zero_lt_one (hr'_pos x)
    have h5 : ‖(1 / r' x) • (y - x)‖ ≥ 2 := by
      have h_norm : ‖(1 / r' x) • (y - x)‖ = |(1 / r' x)| * ‖y - x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      rw [h_norm, abs_of_pos h9]
      have h10 : (1 / r' x) * ‖y - x‖ ≥ (1 / r' x) * (2 * r' x) := by gcongr
      have h11 : (1 / r' x) * (2 * r' x) = 2 := by
        field_simp [(hr'_pos x).ne'] <;> ring
      linarith
    have h12 : b.rOut ≤ dist (x + (1 / r' x) • (y - x)) x := by
      rw [h_rOut]; simpa [dist_eq_norm] using h5
    have h13 : bump i y = 0 := b.zero_of_le_dist h12
    exact h2 h13

  let W : Set (E m) := ⋃ i ∈ s, ball i.val (r' i.val)
  have hW_open : IsOpen W := by apply isOpen_biUnion; intro _ _; exact isOpen_ball
  have hK_sub_W : K ⊆ W := hs

  let ψ : E m → ℝ := fun z => 1 - ∏ i ∈ s, (1 - bump i z)

  have hψ_diff : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    have h_bump_diff' : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (fun z => 1 - bump i z) := by
      intro i hi
      exact contDiff_const.sub (hbump_diff i hi)
    have h_prod : ContDiff ℝ (⊤ : ℕ∞) (fun z => ∏ i ∈ s, (1 - bump i z)) :=
      contDiff_finset_prod s (fun i => fun z => 1 - bump i z) h_bump_diff'
    exact contDiff_const.sub h_prod

  have hψ_one : EqOn ψ 1 W := by
    intro z hz
    have h_exists : ∃ (i : I), i ∈ s ∧ z ∈ ball i.val (r' i.val) := by
      simpa [W, Set.mem_iUnion] using hz
    rcases h_exists with ⟨i, hi, hzi⟩
    have h7 : bump i z = 1 := hbump_one i hi z hzi
    have h8 : ∏ j ∈ s, (1 - bump j z) = 0 := by
      apply Finset.prod_eq_zero hi
      rw [h7] <;> norm_num
    have h9 : ψ z = 1 - ∏ j ∈ s, (1 - bump j z) := by rfl
    rw [h9, h8] <;> norm_num

  have hψ_closure : closure (Function.support ψ) ⊆ V := by
    have h1 : Function.support ψ ⊆ ⋃ i ∈ s, closedBall i.val (2 * r' i.val) := by
      intro z hz
      have h2 : ψ z ≠ 0 := hz
      have h3 : ∃ (i : I), i ∈ s ∧ bump i z ≠ 0 := by
        by_contra h4
        push Not at h4
        have h5 : ∏ j ∈ s, (1 - bump j z) = 1 := by
          apply Finset.prod_eq_one
          intro j hj
          have h6 : bump j z = 0 := h4 j hj
          rw [h6] <;> norm_num
        have h7 : ψ z = 0 := by
          have h8 : ψ z = 1 - ∏ j ∈ s, (1 - bump j z) := by rfl
          rw [h8, h5] <;> norm_num
        exact h2 h7
      rcases h3 with ⟨i, hi, hne⟩
      have h4 : z ∈ Function.support (bump i) := hne
      have h5 : z ∈ ball i.val (2 * r' i.val) := hbump_support i hi h4
      have h6 : z ∈ closedBall i.val (2 * r' i.val) := ball_subset_closedBall h5
      exact Set.mem_iUnion₂.mpr ⟨i, hi, h6⟩
    have h2 : IsClosed (⋃ i ∈ s, closedBall i.val (2 * r' i.val)) := by
      have h_compact : IsCompact (⋃ i ∈ s, closedBall i.val (2 * r' i.val)) :=
        Finset.isCompact_biUnion s (fun x _ => isCompact_closedBall x.val (2 * r' x.val))
      exact h_compact.isClosed
    have h3 : closure (Function.support ψ) ⊆ ⋃ i ∈ s, closedBall i.val (2 * r' i.val) :=
      closure_minimal h1 h2
    have h4 : (⋃ i ∈ s, closedBall i.val (2 * r' i.val)) ⊆ V := by
      intro z hz
      rcases Set.mem_iUnion₂.mp hz with ⟨i, hi, hzi⟩
      exact hr'_sub i.val i.prop hzi
    exact h3.trans h4

  exact ⟨ψ, W, hW_open, hK_sub_W, hψ_closure, hψ_diff, hψ_one⟩

/-- Given compact `K ⊆ V` open and `f` C¹ on `V`, there exists a globally C¹
function `g` agreeing with `f` on an open neighborhood of `K`. -/
lemma exists_c1_extension
    {K V : Set (E m)} (hK : IsCompact K) (hV_open : IsOpen V) (hK_sub : K ⊆ V)
    (f : E m → ℝ) (hf : ContDiffOn ℝ 1 f V) :
    ∃ (g : E m → ℝ) (W : Set (E m)),
      IsOpen W ∧ K ⊆ W ∧ ContDiff ℝ 1 g ∧ EqOn g f W := by
  rcases exists_smooth_indicator hK hV_open hK_sub with
    ⟨ψ, W, hW_open, hK_sub_W, hψ_closure, hψ_diff, hψ_one⟩
  let g : E m → ℝ := fun z => ψ z * f z
  have hg_on_V : ContDiffOn ℝ 1 g V := by
    apply ContDiffOn.mul
    · exact hψ_diff.of_le (by simp) |>.contDiffOn
    · exact hf
  have h_main : ContDiff ℝ 1 g := by
    have h1 : ∀ (x : E m), ContDiffAt ℝ 1 g x := by
      intro x
      by_cases hx : x ∈ V
      · exact hg_on_V.contDiffAt (hV_open.mem_nhds hx)
      · have h2 : x ∉ closure (Function.support ψ) := by
          intro h3
          exact hx (hψ_closure h3)
        have h3 : IsOpen (closure (Function.support ψ))ᶜ := isOpen_compl_iff.mpr isClosed_closure
        have h4 : ∀ᶠ (y : E m) in nhds x, y ∈ (closure (Function.support ψ))ᶜ :=
          h3.mem_nhds h2
        have h5 : ∀ᶠ (y : E m) in nhds x, ψ y = 0 := by
          filter_upwards [h4] with y hy
          have h6 : y ∉ Function.support ψ := by
            intro h7
            exact hy (subset_closure h7)
          simpa [Function.mem_support] using h6
        have h6 : ∀ᶠ (y : E m) in nhds x, g y = 0 := by
          filter_upwards [h5] with y hy
          dsimp only [g]
          rw [hy] <;> ring
        exact contDiffAt_const.congr_of_eventuallyEq h6
    exact contDiff_iff_contDiffAt.mpr h1
  have hg_eq : EqOn g f W := by
    intro z hz
    have h1 : ψ z = 1 := hψ_one hz
    dsimp only [g]
    rw [h1] <;> ring
  exact ⟨g, W, hW_open, hK_sub_W, h_main, hg_eq⟩

-- ============================================================================
-- Measure-preserving equivalence E(m) × ℝ ≅ E(m+1)
-- ============================================================================

/-- Linear equivalence `E(m) × ℝ ≃ E(m+1)` via `unsplit`. -/
noncomputable def unsplitEquiv : (E m × ℝ) ≃ₗ[ℝ] E (m + 1) :=
  { toFun := fun p : E m × ℝ => unsplit p.1 p.2
    invFun := fun y : E (m + 1) => (GraphAreaFormula.proj y, coordECL y)
    map_add' := by
      intro p q
      simp [unsplit_eq, inclEm.map_add, scaleE.map_add] <;> abel
    map_smul' := by
      intro c p
      have h1 : (c • p).1 = c • p.1 := by simp
      have h2 : (c • p).2 = c * p.2 := by simp
      rw [h1, h2]
      have h3 : inclEm (c • p.1) = c • inclEm p.1 := inclEm.map_smul c p.1
      have h4 : (scaleE (c * p.2) : E (m + 1)) = c • (scaleE p.2 : E (m + 1)) := by
        simpa [scaleE, smul_smul] using rfl
      have h5 : unsplit (c • p.1) (c * p.2) = c • unsplit p.1 p.2 := by
        rw [unsplit_eq (c * p.2) (c • p.1), unsplit_eq p.2 p.1, h3, h4, smul_add]
        <;> simp
      exact h5
    left_inv := by
      intro p
      have h1 : GraphAreaFormula.proj (unsplit p.1 p.2) = p.1 :=
        GraphAreaFormula.graphMap_proj (fun _ => p.2) p.1
      have h2 : coordECL (unsplit p.1 p.2) = p.2 := by
        rw [unsplit_eq p.2 p.1]
        have h := coordECL.map_add (inclEm p.1) (scaleE p.2 : E (m + 1))
        rw [h]
        have h21 : coordECL (inclEm p.1) = 0 := by
          simp [coordECL, inclEm, GraphAreaFormula.F_lin_apply_last]
        have h22 : coordECL (scaleE p.2 : E (m + 1)) = p.2 := by
          have h_scaleE : (scaleE p.2 : E (m + 1)) = p.2 • (eLast : E (m + 1)) := by rfl
          rw [h_scaleE]
          have h_smul : coordECL (p.2 • (eLast : E (m + 1))) = p.2 * coordECL (eLast : E (m + 1)) :=
            coordECL.map_smul p.2 (eLast : E (m + 1))
          rw [h_smul, coordECL_eLast] <;> ring
        rw [h21, h22] <;> ring
      exact Prod.ext h1 h2
    right_inv := by
      intro y
      have h1 : unsplit (GraphAreaFormula.proj y) (coordECL y) = y := by
        rw [unsplit_eq (coordECL y) (GraphAreaFormula.proj y)]
        let v : E (m + 1) := inclEm (GraphAreaFormula.proj y) + scaleE (coordECL y)
        have hv : v = inclEm (GraphAreaFormula.proj y) + scaleE (coordECL y) := rfl
        ext i
        by_cases hlt : i.val < m
        · let j : Fin m := ⟨i.val, hlt⟩
          have hi : i = Fin.castSucc j := by
            apply Fin.ext
            simp [j, Fin.castSucc]
          rw [hi]
          have h_a : (inclEm (GraphAreaFormula.proj y)) (Fin.castSucc j) = (GraphAreaFormula.proj y) j :=
            GraphAreaFormula.F_lin_apply_castSucc (0 : E m →L[ℝ] ℝ) (GraphAreaFormula.proj y) j
          have h_b : (scaleE (coordECL y) : E (m + 1)) (Fin.castSucc j) = 0 := by
            have h_eLast : (eLast : E (m + 1)) (Fin.castSucc j) = 0 := by
              simp [eLast, EuclideanSpace.single_apply] <;> omega
            simp [scaleE, h_eLast] <;> ring
          have h_c : (GraphAreaFormula.proj y) j = y (Fin.castSucc j) := by
            simp [GraphAreaFormula.proj_apply] <;> rfl
          have h_sum : v (Fin.castSucc j) = (inclEm (GraphAreaFormula.proj y)) (Fin.castSucc j) + (scaleE (coordECL y)) (Fin.castSucc j) := by
            rw [hv] <;> rfl
          rw [h_sum, h_a, h_b, h_c] <;> ring
        · have hval : i.val = m := by omega
          have hi : i = Fin.last m := by
            apply Fin.ext
            simp [hval, Fin.last] <;> omega
          rw [hi]
          have h_a : (inclEm (GraphAreaFormula.proj y)) (Fin.last m) = 0 :=
            GraphAreaFormula.F_lin_apply_last (0 : E m →L[ℝ] ℝ) (GraphAreaFormula.proj y)
          have h_b : (scaleE (coordECL y) : E (m + 1)) (Fin.last m) = coordECL y := by
            have h_scaleE : (scaleE (coordECL y) : E (m + 1)) = (coordECL y) • (eLast : E (m + 1)) := by rfl
            rw [h_scaleE]
            have h_smul : ((coordECL y) • (eLast : E (m + 1))) (Fin.last m) =
                (coordECL y) * (eLast : E (m + 1)) (Fin.last m) := by exact Real.ext_cauchy rfl
            rw [h_smul]
            have h_eLast : (eLast : E (m + 1)) (Fin.last m) = 1 := by
              simp [eLast, EuclideanSpace.single_apply] <;> omega
            rw [h_eLast] <;> ring
          have h_c : coordECL y = y (Fin.last m) := by
            simp [coordECL] <;> rfl
          have h_sum : v (Fin.last m) = (inclEm (GraphAreaFormula.proj y)) (Fin.last m) + (scaleE (coordECL y)) (Fin.last m) := by
            rw [hv] <;> rfl
          rw [h_sum, h_a, h_b, h_c] <;> ring
      exact h1 }

/-- Measure-preserving property of `unsplitEquiv`.
Proof: `unsplitEquiv.symm` equals `eSplit m`, the coordinate-splitting equiv
from `PrekopaLeindler`, which is known to preserve Lebesgue volume. -/
lemma unsplitEquiv_measurePreserving :
    MeasureTheory.MeasurePreserving (unsplitEquiv : (E m × ℝ) → E (m + 1)) volume volume := by
  let eSplit_m : E (m + 1) ≃ᵐ (E m × ℝ) := eSplit m
  have h_eq : (unsplitEquiv.symm : E (m + 1) → E m × ℝ) = (eSplit_m : E (m + 1) → E m × ℝ) := by
    funext y
    have h1 : (eSplit_m : E (m + 1) → E m × ℝ) y = (GraphAreaFormula.proj y, coordECL y) := by
      simp [eSplit_m, eSplit, eOfLp, eToLp, MeasurableEquiv.piFinSuccAbove_apply,
        GraphAreaFormula.proj, coordECL, EuclideanSpace.equiv]
      <;> ext i <;> simp [Fin.succAbove] <;> rfl
    have h2 : unsplitEquiv.symm y = (GraphAreaFormula.proj y, coordECL y) := by rfl
    rw [h1, h2]
  have h1 : MeasurePreserving (eSplit_m : E (m + 1) → E m × ℝ) volume volume :=
    eSplit_measurePreserving m
  have h2 : MeasurePreserving (eSplit_m.symm : E m × ℝ → E (m + 1)) volume volume := h1.symm
  have h3 : (unsplitEquiv : (E m × ℝ) → E (m + 1)) = (eSplit_m.symm : E m × ℝ → E (m + 1)) := by
    funext x
    have h4 : (eSplit_m : E (m + 1) → E m × ℝ) (unsplitEquiv x) = x := by
      have h5 : (unsplitEquiv.symm : E (m + 1) → E m × ℝ) (unsplitEquiv x) = x :=
        unsplitEquiv.left_inv x
      rw [h_eq] at h5
      exact h5
    have h6 : (eSplit_m : E (m + 1) → E m × ℝ) (eSplit_m.symm x) = x := eSplit_m.right_inv x
    exact eSplit_m.injective (h4.trans h6.symm)
  rw [h3]
  exact h2

-- ============================================================================
-- Single-patch coarea formula
-- ============================================================================

/-- **Single-patch coarea formula.** -/
lemma coarea_single_patch
    (f : E (m + 1) → ℝ)
    (hf : ContDiff ℝ 1 f)
    (φ : OpenPartialHomeomorph (E (m + 1)) (E (m + 1)))
    (hφ_coe : (φ : E (m + 1) → E (m + 1)) =
        fun y => projHCL y + f y • (eLast : E (m + 1)))
    (hφ_symm_diff : ContDiffOn ℝ 1 φ.symm φ.target)
    {V : Set (E (m + 1))}
    (hV_source : V ⊆ φ.source)
    (hV_reg : ∀ y ∈ V, (fderiv ℝ f y) (eLast : E (m + 1)) ≠ 0)
    (A : Set (E (m + 1)))
    (hA : MeasurableSet A)
    (hA_compact : IsCompact A)
    (hA_sub : A ⊆ V) :
    ∫⁻ (t : ℝ), μHE[m] (A ∩ {y | f y = t}) =
    ∫⁻ (y : E (m + 1)) in A, ENNReal.ofReal ‖fderiv ℝ f y‖ := by
  classical
  let S : Set (E (m + 1)) := φ '' A
  have h_target_meas : MeasurableSet φ.target := φ.open_target.measurableSet

  have hS_meas : MeasurableSet S := by
    have h1 : S = φ.target ∩ (φ.symm ⁻¹' A) := by
      ext y
      constructor
      · rintro ⟨x, hxA, rfl⟩
        have hx_src : x ∈ φ.source := hV_source (hA_sub hxA)
        have h_in_tgt : φ x ∈ φ.target := φ.mapsTo hx_src
        have h_symm : φ.symm (φ x) = x := φ.left_inv hx_src
        have h_goal : φ.symm (φ x) ∈ A := by rw [h_symm]; exact hxA
        exact ⟨h_in_tgt, by simpa [Set.mem_preimage] using h_goal⟩
      · rintro ⟨hy_tgt, hyA⟩
        refine ⟨φ.symm y, hyA, φ.right_inv hy_tgt⟩
    rw [h1]
    have h3 : ContinuousOn φ.symm φ.target := φ.continuousOn_symm
    let g : φ.target → E (m + 1) := fun x => φ.symm x
    have hg_cont : Continuous g := continuousOn_iff_continuous_restrict.mp h3
    have hg_meas : Measurable g := hg_cont.measurable
    have h4 : MeasurableSet (g ⁻¹' A) := hA.preimage hg_meas
    have h5 : MeasurableSet (Subtype.val '' (g ⁻¹' A)) :=
      MeasurableSet.subtype_image h_target_meas h4
    have h6 : Subtype.val '' (g ⁻¹' A) = φ.target ∩ φ.symm ⁻¹' A := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff]
      constructor
      · rintro ⟨x, hxA, rfl⟩
        have hxt : (x : E (m + 1)) ∈ φ.target := x.prop
        exact ⟨hxt, hxA⟩
      · rintro ⟨hyt, hyA⟩
        exact ⟨⟨y, hyt⟩, hyA, rfl⟩
    rw [←h6]
    exact h5

  -- Measurable extension of φ.symm by zero outside φ.target
  let φ_symm_ext : E (m + 1) → E (m + 1) := fun p =>
    if p ∈ φ.target then φ.symm p else 0
  have hφ_symm_cont_on : ContinuousOn φ.symm φ.target := hφ_symm_diff.continuousOn
  have hφ_symm_ext_meas : Measurable φ_symm_ext := by
    have h_main : ∀ (B : Set (E (m + 1))), MeasurableSet B →
        MeasurableSet (φ_symm_ext ⁻¹' B) := by
      intro B hB
      by_cases h0 : (0 : E (m + 1)) ∈ B
      · -- 0 ∈ B: preimage = (φ.target ∩ φ.symm ⁻¹' B) ∪ (φ.target)ᶜ
        have h_eq : φ_symm_ext ⁻¹' B = (φ.target ∩ φ.symm ⁻¹' B) ∪ (φ.target)ᶜ := by
          ext p
          simp [φ_symm_ext, h0] <;> split_ifs <;> tauto
        rw [h_eq]
        have h2 : MeasurableSet (φ.target ∩ φ.symm ⁻¹' B) := by
          have h_restrict_cont : Continuous (fun x : φ.target => φ.symm x) :=
            continuousOn_iff_continuous_restrict.mp hφ_symm_cont_on
          have h_restrict_meas : Measurable (fun x : φ.target => φ.symm x) :=
            h_restrict_cont.measurable
          have h4 : MeasurableSet ((fun x : φ.target => φ.symm x) ⁻¹' B) :=
            hB.preimage h_restrict_meas
          have h5 : MeasurableSet (Subtype.val '' ((fun x : φ.target => φ.symm x) ⁻¹' B)) :=
            MeasurableSet.subtype_image h_target_meas h4
          have h6 : Subtype.val '' ((fun x : φ.target => φ.symm x) ⁻¹' B) = φ.target ∩ φ.symm ⁻¹' B := by
            ext y
            simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff]
            constructor
            · rintro ⟨x, hx, rfl⟩
              exact ⟨x.prop, hx⟩
            · rintro ⟨hyt, hyA⟩
              exact ⟨⟨y, hyt⟩, hyA, rfl⟩
          rw [←h6]
          exact h5
        exact h2.union h_target_meas.compl
      · -- 0 ∉ B: preimage = φ.target ∩ φ.symm ⁻¹' B
        have h_eq : φ_symm_ext ⁻¹' B = φ.target ∩ φ.symm ⁻¹' B := by
          ext p
          simp [φ_symm_ext, h0] <;> split_ifs <;> tauto
        rw [h_eq]
        have h_restrict_cont : Continuous (fun x : φ.target => φ.symm x) :=
          continuousOn_iff_continuous_restrict.mp hφ_symm_cont_on
        have h_restrict_meas : Measurable (fun x : φ.target => φ.symm x) :=
          h_restrict_cont.measurable
        have h4 : MeasurableSet ((fun x : φ.target => φ.symm x) ⁻¹' B) :=
          hB.preimage h_restrict_meas
        have h5 : MeasurableSet (Subtype.val '' ((fun x : φ.target => φ.symm x) ⁻¹' B)) :=
          MeasurableSet.subtype_image h_target_meas h4
        have h6 : Subtype.val '' ((fun x : φ.target => φ.symm x) ⁻¹' B) = φ.target ∩ φ.symm ⁻¹' B := by
          ext y
          simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff]
          constructor
          · rintro ⟨x, hx, rfl⟩
            exact ⟨x.prop, hx⟩
          · rintro ⟨hyt, hyA⟩
            exact ⟨⟨y, hyt⟩, hyA, rfl⟩
        rw [←h6]
        exact h5
    exact h_main

  -- Define h(p) = indicator_S(p) * J(p), using measurable extension
  let J : E (m + 1) → ENNReal := fun p =>
    ENNReal.ofReal (‖fderiv ℝ f (φ_symm_ext p)‖ /
      |(fderiv ℝ f (φ_symm_ext p)) (eLast : E (m + 1))|)
  have hJ_meas : Measurable J := by fun_prop
  let h : E (m + 1) → ENNReal := Set.indicator S J
  have h_h_meas : Measurable h := hJ_meas.indicator hS_meas

  -- On S, φ_symm_ext = φ.symm
  have h_ext_eq : ∀ p ∈ S, φ_symm_ext p = φ.symm p := by
    intro p hp
    have h_p_tgt : p ∈ φ.target := by
      rcases hp with ⟨x, _, rfl⟩
      exact φ.mapsTo (hV_source (hA_sub ‹_›))
    simp [φ_symm_ext, h_p_tgt]

  -- S is compact
  have hφ_cont_on_source : ContinuousOn φ φ.source :=
    φ.toPartialHomeomorph.continuousOn_toFun
  have hφ_on_A : ContinuousOn φ A :=
    hφ_cont_on_source.mono (hA_sub.trans hV_source)
  have hS_compact : IsCompact S := hA_compact.image_of_continuousOn hφ_on_A

  -- For each t, construct B_t and C¹ extension, then apply slice lemma
  have h_slice : ∀ (t : ℝ),
      (∫⁻ (z : E m), h (unsplit z t)) = μHE[m] (A ∩ {y | f y = t}) := by
    intro t
    let B_t : Set (E m) := {z | unsplit z t ∈ S}
    have h_cont_unsplit : Continuous (fun z : E m => unsplit z t) := by
      have h : (fun z : E m => unsplit z t) = fun z => inclEm z + scaleE t := by
        funext z; exact unsplit_eq t z
      rw [h]; fun_prop
    have hB_meas : MeasurableSet B_t := h_cont_unsplit.measurable hS_meas

    have hB_closed : IsClosed B_t := hS_compact.isClosed.preimage h_cont_unsplit
    let h_inclEm_iso : Isometry (inclEm : E m → E (m + 1)) :=
      Isometry.of_dist_eq fun (x y : E m) => by
        have h1 : dist (inclEm x) (inclEm y) = ‖inclEm (x - y)‖ := by
          rw [dist_eq_norm, ← inclEm.map_sub] <;> rfl
        rw [h1, inclEm_isometry (x - y), ← dist_eq_norm]
    have hB_bdd : Bornology.IsBounded B_t := by
      have h_iso : Isometry (fun z : E m => unsplit z t) :=
        Isometry.of_dist_eq fun (x y : E m) => by
          have h_eq1 : unsplit x t = inclEm x + scaleE t := unsplit_eq t x
          have h_eq2 : unsplit y t = inclEm y + scaleE t := unsplit_eq t y
          rw [h_eq1, h_eq2]
          have h1 : inclEm x + scaleE t - (inclEm y + scaleE t) = inclEm (x - y) := by
            have h2 : inclEm x + scaleE t - (inclEm y + scaleE t) = inclEm x - inclEm y := by abel
            rw [h2, ← inclEm.map_sub]
          rw [dist_eq_norm, h1, inclEm_isometry (x - y), ← dist_eq_norm]
      have h_antilipschitz : AntilipschitzWith 1 (fun z : E m => unsplit z t) :=
        Isometry.antilipschitz h_iso
      exact AntilipschitzWith.isBounded_preimage h_antilipschitz hS_compact.isBounded
    have hB_compact : IsCompact B_t :=
      Metric.isCompact_of_isClosed_isBounded hB_closed hB_bdd

    let V_t : Set (E m) := {z | unsplit z t ∈ φ.target}
    have hVt_open : IsOpen V_t := by
      have h_cont : Continuous (fun z : E m => unsplit z t) := by
        have h : (fun z : E m => unsplit z t) = fun z => inclEm z + scaleE t := by
          funext z; exact unsplit_eq t z
        rw [h]; fun_prop
      exact h_cont.isOpen_preimage _ φ.open_target
    have hB_sub_Vt : B_t ⊆ V_t := by
      intro z hz
      have h5 : unsplit z t ∈ S := hz
      have h6 : S ⊆ φ.target := by
        intro y hy
        rcases hy with ⟨x, _, rfl⟩
        exact φ.mapsTo (hV_source (hA_sub ‹_›))
      exact h6 h5

    let implicit_fun : E m → ℝ := fun z => coordECL (φ.symm (unsplit z t))
    have h_implicit_diff : ContDiffOn ℝ 1 implicit_fun V_t := by
      have h_cont : Continuous (fun z : E m => unsplit z t) := by
        have h : (fun z : E m => unsplit z t) = fun z => inclEm z + scaleE t := by
          funext z; exact unsplit_eq t z
        rw [h]; fun_prop
      have h3 : ContDiff ℝ 1 (fun z : E m => unsplit z t) := by
        have h_eq : (fun z : E m => unsplit z t) = fun z => inclEm z + scaleE t := by
          funext z; exact unsplit_eq t z
        rw [h_eq]
        let i : E m →L[ℝ] E (m + 1) := inclEm
        have h_incl : ContDiff ℝ 1 i := i.contDiff
        exact h_incl.add contDiff_const
      have h4 : MapsTo (fun z : E m => unsplit z t) V_t φ.target := by
        intro z hz; exact hz
      have h5 : ContDiffOn ℝ 1 φ.symm φ.target := hφ_symm_diff
      have h6 : ContDiffOn ℝ 1 (fun z => φ.symm (unsplit z t)) V_t :=
        h5.comp h3.contDiffOn h4
      let c : E (m + 1) →L[ℝ] ℝ := coordECL
      have h7 : ContDiff ℝ 1 c := c.contDiff
      have h_univ : MapsTo (fun z : E m => φ.symm (unsplit z t)) V_t Set.univ :=
        fun _ _ => Set.mem_univ _
      exact h7.contDiffOn.comp h6 h_univ

    rcases exists_c1_extension hB_compact hVt_open hB_sub_Vt implicit_fun h_implicit_diff with
      ⟨g_t, U, hU_open, hB_sub_U, hgt_diff, hgt_eq_on⟩

    have h1 : ∫⁻ (z : E m), h (unsplit z t) = ∫⁻ (z : E m) in B_t, h (unsplit z t) := by
      have h_eq : ∀ (z : E m), h (unsplit z t) =
          Set.indicator B_t (fun z => h (unsplit z t)) z := by
        intro z
        by_cases hz : z ∈ B_t
        · simp [hz, Set.indicator_apply]
        · have h9 : h (unsplit z t) = 0 := by
            have h10 : unsplit z t ∉ S := by simpa [B_t] using hz
            simp [h, h10, Set.indicator_apply]
          simp [hz, Set.indicator_apply, h9]
      rw [lintegral_congr h_eq]
      rw [← lintegral_indicator hB_meas] <;> rfl
    rw [h1]
    have h2 : ∀ (z : E m), z ∈ B_t →
        h (unsplit z t) = ENNReal.ofReal (‖fderiv ℝ f (φ.symm (unsplit z t))‖ /
          |(fderiv ℝ f (φ.symm (unsplit z t))) (eLast : E (m + 1))|) := by
      intro z hz
      have h3 : unsplit z t ∈ S := hz
      have h4 : φ_symm_ext (unsplit z t) = φ.symm (unsplit z t) := h_ext_eq (unsplit z t) h3
      simp [h, J, h3, Set.indicator_apply, h4] <;> rfl
    have h3 : ∫⁻ (z : E m) in B_t, h (unsplit z t) =
        ∫⁻ (z : E m) in B_t, ENNReal.ofReal (‖fderiv ℝ f (φ.symm (unsplit z t))‖ /
          |(fderiv ℝ f (φ.symm (unsplit z t))) (eLast : E (m + 1))|) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hB_meas] with z hz
      exact h2 z hz
    rw [h3]
    exact (coarea_graph_slice_local f hf φ hφ_coe hV_source hV_reg A hA hA_sub t
      g_t hgt_diff U hU_open B_t hB_sub_U hgt_eq_on rfl).symm

  -- Fubini
  have h_fubini : (∫⁻ (p : E (m + 1)), h p) =
      ∫⁻ (t : ℝ), ∫⁻ (z : E m), h (unsplit z t) := by
    have hmp := unsplitEquiv_measurePreserving (m := m)
    have h1 : (∫⁻ (p : E (m + 1)), h p) =
        ∫⁻ (q : E m × ℝ), h (unsplitEquiv q) :=
      (hmp.lintegral_comp h_h_meas).symm
    rw [h1]
    let F : (E m × ℝ) → ENNReal := fun q => h (unsplitEquiv q)
    have hF_meas : Measurable F := h_h_meas.comp hmp.measurable
    have hvol : (volume : Measure (E m × ℝ)) = Measure.prod volume volume :=
      MeasureTheory.Measure.volume_eq_prod (E m) ℝ
    have h2 : ∫⁻ (q : E m × ℝ), F q = ∫⁻ (t : ℝ), ∫⁻ (z : E m), F (z, t) := by
      rw [hvol]
      exact MeasureTheory.lintegral_prod_symm' F hF_meas
    rw [h2]
    <;> rfl

  have h_left : (∫⁻ (p : E (m + 1)), h p) =
      ∫⁻ (t : ℝ), μHE[m] (A ∩ {y | f y = t}) := by
    rw [h_fubini]
    apply lintegral_congr
    intro t
    exact h_slice t

  -- Change of variables
  have h_fderiv : ∀ (y : E (m + 1)), HasStrictFDerivAt φ (coareaPhiFDeriv (fderiv ℝ f y)) y := by
    intro y
    have h_diff : Differentiable ℝ f := (contDiff_one_iff_fderiv.mp hf).1
    have h_cont : Continuous (fderiv ℝ f) := (contDiff_one_iff_fderiv.mp hf).2
    have h_der : ∀ᶠ w in nhds y, HasFDerivAt f (fderiv ℝ f w) w := by
      filter_upwards with w
      exact h_diff.differentiableAt.hasFDerivAt
    have h_fderiv_strict : HasStrictFDerivAt f (fderiv ℝ f y) y :=
      hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt h_der h_cont.continuousAt
    have h_a : HasStrictFDerivAt (fun y => projHCL y) projHCL y := projHCL.hasStrictFDerivAt
    have h_b : HasStrictFDerivAt (fun y : E (m + 1) => f y • (eLast : E (m + 1)))
        ((fderiv ℝ f y).smulRight (eLast : E (m + 1))) y :=
      h_fderiv_strict.smul_const (eLast : E (m + 1))
    let D := coareaPhiFDeriv (fderiv ℝ f y)
    have hD_eq : D = projHCL + scaleE.comp (fderiv ℝ f y) := by ext x; rfl
    have h_sum : HasStrictFDerivAt (fun y : E (m + 1) => projHCL y + f y • (eLast : E (m + 1)))
        (projHCL + scaleE.comp (fderiv ℝ f y)) y := h_a.add h_b
    have h_sum2 : HasStrictFDerivAt (fun y : E (m + 1) => projHCL y + f y • (eLast : E (m + 1))) D y := by
      exact hD_eq.symm ▸ h_sum
    have hφ_eq : (φ : E (m + 1) → E (m + 1)) = (fun y : E (m + 1) => projHCL y + f y • (eLast : E (m + 1))) := hφ_coe
    rw [hφ_eq]
    exact h_sum2

  have h_fderiv_on : ∀ (y : E (m + 1)), y ∈ A →
      HasFDerivWithinAt φ (coareaPhiFDeriv (fderiv ℝ f y)) A y := by
    intro y _
    exact (h_fderiv y).hasFDerivAt.hasFDerivWithinAt

  have h_inj : Set.InjOn φ A := by
    intro y1 hy1 y2 hy2 h
    have h1 : y1 ∈ φ.source := hV_source (hA_sub hy1)
    have h2 : y2 ∈ φ.source := hV_source (hA_sub hy2)
    have h3 : φ.symm (φ y1) = φ.symm (φ y2) := by rw [h]
    have h4 : φ.symm (φ y1) = y1 := φ.left_inv h1
    have h5 : φ.symm (φ y2) = y2 := φ.left_inv h2
    rw [h4, h5] at h3
    exact h3

  have h_cov : (∫⁻ (p : E (m + 1)) in S, h p) =
      ∫⁻ (y : E (m + 1)) in A,
        ENNReal.ofReal |(coareaPhiFDeriv (fderiv ℝ f y)).det| * h (φ y) :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      volume hA h_fderiv_on h_inj h

  have h_support : (∫⁻ (p : E (m + 1)), h p) = ∫⁻ (p : E (m + 1)) in S, h p := by
    have h1 : h = Set.indicator S h := by
      funext p
      by_cases h2 : p ∈ S
      · simp [h, h2, Set.indicator_apply]
      · simp [h, h2, Set.indicator_apply]
    have h2 : ∫⁻ (p : E (m + 1)), Set.indicator S h p = ∫⁻ (p : E (m + 1)) in S, h p :=
      lintegral_indicator hS_meas h
    have h3 : ∫⁻ (p : E (m + 1)), h p = ∫⁻ (p : E (m + 1)), Set.indicator S h p :=
      congr_arg (fun f : E (m + 1) → ENNReal => ∫⁻ p, f p) h1
    rw [h3, h2]

  have h_algebra : ∀ (y : E (m + 1)), y ∈ A →
      ENNReal.ofReal |(coareaPhiFDeriv (fderiv ℝ f y)).det| * h (φ y) =
      ENNReal.ofReal ‖fderiv ℝ f y‖ := by
    intro y hy
    have h_reg : (fderiv ℝ f y) (eLast : E (m + 1)) ≠ 0 := hV_reg y (hA_sub hy)
    have h_y_src : y ∈ φ.source := hV_source (hA_sub hy)
    have h_phi_y_in_S : φ y ∈ S := ⟨y, hy, rfl⟩
    have h_det : (coareaPhiFDeriv (fderiv ℝ f y)).det =
        (fderiv ℝ f y) (eLast : E (m + 1)) :=
      det_coareaPhiFDeriv (fderiv ℝ f y)
    have h_symm : φ.symm (φ y) = y := φ.left_inv h_y_src
    have h_ext : φ_symm_ext (φ y) = φ.symm (φ y) := h_ext_eq (φ y) h_phi_y_in_S
    have h_h_val : h (φ y) = ENNReal.ofReal (‖fderiv ℝ f y‖ /
        |(fderiv ℝ f y) (eLast : E (m + 1))|) := by
      simp [h, J, h_phi_y_in_S, Set.indicator_apply, h_ext, h_symm] <;> rfl
    rw [h_h_val, h_det]
    have h_pos : 0 < |(fderiv ℝ f y) (eLast : E (m + 1))| := abs_pos.mpr h_reg
    have h_mul : ENNReal.ofReal |(fderiv ℝ f y) (eLast : E (m + 1))| *
        ENNReal.ofReal (‖fderiv ℝ f y‖ / |(fderiv ℝ f y) (eLast : E (m + 1))|) =
        ENNReal.ofReal (|(fderiv ℝ f y) (eLast : E (m + 1))| *
          (‖fderiv ℝ f y‖ / |(fderiv ℝ f y) (eLast : E (m + 1))|)) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [h_mul]
    have h_cancel : |(fderiv ℝ f y) (eLast : E (m + 1))| *
        (‖fderiv ℝ f y‖ / |(fderiv ℝ f y) (eLast : E (m + 1))|) = ‖fderiv ℝ f y‖ := by
      field_simp [h_pos.ne'] <;> ring
    rw [h_cancel]

  have h_right : (∫⁻ (p : E (m + 1)) in S, h p) =
      ∫⁻ (y : E (m + 1)) in A, ENNReal.ofReal ‖fderiv ℝ f y‖ := by
    rw [h_cov]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hA] with y hy
    exact h_algebra y hy

  calc
    (∫⁻ (t : ℝ), μHE[m] (A ∩ {y | f y = t}))
      = (∫⁻ (p : E (m + 1)), h p) := h_left.symm
    _ = (∫⁻ (p : E (m + 1)) in S, h p) := h_support
    _ = (∫⁻ (y : E (m + 1)) in A, ENNReal.ofReal ‖fderiv ℝ f y‖) := h_right

end Geometry
