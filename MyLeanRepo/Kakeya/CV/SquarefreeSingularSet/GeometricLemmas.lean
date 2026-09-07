import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSet.AlgebraicLemmas
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Compactness.Lindelof

/-!
# Geometric lemmas for the squarefree singular set proof

Main result: `plane_curve_dimH_le_one` — a nonzero polynomial in R² has zero
set of Hausdorff dimension at most 1.
-/

noncomputable section

open MeasureTheory Metric Set MvPolynomial
open scoped ENNReal

namespace Kakeya.CV

abbrev P2 := EuclideanSpace ℝ (Fin 2)

/-- `polynomialValue` for Fin 2 is C^∞. -/
lemma polynomial_contDiff2 (h : MvPolynomial (Fin 2) ℝ) :
    ContDiff ℝ ⊤ (polynomialValue h) := by
  induction h using MvPolynomial.induction_on with
  | C a =>
    have h' : polynomialValue (C a) = (fun (_ : P2) => a) := by
      funext y; simp [polynomialValue]
    rw [h']; exact contDiff_const
  | add p q hp hq =>
    have h_eq : polynomialValue (p + q) = fun y => polynomialValue p y + polynomialValue q y := by
      funext y; simp [polynomialValue, eval_add]
    rw [h_eq]; exact hp.add hq
  | mul_X p i hp =>
    let coordI : P2 →L[ℝ] ℝ :=
      { toFun := fun x => x i
        map_add' := by intro x y; simp
        map_smul' := by intro c x; simp }
    have h_eq : polynomialValue (p * X i) = fun y => polynomialValue p y * y i := by
      funext y; simp [polynomialValue, eval_mul, eval_X]
    rw [h_eq]; exact hp.mul coordI.contDiff

/-- Coordinate equivalence P2 ≃ ℝ × ℝ. -/
def p2Equiv : P2 ≃L[ℝ] (ℝ × ℝ) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans
    (LinearEquiv.piFinTwo ℝ (fun _ => ℝ)).toContinuousLinearEquiv

/-- Directional derivative of polynomial evaluation at u in direction v. -/
lemma deriv_polynomialValue_direction_gen (h : MvPolynomial (Fin 2) ℝ) (u v : P2) :
    HasDerivAt (fun t : ℝ => polynomialValue h (u + t • v))
      (∑ i : Fin 2, v i * polynomialValue (pderiv i h) u) 0 := by
  induction h using MvPolynomial.induction_on with
  | C a =>
    have h1 : (fun t : ℝ => polynomialValue (C a) (u + t • v)) = fun (_ : ℝ) => a := by
      funext t; simp [polynomialValue]
    rw [h1]
    have h2 : (∑ i : Fin 2, v i * polynomialValue (pderiv i (C a)) u) = 0 := by
      simp [polynomialValue]
    rw [h2]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    have h_eq1 : (fun t : ℝ => polynomialValue (p + q) (u + t • v)) =
        fun t => polynomialValue p (u + t • v) + polynomialValue q (u + t • v) := by
      funext t; simp [polynomialValue, eval_add]
    rw [h_eq1]
    have h_sum : (∑ i : Fin 2, v i * polynomialValue (pderiv i (p + q)) u) =
        (∑ i : Fin 2, v i * polynomialValue (pderiv i p) u) +
        (∑ i : Fin 2, v i * polynomialValue (pderiv i q) u) := by
      have h3 : ∀ i, pderiv i (p + q) = pderiv i p + pderiv i q := by
        intro i; exact map_add (pderiv i) p q
      have h4 : ∑ i : Fin 2, v i * polynomialValue (pderiv i (p + q)) u =
          ∑ i : Fin 2, (v i * polynomialValue (pderiv i p) u + v i * polynomialValue (pderiv i q) u) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [h3 i]
        simp [polynomialValue, eval_add] <;> ring
      rw [h4, Finset.sum_add_distrib]
    rw [h_sum]
    exact hp.add hq
  | mul_X p i hp =>
    have h_eq1 : (fun t : ℝ => polynomialValue (p * X i) (u + t • v)) =
        fun t => polynomialValue p (u + t • v) * (u i + t * v i) := by
      funext t; simp [polynomialValue, eval_mul, eval_X] <;> ring
    rw [h_eq1]
    have h3 : ∀ j : Fin 2, pderiv j (p * X i) = (pderiv j p) * X i + p * pderiv j (X i) := by
      intro j; exact pderiv_mul
    have h4 : ∀ j : Fin 2, polynomialValue (pderiv j (p * X i)) u =
        polynomialValue (pderiv j p) u * u i + polynomialValue p u * (if j = i then (1 : ℝ) else 0) := by
      intro j
      rw [h3 j]
      by_cases hji : j = i
      · subst hji
        simp [polynomialValue, eval_add, eval_mul, eval_X, pderiv_X_self] <;> ring
      · have hne : j ≠ i := hji
        simp [polynomialValue, eval_add, eval_mul, eval_X, pderiv_X_of_ne hne.symm, hne] <;> ring
    have h_deriv_sum : (∑ j : Fin 2, v j * polynomialValue (pderiv j (p * X i)) u) =
        (u i) * (∑ j : Fin 2, v j * polynomialValue (pderiv j p) u) + v i * polynomialValue p u := by
      have h5 : ∑ j : Fin 2, v j * polynomialValue (pderiv j (p * X i)) u =
          ∑ j : Fin 2, v j * (polynomialValue (pderiv j p) u * u i +
            polynomialValue p u * (if j = i then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl; intro j _; rw [h4 j]
      rw [h5]
      have h61 : ∑ j : Fin 2, v j * (polynomialValue (pderiv j p) u * u i +
            polynomialValue p u * (if j = i then (1 : ℝ) else 0)) =
          ∑ j : Fin 2, (v j * (polynomialValue (pderiv j p) u * u i) +
            v j * (polynomialValue p u * (if j = i then (1 : ℝ) else 0))) := by
        apply Finset.sum_congr rfl; intro j _; ring
      rw [h61, Finset.sum_add_distrib]
      have h7 : ∑ j : Fin 2, v j * (polynomialValue (pderiv j p) u * u i) =
          (u i) * ∑ j : Fin 2, v j * polynomialValue (pderiv j p) u := by
        have h71 : ∑ j : Fin 2, v j * (polynomialValue (pderiv j p) u * u i) =
            ∑ j : Fin 2, (u i) * (v j * polynomialValue (pderiv j p) u) := by
          apply Finset.sum_congr rfl; intro j _; ring
        rw [h71, Finset.mul_sum]
      have h8 : ∑ j : Fin 2, v j * (polynomialValue p u * (if j = i then (1 : ℝ) else 0)) =
          v i * polynomialValue p u := by
        have h9 : ∀ j : Fin 2, v j * (polynomialValue p u * (if j = i then (1 : ℝ) else 0)) =
            if j = i then v i * polynomialValue p u else 0 := by
          intro j; by_cases hji : j = i
          · subst hji; simp
          · simp [hji]
        rw [Finset.sum_congr rfl (fun x _ => h9 x)]
        simp [Finset.sum_ite] <;> ring
      rw [h7, h8] <;> ring
    rw [h_deriv_sum]
    have h_id : HasDerivAt (fun t : ℝ => u i + t * v i) (v i) 0 := by
      have h : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id (0 : ℝ)
      simpa using h.smul_const (v i) |>.const_add (u i)
    have h_raw := hp.mul h_id
    have h_simp : (∑ j : Fin 2, v j * polynomialValue (pderiv j p) u) * (u i + (0 : ℝ) * v i) +
        polynomialValue p (u + (0 : ℝ) • v) * v i =
        (u i) * (∑ j : Fin 2, v j * polynomialValue (pderiv j p) u) + v i * polynomialValue p u := by
      simp [zero_smul] <;> ring
    exact h_raw.congr_deriv h_simp

/-- Derivative in the e₂ direction. -/
lemma deriv_polynomialValue_direction (h : MvPolynomial (Fin 2) ℝ) (u : P2) :
    HasDerivAt (fun t : ℝ => polynomialValue h (u + t • EuclideanSpace.single 1 1))
      (polynomialValue (pderiv 1 h) u) 0 := by
  let e2 : P2 := EuclideanSpace.single 1 1
  have h_gen := deriv_polynomialValue_direction_gen h u e2
  have h_sum : (∑ i : Fin 2, e2 i * polynomialValue (pderiv i h) u) =
      polynomialValue (pderiv 1 h) u := by
    simp [e2, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] <;> ring
  rw [h_sum] at h_gen
  exact h_gen

/-- Local dimension bound at a regular point of a plane curve. -/
lemma plane_curve_regular_local_dim (h : MvPolynomial (Fin 2) ℝ) {u : P2}
    (hu : polynomialValue h u = 0)
    (hy_ne : polynomialValue (pderiv 1 h) u ≠ 0) :
    ∃ (U : Set P2), IsOpen U ∧ u ∈ U ∧
      dimH ({p : P2 | polynomialValue h p = 0} ∩ U) ≤ 1 := by
  let v : ℝ × ℝ := p2Equiv u
  let F : (ℝ × ℝ) → ℝ := fun w => polynomialValue h (p2Equiv.symm w)
  have hF_contDiff : ContDiff ℝ ⊤ F :=
    (polynomial_contDiff2 h).comp p2Equiv.symm.contDiff
  have hF_diff : ContDiffAt ℝ ⊤ F v := hF_contDiff.contDiffAt
  let e2 : P2 := EuclideanSpace.single 1 1
  have hF_diff_at : DifferentiableAt ℝ F v := hF_diff.differentiableAt (by simp)
  have h7 : (fderiv ℝ F v) (0, 1) = polynomialValue (pderiv 1 h) u := by
    have h_line : lineDeriv ℝ F v (0, 1) = (fderiv ℝ F v) (0, 1) :=
      hF_diff_at.lineDeriv_eq_fderiv
    rw [← h_line]
    have h_eq1 : (fun t : ℝ => F (v + t • (0, 1))) =
        fun t : ℝ => polynomialValue h (u + t • e2) := by
      funext t
      have hlin : p2Equiv.symm (v + t • (0, 1)) = u + t • e2 := by
        have h : p2Equiv.symm (v + t • (0, 1)) =
            p2Equiv.symm v + t • p2Equiv.symm (0, 1) := by
          rw [p2Equiv.symm.map_add, p2Equiv.symm.map_smul]
        have h_u : p2Equiv.symm v = u := p2Equiv.left_inv u
        rw [h, h_u]
        have h3 : p2Equiv.symm (0, 1) = e2 := by
          simp [p2Equiv, e2] <;> ext i <;> fin_cases i <;> simp <;> rfl
        rw [h3]
      dsimp only [F]; rw [hlin]
    rw [lineDeriv, h_eq1]
    exact (deriv_polynomialValue_direction h u).deriv
  let c : ℝ := polynomialValue (pderiv 1 h) u
  have hc : c ≠ 0 := hy_ne
  have h_fu : F v = 0 := by simpa [F, v] using hu
  have hpart : (fderiv ℝ F v) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      c • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro (x : ℝ)
    have h1 : ((fderiv ℝ F v) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) x = (fderiv ℝ F v) (0, x) := by rfl
    have h2 : (c • ContinuousLinearMap.id ℝ ℝ) x = c * x := by
      simp [ContinuousLinearMap.id_apply] <;> ring
    rw [h1, h2]
    have h4 : (0, x) = (x • (0, 1) : ℝ × ℝ) := by
      congr <;> simp <;> ring
    have h5 : (fderiv ℝ F v) (0, x) = x * (fderiv ℝ F v) (0, 1) := by
      rw [h4]
      exact (fderiv ℝ F v).map_smul x (0, (1 : ℝ))
    rw [h5, h7] <;> ring
  let c_equiv : ℝ ≃L[ℝ] ℝ :=
    { toFun := fun x => c * x
      invFun := fun x => c⁻¹ * x
      left_inv := fun x => by field_simp [hc] <;> ring
      right_inv := fun x => by field_simp [hc] <;> ring
      map_add' := by intro x y; ring
      map_smul' := by intro r x; simp <;> ring
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  have h_clm_eq : (c • ContinuousLinearMap.id ℝ ℝ) = (c_equiv : ℝ →L[ℝ] ℝ) := by
    ext <;> simp [c_equiv] <;> ring
  have hinv : ((fderiv ℝ F v) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hpart, h_clm_eq]
    exact ContinuousLinearMap.isInvertible_equiv (f := c_equiv)
  let ψ : ℝ → ℝ := hF_diff.implicitFunction (by simp) hinv
  have hψ_diff : ContDiffAt ℝ ⊤ ψ v.1 :=
    hF_diff.contDiffAt_implicitFunction (by simp) hinv
  have h_eventually_raw : ∀ᶠ w in nhds v, F w = F v ↔ ψ w.1 = w.2 :=
    hF_diff.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  have h_eventually : ∀ᶠ w in nhds v, F w = 0 ↔ ψ w.1 = w.2 := by
    filter_upwards [h_eventually_raw] with w hw
    have h : F w = F v ↔ ψ w.1 = w.2 := hw
    rw [h_fu] at h
    exact h
  rcases h_eventually.exists_mem with ⟨N, hN_nhds, hN_prop⟩
  rcases _root_.mem_nhds_iff.mp hN_nhds with ⟨N_open, hN_sub, hN_open', hN_mem⟩
  have hψ_c1 : ContDiffAt ℝ 1 ψ v.1 := hψ_diff.of_le le_top
  rcases hψ_c1.hasStrictFDerivAt (by norm_num) |>.exists_lipschitzOnWith with ⟨C, W, hW_nhds, hW_lip⟩
  rcases _root_.mem_nhds_iff.mp hW_nhds with ⟨W_open, hW_sub, hW_open', hW_mem⟩
  let hW_lip_open : LipschitzOnWith C ψ W_open := hW_lip.mono hW_sub
  let N' : Set (ℝ × ℝ) := N_open ∩ (W_open ×ˢ Set.univ)
  have hN'_open : IsOpen N' := hN_open'.inter (hW_open'.prod isOpen_univ)
  have hN'_mem : v ∈ N' := ⟨hN_mem, ⟨hW_mem, trivial⟩⟩
  let U : Set P2 := p2Equiv.symm '' N'
  have hU_open : IsOpen U := p2Equiv.symm.isOpenMap N' hN'_open
  have hU_mem : u ∈ U := ⟨v, hN'_mem, p2Equiv.left_inv u⟩
  let g : ℝ → P2 := fun x => p2Equiv.symm (x, ψ x)
  let D : Set ℝ := {x ∈ W_open | (x, ψ x) ∈ N'}
  have hS_sub : {p : P2 | polynomialValue h p = 0} ∩ U ⊆ g '' D := by
    intro z hz
    rcases hz.2 with ⟨w, hwN', rfl⟩
    have h_Fw : F w = 0 := by simpa [F] using hz.1
    have h_iff : F w = 0 ↔ ψ w.1 = w.2 := hN_prop w (hN_sub hwN'.1)
    have h_eq : ψ w.1 = w.2 := h_iff.mp h_Fw
    have h_x_in_D : w.1 ∈ D := ⟨hwN'.2.1, by simpa [h_eq] using hwN'⟩
    refine ⟨w.1, h_x_in_D, ?_⟩
    have h_g : g w.1 = p2Equiv.symm w := by simp [g, h_eq] <;> rfl
    rw [h_g]
  have h_prod_lip : LipschitzOnWith (C + 1) (fun x : ℝ => (x, ψ x)) W_open := by
    have h : ∀ (x : ℝ), x ∈ W_open → ∀ (y : ℝ), y ∈ W_open →
        dist ((x, ψ x)) ((y, ψ y)) ≤ ((C + 1 : NNReal) : ℝ) * dist x y := by
      intro x hx y hy
      have h_ψ : dist (ψ x) (ψ y) ≤ (C : ℝ) * dist x y :=
        hW_lip_open.dist_le_mul x hx y hy
      have h_d : dist (x, ψ x) (y, ψ y) ≤ dist x y + dist (ψ x) (ψ y) := by
        rw [Prod.dist_eq]
        exact max_le_add_of_nonneg (by positivity) (by positivity)
      calc dist (x, ψ x) (y, ψ y)
        ≤ dist x y + dist (ψ x) (ψ y) := h_d
        _ ≤ dist x y + (C : ℝ) * dist x y := by gcongr
        _ = ((C + 1 : NNReal) : ℝ) * dist x y := by simp [add_mul] <;> ring
    have h' := LipschitzOnWith.of_dist_le' h
    have h_coe : (((C + 1 : NNReal) : ℝ).toNNReal) = C + 1 := by simp
    rw [h_coe] at h'
    exact h'
  let K : NNReal := ‖(p2Equiv.symm : (ℝ × ℝ) →L[ℝ] P2)‖₊
  have hg_lip : LipschitzOnWith (K * (C + 1)) g W_open := by
    have h : ∀ (x : ℝ), x ∈ W_open → ∀ (y : ℝ), y ∈ W_open →
        dist (g x) (g y) ≤ ((K * (C + 1) : NNReal) : ℝ) * dist x y := by
      intro x hx y hy
      have h2 : dist ((x, ψ x)) ((y, ψ y)) ≤ ((C + 1 : NNReal) : ℝ) * dist x y :=
        h_prod_lip.dist_le_mul x hx y hy
      have h1 : dist (g x) (g y) ≤ (K : ℝ) * dist ((x, ψ x)) ((y, ψ y)) :=
        p2Equiv.symm.lipschitz.dist_le_mul (x, ψ x) (y, ψ y)
      calc dist (g x) (g y)
        ≤ (K : ℝ) * dist ((x, ψ x)) ((y, ψ y)) := h1
        _ ≤ (K : ℝ) * (((C + 1 : NNReal) : ℝ) * dist x y) := by gcongr
        _ = ((K * (C + 1) : NNReal) : ℝ) * dist x y := by simp [mul_assoc] <;> ring
    have h' := LipschitzOnWith.of_dist_le' h
    have h_coe : (((K * (C + 1) : NNReal) : ℝ).toNNReal) = K * (C + 1) := by
      have h_gen : ∀ (n : NNReal), ((n : ℝ).toNNReal) = n := by intro n; simp
      exact h_gen (K * (C + 1))
    rw [h_coe] at h'
    exact h'
  have hD_sub : D ⊆ W_open := by simp [D]
  have hg_lip_D : LipschitzOnWith (K * (C + 1)) g D := hg_lip.mono hD_sub
  have h_dim_image : dimH (g '' D) ≤ dimH D := hg_lip_D.dimH_image_le
  have h_dim_D : dimH D ≤ 1 := by
    have h : dimH D ≤ dimH (Set.univ : Set ℝ) := dimH_mono (Set.subset_univ D)
    rw [Real.dimH_univ] at h
    exact h
  have h_main : dimH ({p : P2 | polynomialValue h p = 0} ∩ U) ≤ 1 := by
    calc dimH ({p : P2 | polynomialValue h p = 0} ∩ U) ≤ dimH (g '' D) := dimH_mono hS_sub
      _ ≤ dimH D := h_dim_image
      _ ≤ 1 := h_dim_D
  exact ⟨U, hU_open, hU_mem, h_main⟩

/-- If every point of a set has an open neighborhood with dimH ≤ d, then dimH ≤ d. -/
lemma dimH_of_locally_bound {s : Set P2} {d : ENNReal}
    (h : ∀ x ∈ s, ∃ (U : Set P2), IsOpen U ∧ x ∈ U ∧ dimH (s ∩ U) ≤ d) :
    dimH s ≤ d := by
  choose U hU_open hU_mem hU_dim using h
  let idx : Type _ := {x : P2 // x ∈ s}
  let U_idx : idx → Set P2 := fun i => U i.val i.property
  have hUo : ∀ (i : idx), IsOpen (U_idx i) := fun i => hU_open i.val i.property
  have hsU : s ⊆ ⋃ (i : idx), U_idx i := by
    intro z hz
    let i : idx := ⟨z, hz⟩
    exact Set.mem_iUnion.mpr ⟨i, hU_mem z hz⟩
  have h_is_lindelof : IsLindelof (s : Set P2) := by
    exact IsLindelof.of_coe
  rcases h_is_lindelof.elim_countable_subcover U_idx hUo hsU with ⟨r, hr_count, hr_cover⟩
  have h1 : ∀ (i : idx), i ∈ r → dimH (s ∩ U_idx i) ≤ d := by
    intro i _
    exact hU_dim i.val i.property
  have h5 : s ⊆ ⋃ i ∈ r, (s ∩ U_idx i) := by
    intro z hz
    rcases Set.mem_iUnion₂.mp (hr_cover hz) with ⟨i, hi, hzU⟩
    exact Set.mem_iUnion₂.mpr ⟨i, hi, ⟨hz, hzU⟩⟩
  have h6 : dimH (⋃ i ∈ r, (s ∩ U_idx i)) ≤ d := by
    rw [dimH_bUnion hr_count]
    exact iSup_le fun i => iSup_le fun hi => h1 i hi
  exact dimH_mono h5 |>.trans h6

/-- Plane curve dimension bound when pderiv 1 is nonzero. -/
lemma plane_curve_with_deriv {p : MvPolynomial (Fin 2) ℝ} (hp : p ≠ 0)
    (hderiv : pderiv 1 p ≠ 0)
    (h_ind : ∀ (q : MvPolynomial (Fin 2) ℝ), totalDegree q < totalDegree p → q ≠ 0 →
      dimH {x : P2 | polynomialValue q x = 0} ≤ 1) :
    dimH {x : P2 | polynomialValue p x = 0} ≤ 1 := by
  let S : Set P2 := {x | polynomialValue p x = 0}
  let S_reg : Set P2 := {x ∈ S | polynomialValue (pderiv 1 p) x ≠ 0}
  let S_sing : Set P2 := {x ∈ S | polynomialValue (pderiv 1 p) x = 0}
  have hS_decomp : S = S_reg ∪ S_sing := by
    ext x; simp [S, S_reg, S_sing] <;> tauto
  have h_sing_sub : S_sing ⊆ {x | polynomialValue (pderiv 1 p) x = 0} := by
    intro x hx; exact hx.2
  have h_deriv_lt : totalDegree (pderiv 1 p) < totalDegree p :=
    SingularSet.totalDegree_pderiv_lt hderiv
  have h_sing_dim : dimH S_sing ≤ 1 := by
    have h_ind' := h_ind (pderiv 1 p) h_deriv_lt hderiv
    exact dimH_mono h_sing_sub |>.trans h_ind'
  have h_local : ∀ (u : P2), u ∈ S_reg → ∃ (U : Set P2), IsOpen U ∧ u ∈ U ∧ dimH (S_reg ∩ U) ≤ 1 := by
    intro u hu
    rcases plane_curve_regular_local_dim p hu.1 hu.2 with ⟨U, hU_open, hU_mem, hU_dim⟩
    refine ⟨U, hU_open, hU_mem, ?_⟩
    have h_sub : S_reg ∩ U ⊆ S ∩ U := by
      intro z hz; exact ⟨hz.1.1, hz.2⟩
    exact dimH_mono h_sub |>.trans hU_dim
  have h_reg_dim : dimH S_reg ≤ 1 :=
    dimH_of_locally_bound h_local
  have h_goal : dimH S ≤ 1 := by
    rw [hS_decomp, dimH_union]
    exact max_le h_reg_dim h_sing_dim
  simpa [S] using h_goal

/-- A nonzero polynomial in two variables has zero set of Hausdorff dimension ≤ 1. -/
theorem plane_curve_dimH_le_one {h : MvPolynomial (Fin 2) ℝ} (hh : h ≠ 0) :
    dimH {p : P2 | polynomialValue h p = 0} ≤ 1 := by
  classical
  let P : ℕ → Prop := fun n => ∀ (p : MvPolynomial (Fin 2) ℝ), totalDegree p = n → p ≠ 0 →
    dimH {x : P2 | polynomialValue p x = 0} ≤ 1
  have h_main : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hdeg hp
      let S : Set P2 := {x | polynomialValue p x = 0}
      by_cases h_const : totalDegree p = 0
      · have hc : p = C (coeff 0 p) := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h_const
        have hcoeff : coeff 0 p ≠ 0 := by
          intro hz
          have h' : p = 0 := by rw [hc, hz] <;> simp
          exact hp h'
        have h_eval : ∀ x : P2, polynomialValue p x = coeff 0 p := by
          intro x; rw [hc]; simp [polynomialValue]
        have hS : S = ∅ := by
          ext x
          simp only [S, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro h
          have h9 : polynomialValue p x = coeff 0 p := h_eval x
          rw [h9] at h
          exact hcoeff h
        simpa [S] using by
          have h_goal : dimH S ≤ 1 := by
            rw [hS] <;> simp
          exact h_goal
      · have hpos : 0 < totalDegree p := by omega
        have h_vars : p.vars.Nonempty := by
          by_contra h2
          have h3 : p.vars = ∅ := by simpa using h2
          have h4 : p.support ⊆ {0} := by
            intro m hm
            have h5 : m.support ⊆ p.vars := by
              exact support_subset_vars_of_mem_support hm
            rw [h3] at h5
            have h6 : m.support = ∅ := by simpa using h5
            have h7 : m = 0 := Finsupp.support_eq_empty.mp h6
            simpa using h7
          have h8 : totalDegree p = 0 := by
            rw [MvPolynomial.totalDegree_eq]
            have h9 : Finset.sup p.support (fun m : Fin 2 →₀ ℕ => (Finsupp.toMultiset m).card) = 0 := by
              apply Finset.sup_eq_zero.mpr
              intro m hm
              have h10 : m = 0 := by
                have h11 : m ∈ ({0} : Finset (Fin 2 →₀ ℕ)) := h4 hm
                simpa using h11
              rw [h10]; simp
            rw [h9]
          exact h_const h8
        rcases h_vars with ⟨i, hi⟩
        have h6 : pderiv i p ≠ 0 := SingularSet.pderiv_ne_zero_of_mem_vars hi
        by_cases h_i1 : i = 1
        · subst h_i1
          exact plane_curve_with_deriv hp h6 (fun q hqlt hq => ih (totalDegree q) (by rwa [hdeg] at hqlt) q rfl hq)
        · have h_i0 : i = 0 := by fin_cases i <;> tauto
          subst h_i0
          let e : Fin 2 ≃ Fin 2 :=
            { toFun := fun j => if j = 0 then (1 : Fin 2) else (0 : Fin 2)
              invFun := fun j => if j = 0 then (1 : Fin 2) else (0 : Fin 2)
              left_inv := by intro j; fin_cases j <;> simp <;> tauto
              right_inv := by intro j; fin_cases j <;> simp <;> tauto }
          let p' := rename e p
          have h_comp : e.symm ∘ e = id := by
            funext j; fin_cases j <;> simp [e] <;> tauto
          have h1 : ∀ (q : MvPolynomial (Fin 2) ℝ), rename e.symm (rename e q) = q := by
            intro q
            rw [rename_rename, h_comp]
            have h_rid : rename id q = q := by
              rw [MvPolynomial.rename_id]
              <;> rfl
            exact h_rid
          have hp' : p' ≠ 0 := by
            intro hz
            have h2 : rename e.symm p' = p := by
              simpa [p'] using h1 p
            rw [hz] at h2
            simp at h2
            exact hp h2.symm
          have h_deriv : pderiv 1 p' ≠ 0 := by
            have h_eq : pderiv 1 p' = rename e (pderiv 0 p) := by
              have h9 : pderiv (e 0) (rename e p) = rename e (pderiv 0 p) :=
                pderiv_rename e.injective 0 p
              have h10 : e 0 = 1 := by simp [e]
              simpa [p', h10] using h9
            rw [h_eq]
            intro hz
            have h_contra : rename e.symm (rename e (pderiv 0 p)) = 0 := by
              rw [hz] <;> simp
            have h_eq2 : rename e.symm (rename e (pderiv 0 p)) = pderiv 0 p := h1 (pderiv 0 p)
            rw [h_eq2] at h_contra
            exact h6 h_contra
          have h_deg : totalDegree p' = totalDegree p := by
            simpa [p', MvPolynomial.renameEquiv] using MvPolynomial.totalDegree_renameEquiv e p
          let euc : P2 ≃L[ℝ] (Fin 2 → ℝ) := EuclideanSpace.equiv (Fin 2) ℝ
          let perm : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
            { toFun := fun f => f ∘ e
              invFun := fun f => f ∘ e.symm
              left_inv := by intro f; funext i; simp
              right_inv := by intro f; funext i; simp
              map_add' := by intro f g; funext i; simp
              map_smul' := by intro c f; funext i; simp [smul_eq_mul]
              continuous_toFun := continuous_pi fun i => continuous_apply (e i)
              continuous_invFun := continuous_pi fun i => continuous_apply (e.symm i) }
          let L : P2 ≃L[ℝ] P2 := euc.trans perm |>.trans euc.symm
          let K_L : NNReal := ‖(L : P2 →L[ℝ] P2)‖₊
          have hL_lip : LipschitzWith K_L L := L.lipschitz
          have h_eval1 : ∀ (x : P2), polynomialValue p' x = polynomialValue p (L x) := by
            intro x
            have hL_eval : euc (L x) = (euc x) ∘ e := by
              simp [L, perm] <;> rfl
            have h1 : polynomialValue p' x = MvPolynomial.eval (euc x) p' := by rfl
            have h2 : polynomialValue p (L x) = MvPolynomial.eval (euc (L x)) p := by rfl
            rw [h1, h2, hL_eval]
            have h3 : MvPolynomial.eval ((euc x) ∘ e) p = MvPolynomial.eval (euc x) (rename e p) := by
              rw [MvPolynomial.eval_rename] <;> rfl
            rw [h3] <;> rfl
          have h_eval2 : ∀ (z : P2), polynomialValue p' (L.symm z) = polynomialValue p z := by
            intro z
            have h : polynomialValue p' (L.symm z) = polynomialValue p (L (L.symm z)) := h_eval1 (L.symm z)
            rw [h]
            have h2 : L (L.symm z) = z := ContinuousLinearEquiv.apply_symm_apply L z
            rw [h2]
          have h_zero_set : L '' {x | polynomialValue p' x = 0} = S := by
            ext z
            simp only [Set.mem_image, S]
            constructor
            · rintro ⟨x, hx, rfl⟩
              have h9 : polynomialValue p (L x) = 0 := by
                rw [← h_eval1 x]; exact hx
              exact h9
            · intro hz
              refine ⟨L.symm z, ?_, ?_⟩
              · have hz' : polynomialValue p z = 0 := by simpa [S] using hz
                have h11 : polynomialValue p' (L.symm z) = 0 := by
                  rw [h_eval2 z, hz']
                simpa using h11
              · exact L.right_inv z
          have h_result : dimH {x | polynomialValue p' x = 0} ≤ 1 :=
            plane_curve_with_deriv hp' h_deriv (fun q hqlt hq =>
              have hqlt' : totalDegree q < n := by
                calc totalDegree q < totalDegree p' := hqlt
                  _ = totalDegree p := h_deg
                  _ = n := hdeg
              ih (totalDegree q) hqlt' q rfl hq)
          have h_transfer : dimH S ≤ dimH {x | polynomialValue p' x = 0} := by
            have h : S = L '' {x | polynomialValue p' x = 0} := h_zero_set.symm
            rw [h]
            exact hL_lip.dimH_image_le _
          exact h_transfer.trans h_result
  exact h_main (totalDegree h) h rfl hh

end Kakeya.CV
