import MyLeanRepo.Kakeya.Cinematic.Geometry
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Centered Taylor extension for C2 functions

Horizontally translate a short interval to the center of `[0,1]` and extend
outside the copied interval by quadratic Taylor polynomials at the endpoints.
-/

noncomputable section

namespace Kakeya.Cinematic

open C2Function

def taylorShift (I : ParameterInterval) : ℝ := 1 / 2 - I.midpoint

def taylorLeft (I : ParameterInterval) : ℝ := I.left + taylorShift I

def taylorRight (I : ParameterInterval) : ℝ := I.right + taylorShift I

lemma taylorLeft_eq (I : ParameterInterval) :
    taylorLeft I = 1 / 2 - I.length / 2 := by
  simp [taylorLeft, taylorShift, ParameterInterval.midpoint,
    ParameterInterval.length] <;> ring

lemma taylorRight_eq (I : ParameterInterval) :
    taylorRight I = 1 / 2 + I.length / 2 := by
  simp [taylorRight, taylorShift, ParameterInterval.midpoint,
    ParameterInterval.length] <;> ring

lemma taylorLeft_lt_taylorRight (I : ParameterInterval)
    (h_len : 0 < I.length) :
    taylorLeft I < taylorRight I := by
  rw [taylorLeft_eq, taylorRight_eq]
  linarith

lemma piecewise2_contDiff2 {f g : ℝ → ℝ} {a : ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (h_val : f a = g a) (h_deriv : deriv f a = deriv g a)
    (h_second : deriv (deriv f) a = deriv (deriv g) a) :
    ContDiff ℝ 2 (Set.piecewise (Set.Iic a) f g) := by
  classical
  let h : ℝ → ℝ := Set.piecewise (Set.Iic a) f g
  let h' : ℝ → ℝ := Set.piecewise (Set.Iic a) (deriv f) (deriv g)
  let h'' : ℝ → ℝ :=
    Set.piecewise (Set.Iic a) (deriv (deriv f)) (deriv (deriv g))
  have hf_diff : Differentiable ℝ f :=
    hf.differentiable (by norm_num)
  have hg_diff : Differentiable ℝ g :=
    hg.differentiable (by norm_num)
  have hf'_diff : Differentiable ℝ (deriv f) :=
    hf.differentiable_deriv_two
  have hg'_diff : Differentiable ℝ (deriv g) :=
    hg.differentiable_deriv_two
  have h_cont_f : Continuous f := hf.continuous
  have h_cont_g : Continuous g := hg.continuous
  have h_cont_f' : Continuous (deriv f) :=
    hf.continuous_deriv (by norm_num)
  have h_cont_g' : Continuous (deriv g) :=
    hg.continuous_deriv (by norm_num)
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hg1 : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have h_cont_f'' : Continuous (deriv (deriv f)) :=
    hf1.continuous_deriv (by norm_num)
  have h_cont_g'' : Continuous (deriv (deriv g)) :=
    hg1.continuous_deriv (by norm_num)
  have h_cont_h : Continuous h :=
    Continuous.piecewise (fun x hx => by
      have h_x : x = a := by simpa [frontier_Iic] using hx
      rw [h_x]
      exact h_val) h_cont_f h_cont_g
  have h_cont_h' : Continuous h' :=
    Continuous.piecewise (fun x hx => by
      have h_x : x = a := by simpa [frontier_Iic] using hx
      rw [h_x]
      exact h_deriv) h_cont_f' h_cont_g'
  have h_cont_h'' : Continuous h'' :=
    Continuous.piecewise (fun x hx => by
      have h_x : x = a := by simpa [frontier_Iic] using hx
      rw [h_x]
      exact h_second) h_cont_f'' h_cont_g''
  have hw_left : ∀ z : ℝ, z ≤ a → h z = f z := by
    intro z hz
    exact Set.piecewise_eq_of_mem (Set.Iic a) f g hz
  have hw_left' : ∀ z : ℝ, z ≤ a → h' z = deriv f z := by
    intro z hz
    exact Set.piecewise_eq_of_mem (Set.Iic a) (deriv f) (deriv g) hz
  have hw_left'' : ∀ z : ℝ, z ≤ a → h'' z = deriv (deriv f) z := by
    intro z hz
    exact Set.piecewise_eq_of_mem
      (Set.Iic a) (deriv (deriv f)) (deriv (deriv g)) hz
  have hw_right : ∀ z : ℝ, ¬z ≤ a → h z = g z := by
    intro z hz
    exact Set.piecewise_eq_of_notMem (Set.Iic a) f g hz
  have hw_right' : ∀ z : ℝ, ¬z ≤ a → h' z = deriv g z := by
    intro z hz
    exact Set.piecewise_eq_of_notMem (Set.Iic a) (deriv f) (deriv g) hz
  have hw_right'' : ∀ z : ℝ, ¬z ≤ a → h'' z = deriv (deriv g) z := by
    intro z hz
    exact Set.piecewise_eq_of_notMem
      (Set.Iic a) (deriv (deriv f)) (deriv (deriv g)) hz
  have h_hasDeriv : ∀ x : ℝ, HasDerivAt h (h' x) x := by
    intro x
    by_cases h_x : x < a
    · have h_ev : h =ᶠ[nhds x] f := by
        filter_upwards [Iio_mem_nhds h_x] with z hz
        exact hw_left z hz.le
      have h_ev' : h' =ᶠ[nhds x] deriv f := by
        filter_upwards [Iio_mem_nhds h_x] with z hz
        exact hw_left' z hz.le
      have h_d : HasDerivAt f (deriv f x) x :=
        (hf_diff x).hasDerivAt
      have h_r : HasDerivAt h (deriv f x) x :=
        h_d.congr_of_eventuallyEq h_ev
      rw [h_ev'.eq_of_nhds]
      exact h_r
    · by_cases h_x2 : x = a
      · have h_left :
            HasDerivWithinAt h (h' a) (Set.Iic a) a := by
          have h_d :
              HasDerivWithinAt f (deriv f a) (Set.Iic a) a :=
            (hf_diff a).hasDerivAt.hasDerivWithinAt
          have h_ev : h =ᶠ[nhdsWithin a (Set.Iic a)] f := by
            filter_upwards [self_mem_nhdsWithin] with z hz
            exact hw_left z hz
          have h_h' : h' a = deriv f a := hw_left' a (by simp)
          rw [h_h']
          exact h_d.congr_of_eventuallyEq_of_mem h_ev (by simp)
        have h_right_ev : h =ᶠ[nhdsWithin a (Set.Ici a)] g := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          by_cases h_eq2 : z = a
          · rw [h_eq2, hw_left a (by simp), h_val]
          · have h_gt : a < z :=
              lt_of_le_of_ne hz (Ne.symm h_eq2)
            exact hw_right z (not_le.mpr h_gt)
        have h_d :
            HasDerivWithinAt g (deriv g a) (Set.Ici a) a :=
          (hg_diff a).hasDerivAt.hasDerivWithinAt
        have h_h' : h' a = deriv g a := by
          rw [hw_left' a (by simp)]
          exact h_deriv
        have h_right :
            HasDerivWithinAt h (h' a) (Set.Ici a) a := by
          rw [h_h']
          exact h_d.congr_of_eventuallyEq_of_mem h_right_ev (by simp)
        have h_union :
            HasDerivWithinAt h (h' a) (Set.Iic a ∪ Set.Ici a) a :=
          h_left.union h_right
        have h_univ : Set.Iic a ∪ Set.Ici a = Set.univ := by
          ext y
          simp
        rw [h_univ] at h_union
        have h_final : HasDerivAt h (h' a) a :=
          hasDerivWithinAt_univ.mp h_union
        rw [h_x2]
        exact h_final
      · have h_gt : a < x :=
          lt_of_le_of_ne (le_of_not_gt h_x) (Ne.symm h_x2)
        have h_ev : h =ᶠ[nhds x] g := by
          filter_upwards [Ioi_mem_nhds h_gt] with z hz
          exact hw_right z (not_le.mpr hz)
        have h_ev' : h' =ᶠ[nhds x] deriv g := by
          filter_upwards [Ioi_mem_nhds h_gt] with z hz
          exact hw_right' z (not_le.mpr hz)
        have h_d : HasDerivAt g (deriv g x) x :=
          (hg_diff x).hasDerivAt
        have h_r : HasDerivAt h (deriv g x) x :=
          h_d.congr_of_eventuallyEq h_ev
        rw [h_ev'.eq_of_nhds]
        exact h_r
  have h_hasDeriv' : ∀ x : ℝ, HasDerivAt h' (h'' x) x := by
    intro x
    by_cases h_x : x < a
    · have h_ev : h' =ᶠ[nhds x] deriv f := by
        filter_upwards [Iio_mem_nhds h_x] with z hz
        exact hw_left' z hz.le
      have h_ev' : h'' =ᶠ[nhds x] deriv (deriv f) := by
        filter_upwards [Iio_mem_nhds h_x] with z hz
        exact hw_left'' z hz.le
      have h_d : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
        (hf'_diff x).hasDerivAt
      have h_r : HasDerivAt h' (deriv (deriv f) x) x :=
        h_d.congr_of_eventuallyEq h_ev
      rw [h_ev'.eq_of_nhds]
      exact h_r
    · by_cases h_x2 : x = a
      · have h_left :
            HasDerivWithinAt h' (h'' a) (Set.Iic a) a := by
          have h_d :
              HasDerivWithinAt (deriv f) (deriv (deriv f) a)
                (Set.Iic a) a :=
            (hf'_diff a).hasDerivAt.hasDerivWithinAt
          have h_ev :
              h' =ᶠ[nhdsWithin a (Set.Iic a)] deriv f := by
            filter_upwards [self_mem_nhdsWithin] with z hz
            exact hw_left' z hz
          have h_h'' : h'' a = deriv (deriv f) a :=
            hw_left'' a (by simp)
          rw [h_h'']
          exact h_d.congr_of_eventuallyEq_of_mem h_ev (by simp)
        have h_right_ev :
            h' =ᶠ[nhdsWithin a (Set.Ici a)] deriv g := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          by_cases h_eq2 : z = a
          · rw [h_eq2, hw_left' a (by simp), h_deriv]
          · have h_gt : a < z :=
              lt_of_le_of_ne hz (Ne.symm h_eq2)
            exact hw_right' z (not_le.mpr h_gt)
        have h_d :
            HasDerivWithinAt (deriv g) (deriv (deriv g) a)
              (Set.Ici a) a :=
          (hg'_diff a).hasDerivAt.hasDerivWithinAt
        have h_h'' : h'' a = deriv (deriv g) a := by
          rw [hw_left'' a (by simp)]
          exact h_second
        have h_right :
            HasDerivWithinAt h' (h'' a) (Set.Ici a) a := by
          rw [h_h'']
          exact h_d.congr_of_eventuallyEq_of_mem h_right_ev (by simp)
        have h_union :
            HasDerivWithinAt h' (h'' a) (Set.Iic a ∪ Set.Ici a) a :=
          h_left.union h_right
        have h_univ : Set.Iic a ∪ Set.Ici a = Set.univ := by
          ext y
          simp
        rw [h_univ] at h_union
        have h_final : HasDerivAt h' (h'' a) a :=
          hasDerivWithinAt_univ.mp h_union
        rw [h_x2]
        exact h_final
      · have h_gt : a < x :=
          lt_of_le_of_ne (le_of_not_gt h_x) (Ne.symm h_x2)
        have h_ev : h' =ᶠ[nhds x] deriv g := by
          filter_upwards [Ioi_mem_nhds h_gt] with z hz
          exact hw_right' z (not_le.mpr hz)
        have h_ev' : h'' =ᶠ[nhds x] deriv (deriv g) := by
          filter_upwards [Ioi_mem_nhds h_gt] with z hz
          exact hw_right'' z (not_le.mpr hz)
        have h_d :
            HasDerivAt (deriv g) (deriv (deriv g) x) x :=
          (hg'_diff x).hasDerivAt
        have h_r : HasDerivAt h' (deriv (deriv g) x) x :=
          h_d.congr_of_eventuallyEq h_ev
        rw [h_ev'.eq_of_nhds]
        exact h_r
  have h_diff_h : Differentiable ℝ h :=
    fun x => (h_hasDeriv x).differentiableAt
  have h_deriv_eq : deriv h = h' := by
    funext x
    exact (h_hasDeriv x).deriv
  have h_diff_h' : Differentiable ℝ h' :=
    fun x => (h_hasDeriv' x).differentiableAt
  have h_deriv'_eq : deriv h' = h'' := by
    funext x
    exact (h_hasDeriv' x).deriv
  have h_contDiff1_h' : ContDiff ℝ 1 h' := by
    rw [contDiff_one_iff_deriv]
    exact ⟨h_diff_h', by rw [h_deriv'_eq]; exact h_cont_h''⟩
  have h_main : ContDiff ℝ 2 h := by
    have h2 : ContDiff ℝ (1 + 1) h := by
      rw [contDiff_succ_iff_deriv]
      exact ⟨h_diff_h, by
        constructor
        · simp
        · rw [h_deriv_eq]
          exact h_contDiff1_h'⟩
    convert h2 using 3 <;> norm_num
  exact h_main

def taylorLeftPoly (f : C2Function) (I : ParameterInterval) : ℝ → ℝ :=
  fun y =>
    f.extension I.left +
      deriv f.extension I.left * (y - taylorLeft I) +
      (deriv (deriv f.extension) I.left / 2) *
        (y - taylorLeft I) ^ 2

def taylorMidFunc (f : C2Function) (I : ParameterInterval) : ℝ → ℝ :=
  fun y => f.extension (y - taylorShift I)

def taylorRightPoly (f : C2Function) (I : ParameterInterval) : ℝ → ℝ :=
  fun y =>
    f.extension I.right +
      deriv f.extension I.right * (y - taylorRight I) +
      (deriv (deriv f.extension) I.right / 2) *
        (y - taylorRight I) ^ 2

def taylorExtensionFun (f : C2Function) (I : ParameterInterval) : ℝ → ℝ :=
  let leftMid :=
    Set.piecewise (Set.Iic (taylorLeft I))
      (taylorLeftPoly f I) (taylorMidFunc f I)
  Set.piecewise (Set.Iic (taylorRight I)) leftMid (taylorRightPoly f I)

def taylorLeftPoly' (f : C2Function) (I : ParameterInterval) : ℝ → ℝ :=
  fun y =>
    deriv f.extension I.left +
      deriv (deriv f.extension) I.left * (y - taylorLeft I)

def taylorMidFunc' (f : C2Function) (I : ParameterInterval) : ℝ → ℝ :=
  fun y => deriv f.extension (y - taylorShift I)

def taylorRightPoly' (f : C2Function) (I : ParameterInterval) : ℝ → ℝ :=
  fun y =>
    deriv f.extension I.right +
      deriv (deriv f.extension) I.right * (y - taylorRight I)

def taylorExtensionFun' (f : C2Function) (I : ParameterInterval) : ℝ → ℝ :=
  let leftMid :=
    Set.piecewise (Set.Iic (taylorLeft I))
      (taylorLeftPoly' f I) (taylorMidFunc' f I)
  Set.piecewise (Set.Iic (taylorRight I)) leftMid (taylorRightPoly' f I)

def taylorExtensionFun'' (f : C2Function) (I : ParameterInterval) : ℝ → ℝ :=
  let f'' := deriv (deriv f.extension)
  let leftMid :=
    Set.piecewise (Set.Iic (taylorLeft I))
      (fun _ => f'' I.left)
      (fun y => f'' (y - taylorShift I))
  Set.piecewise (Set.Iic (taylorRight I)) leftMid
    (fun _ => f'' I.right)

lemma taylor_poly_deriv (a b c y0 : ℝ) :
    deriv (fun y : ℝ =>
      a + b * (y - y0) + c * (y - y0) ^ 2) =
      fun y : ℝ => b + 2 * c * (y - y0) := by
  funext y
  have h_id : HasDerivAt (fun y : ℝ => y - y0) 1 y :=
    (hasDerivAt_id y).sub_const y0
  have h_b : HasDerivAt (fun y : ℝ => b * (y - y0)) b y := by
    have h :
        HasDerivAt (fun y : ℝ => b * (y - y0)) (b * (1 : ℝ)) y :=
      h_id.const_mul b
    have h_eq : b * (1 : ℝ) = b := by ring
    rw [h_eq] at h
    exact h
  have h_sq : HasDerivAt (fun y : ℝ => (y - y0) ^ 2)
      (2 * (y - y0)) y := by
    have h : HasDerivAt
        (fun y : ℝ => (y - y0) * (y - y0))
        (1 * (y - y0) + (y - y0) * 1) y :=
      h_id.mul h_id
    have h_eq :
        1 * (y - y0) + (y - y0) * 1 = 2 * (y - y0) := by
      ring
    rw [h_eq] at h
    simpa [pow_two] using h
  have h_c : HasDerivAt (fun y : ℝ => c * (y - y0) ^ 2)
      (2 * c * (y - y0)) y := by
    have h : HasDerivAt (fun y : ℝ => c * (y - y0) ^ 2)
        (c * (2 * (y - y0))) y :=
      h_sq.const_mul c
    have h_eq : c * (2 * (y - y0)) = 2 * c * (y - y0) := by
      ring
    rw [h_eq] at h
    exact h
  have h_a : HasDerivAt (fun _ : ℝ => a) 0 y :=
    hasDerivAt_const y a
  have h_sum : HasDerivAt
      (fun y : ℝ => a + b * (y - y0) + c * (y - y0) ^ 2)
      ((0 : ℝ) + b + 2 * c * (y - y0)) y :=
    (h_a.add h_b).add h_c
  have h_eq :
      (0 : ℝ) + b + 2 * c * (y - y0) = b + 2 * c * (y - y0) := by
    ring
  rw [h_eq] at h_sum
  exact h_sum.deriv

lemma deriv_leftPoly (f : C2Function) (I : ParameterInterval) :
    deriv (taylorLeftPoly f I) = taylorLeftPoly' f I := by
  funext y
  rw [show taylorLeftPoly f I = fun z : ℝ =>
      f.extension I.left +
        deriv f.extension I.left * (z - taylorLeft I) +
        (deriv (deriv f.extension) I.left / 2) *
          (z - taylorLeft I) ^ 2 by rfl]
  rw [congrFun (taylor_poly_deriv
    (f.extension I.left) (deriv f.extension I.left)
    (deriv (deriv f.extension) I.left / 2) (taylorLeft I)) y]
  simp only [taylorLeftPoly']
  ring

lemma deriv2_leftPoly (f : C2Function) (I : ParameterInterval) (y : ℝ) :
    deriv (deriv (taylorLeftPoly f I)) y =
      deriv (deriv f.extension) I.left := by
  rw [deriv_leftPoly]
  have h_id : HasDerivAt (fun z : ℝ => z - taylorLeft I) 1 y :=
    (hasDerivAt_id y).sub_const (taylorLeft I)
  have h_const : HasDerivAt
      (fun _ : ℝ => deriv (deriv f.extension) I.left) 0 y :=
    hasDerivAt_const y _
  have h_b : HasDerivAt
      (fun z : ℝ =>
        deriv (deriv f.extension) I.left * (z - taylorLeft I))
      (deriv (deriv f.extension) I.left) y := by
    have h : HasDerivAt
        (fun z : ℝ =>
          deriv (deriv f.extension) I.left * (z - taylorLeft I))
        (0 * (y - taylorLeft I) +
          deriv (deriv f.extension) I.left * 1) y :=
      h_const.mul h_id
    have h_eq :
        0 * (y - taylorLeft I) +
            deriv (deriv f.extension) I.left * 1 =
          deriv (deriv f.extension) I.left := by
      ring
    rw [h_eq] at h
    exact h
  have h_a : HasDerivAt
      (fun _ : ℝ => deriv f.extension I.left) 0 y :=
    hasDerivAt_const y _
  have h_sum : HasDerivAt
      (fun z : ℝ =>
        deriv f.extension I.left +
          deriv (deriv f.extension) I.left * (z - taylorLeft I))
      ((0 : ℝ) + deriv (deriv f.extension) I.left) y :=
    h_a.add h_b
  have h_eq :
      (0 : ℝ) + deriv (deriv f.extension) I.left =
        deriv (deriv f.extension) I.left := by
    ring
  rw [h_eq] at h_sum
  exact h_sum.deriv

lemma deriv_midFunc (f : C2Function) (I : ParameterInterval) :
    deriv (taylorMidFunc f I) = taylorMidFunc' f I := by
  funext y
  have h_inner : HasDerivAt (fun x : ℝ => x - taylorShift I) 1 y :=
    (hasDerivAt_id y).sub_const (taylorShift I)
  have h_outer :
      HasDerivAt f.extension
        (deriv f.extension (y - taylorShift I))
        (y - taylorShift I) :=
    (f.extension_contDiff.differentiable (by norm_num)
      (y - taylorShift I)).hasDerivAt
  have h_comp :
      HasDerivAt
        (f.extension ∘ fun x : ℝ => x - taylorShift I)
        (deriv f.extension (y - taylorShift I) * 1) y :=
    h_outer.comp y h_inner
  have h_eq :
      deriv f.extension (y - taylorShift I) * 1 =
        deriv f.extension (y - taylorShift I) := by
    ring
  rw [h_eq] at h_comp
  have h_final :
      HasDerivAt (taylorMidFunc f I)
        (deriv f.extension (y - taylorShift I)) y := by
    convert h_comp using 1 <;> funext z <;> rfl
  exact h_final.deriv

lemma deriv2_midFunc (f : C2Function) (I : ParameterInterval) (y : ℝ) :
    deriv (deriv (taylorMidFunc f I)) y =
      deriv (deriv f.extension) (y - taylorShift I) := by
  rw [deriv_midFunc]
  have h_inner : HasDerivAt (fun x : ℝ => x - taylorShift I) 1 y :=
    (hasDerivAt_id y).sub_const (taylorShift I)
  have h_outer :
      HasDerivAt (deriv f.extension)
        (deriv (deriv f.extension) (y - taylorShift I))
        (y - taylorShift I) :=
    (f.extension_contDiff.differentiable_deriv_two
      (y - taylorShift I)).hasDerivAt
  have h_comp :
      HasDerivAt
        ((deriv f.extension) ∘ fun x : ℝ => x - taylorShift I)
        (deriv (deriv f.extension) (y - taylorShift I) * 1) y :=
    h_outer.comp y h_inner
  have h_eq :
      deriv (deriv f.extension) (y - taylorShift I) * 1 =
        deriv (deriv f.extension) (y - taylorShift I) := by
    ring
  rw [h_eq] at h_comp
  have h_final :
      HasDerivAt (taylorMidFunc' f I)
        (deriv (deriv f.extension) (y - taylorShift I)) y := by
    convert h_comp using 1 <;> funext z <;> rfl
  exact h_final.deriv

lemma deriv_rightPoly (f : C2Function) (I : ParameterInterval) :
    deriv (taylorRightPoly f I) = taylorRightPoly' f I := by
  funext y
  rw [show taylorRightPoly f I = fun z : ℝ =>
      f.extension I.right +
        deriv f.extension I.right * (z - taylorRight I) +
        (deriv (deriv f.extension) I.right / 2) *
          (z - taylorRight I) ^ 2 by rfl]
  rw [congrFun (taylor_poly_deriv
    (f.extension I.right) (deriv f.extension I.right)
    (deriv (deriv f.extension) I.right / 2) (taylorRight I)) y]
  simp only [taylorRightPoly']
  ring

lemma deriv2_rightPoly (f : C2Function) (I : ParameterInterval) (y : ℝ) :
    deriv (deriv (taylorRightPoly f I)) y =
      deriv (deriv f.extension) I.right := by
  rw [deriv_rightPoly]
  have h_id : HasDerivAt (fun z : ℝ => z - taylorRight I) 1 y :=
    (hasDerivAt_id y).sub_const (taylorRight I)
  have h_const : HasDerivAt
      (fun _ : ℝ => deriv (deriv f.extension) I.right) 0 y :=
    hasDerivAt_const y _
  have h_b : HasDerivAt
      (fun z : ℝ =>
        deriv (deriv f.extension) I.right * (z - taylorRight I))
      (deriv (deriv f.extension) I.right) y := by
    have h : HasDerivAt
        (fun z : ℝ =>
          deriv (deriv f.extension) I.right * (z - taylorRight I))
        (0 * (y - taylorRight I) +
          deriv (deriv f.extension) I.right * 1) y :=
      h_const.mul h_id
    have h_eq :
        0 * (y - taylorRight I) +
            deriv (deriv f.extension) I.right * 1 =
          deriv (deriv f.extension) I.right := by
      ring
    rw [h_eq] at h
    exact h
  have h_a : HasDerivAt
      (fun _ : ℝ => deriv f.extension I.right) 0 y :=
    hasDerivAt_const y _
  have h_sum : HasDerivAt
      (fun z : ℝ =>
        deriv f.extension I.right +
          deriv (deriv f.extension) I.right * (z - taylorRight I))
      ((0 : ℝ) + deriv (deriv f.extension) I.right) y :=
    h_a.add h_b
  have h_eq :
      (0 : ℝ) + deriv (deriv f.extension) I.right =
        deriv (deriv f.extension) I.right := by
    ring
  rw [h_eq] at h_sum
  exact h_sum.deriv

end Kakeya.Cinematic
