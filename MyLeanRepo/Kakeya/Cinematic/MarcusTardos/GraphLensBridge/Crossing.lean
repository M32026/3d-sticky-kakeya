import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.GraphLensBridge.Definitions
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Topology.Order.IntermediateValue

/-!
# Crossing signs of graph lenses

A proper intersection is a sign-changing zero.  Since the two endpoints of a
graph lens already exhaust the allowed intersections of its two curves, its
upper side lies strictly above its lower side on the lens interval and
strictly below it outside that interval.
-/

noncomputable section

namespace Kakeya.Cinematic.GraphLensBridge

open Kakeya.Cinematic Set
open scoped Topology

theorem upper_mem_curves {curves : Finset C2Function} {lens : GraphLens}
    (hsides : lens.f ∈ curves ∧ lens.g ∈ curves) :
    upper lens ∈ curves := by
  rcases upper_eq_f_or_g lens with h | h <;> simp [h, hsides]

theorem lower_mem_curves {curves : Finset C2Function} {lens : GraphLens}
    (hsides : lens.f ∈ curves ∧ lens.g ∈ curves) :
    lower lens ∈ curves := by
  rcases lower_eq_f_or_g lens with h | h <;> simp [h, hsides]

theorem upper_ne_lower_at_interior (lens : GraphLens) (x : UnitPoint)
    (hleft : (lens.left : ℝ) < x) (hright : (x : ℝ) < lens.right) :
    upper lens x ≠ lower lens x := by
  rcases upper_eq_f_or_g lens with hu | hu <;>
    rcases lower_eq_f_or_g lens with hl | hl
  · exact False.elim (upper_ne_lower lens (hu.trans hl.symm))
  · simpa [hu, hl] using lens.no_interior_intersection x hleft hright
  · simpa [hu, hl] using (lens.no_interior_intersection x hleft hright).symm
  · exact False.elim (upper_ne_lower lens (hu.trans hl.symm))

theorem zero_between {u v : C2Function} {x y : UnitPoint}
    (hxy : (x : ℝ) ≤ y) (hxu : u x ≤ v x) (hyu : v y ≤ u y) :
    ∃ z : UnitPoint, (x : ℝ) ≤ z ∧ (z : ℝ) ≤ y ∧ u z = v z := by
  let gap : ℝ → ℝ := fun z => u.extension z - v.extension z
  have hcontinuous : Continuous gap :=
    (u.extension_contDiff.continuous.sub v.extension_contDiff.continuous)
  have hzero : (0 : ℝ) ∈ Set.Icc (gap x) (gap y) := by
    constructor <;> dsimp [gap] <;>
      simp only [C2Function.extension_eq_value] <;> linarith
  rcases intermediate_value_Icc (a := (x : ℝ)) (b := (y : ℝ)) (f := gap)
      hxy hcontinuous.continuousOn hzero with
    ⟨z, hz, hgap⟩
  let zPoint : UnitPoint := ⟨z, by
    constructor
    · exact x.property.1.trans hz.1
    · exact hz.2.trans y.property.2⟩
  refine ⟨zPoint, hz.1, hz.2, ?_⟩
  have hu : u.extension z = u zPoint := u.extension_eq_value zPoint
  have hv : v.extension z = v zPoint := v.extension_eq_value zPoint
  dsimp [gap] at hgap
  rw [hu, hv] at hgap
  linarith

theorem strict_zero_between {u v : C2Function} {x y : UnitPoint}
    (hxy : (x : ℝ) < y) (hx : u x < v x) (hy : v y < u y) :
    ∃ z : UnitPoint, (x : ℝ) < z ∧ (z : ℝ) < y ∧ u z = v z := by
  rcases zero_between hxy.le (le_of_lt hx) (le_of_lt hy) with
    ⟨z, hxz, hzy, hz⟩
  refine ⟨z, lt_of_le_of_ne hxz ?_, lt_of_le_of_ne hzy ?_, hz⟩
  · intro hzx
    have : z = x := Subtype.ext hzx.symm
    subst z
    exact (ne_of_lt hx) hz
  · intro hyz
    have : z = y := Subtype.ext hyz
    subst z
    exact (ne_of_gt hy) hz

theorem lower_lt_upper_inside (lens : GraphLens) (x : UnitPoint)
    (hleft : (lens.left : ℝ) < x) (hright : (x : ℝ) < lens.right) :
    lower lens x < upper lens x := by
  by_contra hnot
  have hxle : upper lens x ≤ lower lens x := le_of_not_gt hnot
  by_cases hxmid : (x : ℝ) ≤ midpoint lens
  · rcases zero_between hxmid hxle
        (le_of_lt (lower_lt_upper_at_midpoint lens)) with
      ⟨z, hxz, hzm, hz⟩
    exact upper_ne_lower_at_interior lens z
      (lt_of_lt_of_le hleft hxz)
      (lt_of_le_of_lt hzm (midpoint_lt_right lens)) hz
  · have hmidlex : (midpoint lens : ℝ) ≤ x := le_of_not_ge hxmid
    rcases zero_between hmidlex
        (le_of_lt (lower_lt_upper_at_midpoint lens)) hxle with
      ⟨z, hmz, hzx, hz⟩
    exact upper_ne_lower_at_interior lens z
      (lt_of_lt_of_le (left_lt_midpoint lens) hmz)
      (lt_of_le_of_lt hzx hright) hz.symm

private theorem upper_lower_eq_at_left (lens : GraphLens) :
    upper lens lens.left = lower lens lens.left := by
  rcases upper_eq_f_or_g lens with hu | hu <;>
    rcases lower_eq_f_or_g lens with hl | hl
  · exact False.elim (upper_ne_lower lens (hu.trans hl.symm))
  · simpa [hu, hl] using lens.eq_left
  · simpa [hu, hl] using lens.eq_left.symm
  · exact False.elim (upper_ne_lower lens (hu.trans hl.symm))

private theorem upper_lower_eq_at_right (lens : GraphLens) :
    upper lens lens.right = lower lens lens.right := by
  rcases upper_eq_f_or_g lens with hu | hu <;>
    rcases lower_eq_f_or_g lens with hl | hl
  · exact False.elim (upper_ne_lower lens (hu.trans hl.symm))
  · simpa [hu, hl] using lens.eq_right
  · simpa [hu, hl] using lens.eq_right.symm
  · exact False.elim (upper_ne_lower lens (hu.trans hl.symm))

private theorem gap_deriv (lens : GraphLens) (x : UnitPoint) :
    deriv (fun t : ℝ => (upper lens).extension t - (lower lens).extension t) x =
      (upper lens).firstDeriv x - (lower lens).firstDeriv x := by
  change deriv ((upper lens).extension - (lower lens).extension) x =
    (upper lens).firstDeriv x - (lower lens).firstDeriv x
  rw [deriv_sub
    ((upper lens).extension_contDiff.differentiable (by norm_num)).differentiableAt
    ((lower lens).extension_contDiff.differentiable (by norm_num)).differentiableAt]
  simp

private theorem gap_deriv_ne_zero {curves : Finset C2Function}
    (hfamily : IsGraphPseudoCircleFamily curves) {lens : GraphLens}
    (hsides : lens.f ∈ curves ∧ lens.g ∈ curves) (x : UnitPoint)
    (hzero : upper lens x = lower lens x) :
    deriv (fun t : ℝ => (upper lens).extension t - (lower lens).extension t) x ≠ 0 := by
  rw [gap_deriv]
  have hproper := hfamily.2 (upper lens) (upper_mem_curves hsides)
    (lower lens) (lower_mem_curves hsides) (upper_ne_lower lens) x hzero
  exact sub_ne_zero.mpr hproper

private theorem gap_deriv_pos_left {curves : Finset C2Function}
    (hfamily : IsGraphPseudoCircleFamily curves) {lens : GraphLens}
    (hsides : lens.f ∈ curves ∧ lens.g ∈ curves) :
    0 < deriv (fun t : ℝ =>
      (upper lens).extension t - (lower lens).extension t) lens.left := by
  let gap : ℝ → ℝ :=
    fun t => (upper lens).extension t - (lower lens).extension t
  have hne : deriv gap lens.left ≠ 0 :=
    gap_deriv_ne_zero hfamily hsides lens.left (upper_lower_eq_at_left lens)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hroot : gap lens.left = 0 := by
      dsimp [gap]
      simp [upper_lower_eq_at_left lens]
    have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg hneg hroot
    have hsignRight :
        ∀ᶠ t in 𝓝[>] (lens.left : ℝ),
          SignType.sign (gap t) = SignType.sign ((lens.left : ℝ) - t) :=
      hsign.filter_mono inf_le_left
    have hinterval :
        Set.Ioo (lens.left : ℝ) lens.right ∈ 𝓝[>] (lens.left : ℝ) :=
      Ioo_mem_nhdsGT lens.left_lt_right
    rcases (hsignRight.and hinterval).exists with
      ⟨t, htSign, ht⟩
    let x : UnitPoint := ⟨t, by
      constructor
      · exact lens.left.property.1.trans ht.1.le
      · exact ht.2.le.trans lens.right.property.2⟩
    have hinside := lower_lt_upper_inside lens x ht.1 ht.2
    have hgapPos : 0 < gap t := by
      have hu : (upper lens).extension t = upper lens x :=
        (upper lens).extension_eq_value x
      have hl : (lower lens).extension t = lower lens x :=
        (lower lens).extension_eq_value x
      dsimp [gap]
      rw [hu, hl]
      linarith
    rw [sign_pos hgapPos, sign_neg (sub_neg.mpr ht.1)] at htSign
    contradiction
  · exact hpos

private theorem gap_deriv_neg_right {curves : Finset C2Function}
    (hfamily : IsGraphPseudoCircleFamily curves) {lens : GraphLens}
    (hsides : lens.f ∈ curves ∧ lens.g ∈ curves) :
    deriv (fun t : ℝ =>
      (upper lens).extension t - (lower lens).extension t) lens.right < 0 := by
  let gap : ℝ → ℝ :=
    fun t => (upper lens).extension t - (lower lens).extension t
  have hne : deriv gap lens.right ≠ 0 :=
    gap_deriv_ne_zero hfamily hsides lens.right (upper_lower_eq_at_right lens)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact hneg
  · have hroot : gap lens.right = 0 := by
      dsimp [gap]
      simp [upper_lower_eq_at_right lens]
    have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos hpos hroot
    have hsignLeft :
        ∀ᶠ t in 𝓝[<] (lens.right : ℝ),
          SignType.sign (gap t) = SignType.sign (t - (lens.right : ℝ)) :=
      hsign.filter_mono inf_le_left
    have hinterval :
        Set.Ioo (lens.left : ℝ) lens.right ∈ 𝓝[<] (lens.right : ℝ) :=
      Ioo_mem_nhdsLT lens.left_lt_right
    rcases (hsignLeft.and hinterval).exists with
      ⟨t, htSign, ht⟩
    let x : UnitPoint := ⟨t, by
      constructor
      · exact lens.left.property.1.trans ht.1.le
      · exact ht.2.le.trans lens.right.property.2⟩
    have hinside := lower_lt_upper_inside lens x ht.1 ht.2
    have hgapPos : 0 < gap t := by
      have hu : (upper lens).extension t = upper lens x :=
        (upper lens).extension_eq_value x
      have hl : (lower lens).extension t = lower lens x :=
        (lower lens).extension_eq_value x
      dsimp [gap]
      rw [hu, hl]
      linarith
    rw [sign_pos hgapPos, sign_neg (sub_neg.mpr ht.2)] at htSign
    contradiction

private theorem no_third_intersection {curves : Finset C2Function}
    (hfamily : IsGraphPseudoCircleFamily curves) {lens : GraphLens}
    (hsides : lens.f ∈ curves ∧ lens.g ∈ curves) (x : UnitPoint)
    (hxleft : (x : ℝ) < lens.left ∨ (lens.right : ℝ) < x) :
    upper lens x ≠ lower lens x := by
  intro hzero
  have hthree := hfamily.1 (upper lens) (upper_mem_curves hsides)
    (lower lens) (lower_mem_curves hsides) (upper_ne_lower lens)
  rcases hxleft with hx | hx
  · exact hthree x lens.left lens.right hx lens.left_lt_right hzero
      (upper_lower_eq_at_left lens) (upper_lower_eq_at_right lens)
  · exact hthree lens.left lens.right x lens.left_lt_right hx
      (upper_lower_eq_at_left lens) (upper_lower_eq_at_right lens) hzero

private theorem real_zero_between {u v : C2Function} {x y : UnitPoint}
    (hxy : (x : ℝ) ≤ y) (hxu : u x ≤ v x) (hyu : v y ≤ u y) :
    ∃ z : UnitPoint, (x : ℝ) ≤ z ∧ (z : ℝ) ≤ y ∧ u z = v z :=
  zero_between hxy hxu hyu

theorem upper_lt_lower_left {curves : Finset C2Function}
    (hfamily : IsGraphPseudoCircleFamily curves) {lens : GraphLens}
    (hsides : lens.f ∈ curves ∧ lens.g ∈ curves) (x : UnitPoint)
    (hx : (x : ℝ) < lens.left) :
    upper lens x < lower lens x := by
  let gap : ℝ → ℝ :=
    fun t => (upper lens).extension t - (lower lens).extension t
  have hderiv := gap_deriv_pos_left hfamily hsides
  have hroot : gap lens.left = 0 := by
    dsimp [gap]
    simp [upper_lower_eq_at_left lens]
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos hderiv hroot
  have hsignLeft :
      ∀ᶠ t in 𝓝[<] (lens.left : ℝ),
        SignType.sign (gap t) = SignType.sign (t - (lens.left : ℝ)) :=
    hsign.filter_mono inf_le_left
  have hinterval :
      Set.Ioo (x : ℝ) lens.left ∈ 𝓝[<] (lens.left : ℝ) :=
    Ioo_mem_nhdsLT hx
  rcases (hsignLeft.and hinterval).exists with
    ⟨y, hySign, hxy, hyleft⟩
  let yPoint : UnitPoint := ⟨y, by
    constructor
    · exact x.property.1.trans hxy.le
    · exact hyleft.le.trans lens.left.property.2⟩
  have hgapNeg : gap y < 0 := by
    apply sign_eq_neg_one_iff.mp
    exact hySign.trans (sign_neg (sub_neg.mpr hyleft))
  have hyUpper : upper lens yPoint < lower lens yPoint := by
    have hu : (upper lens).extension y = upper lens yPoint :=
      (upper lens).extension_eq_value yPoint
    have hl : (lower lens).extension y = lower lens yPoint :=
      (lower lens).extension_eq_value yPoint
    dsimp [gap] at hgapNeg
    rw [hu, hl] at hgapNeg
    linarith
  by_contra hnot
  have hxLower : lower lens x ≤ upper lens x := le_of_not_gt hnot
  rcases real_zero_between hxy.le hxLower (le_of_lt hyUpper) with
    ⟨z, hxz, hzy, hz⟩
  exact no_third_intersection hfamily hsides z
    (Or.inl (lt_of_le_of_lt hzy hyleft)) hz.symm

theorem upper_lt_lower_right {curves : Finset C2Function}
    (hfamily : IsGraphPseudoCircleFamily curves) {lens : GraphLens}
    (hsides : lens.f ∈ curves ∧ lens.g ∈ curves) (x : UnitPoint)
    (hx : (lens.right : ℝ) < x) :
    upper lens x < lower lens x := by
  let gap : ℝ → ℝ :=
    fun t => (upper lens).extension t - (lower lens).extension t
  have hderiv := gap_deriv_neg_right hfamily hsides
  have hroot : gap lens.right = 0 := by
    dsimp [gap]
    simp [upper_lower_eq_at_right lens]
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg hderiv hroot
  have hsignRight :
      ∀ᶠ t in 𝓝[>] (lens.right : ℝ),
        SignType.sign (gap t) = SignType.sign ((lens.right : ℝ) - t) :=
    hsign.filter_mono inf_le_left
  have hinterval :
      Set.Ioo (lens.right : ℝ) (x : ℝ) ∈ 𝓝[>] (lens.right : ℝ) :=
    Ioo_mem_nhdsGT hx
  rcases (hsignRight.and hinterval).exists with
    ⟨y, hySign, hrighty, hyx⟩
  let yPoint : UnitPoint := ⟨y, by
    constructor
    · exact lens.right.property.1.trans hrighty.le
    · exact hyx.le.trans x.property.2⟩
  have hgapNeg : gap y < 0 := by
    apply sign_eq_neg_one_iff.mp
    exact hySign.trans (sign_neg (sub_neg.mpr hrighty))
  have hyUpper : upper lens yPoint < lower lens yPoint := by
    have hu : (upper lens).extension y = upper lens yPoint :=
      (upper lens).extension_eq_value yPoint
    have hl : (lower lens).extension y = lower lens yPoint :=
      (lower lens).extension_eq_value yPoint
    dsimp [gap] at hgapNeg
    rw [hu, hl] at hgapNeg
    linarith
  by_contra hnot
  have hxLower : lower lens x ≤ upper lens x := le_of_not_gt hnot
  rcases real_zero_between hyx.le (le_of_lt hyUpper) hxLower with
    ⟨z, hyz, hzx, hz⟩
  exact no_third_intersection hfamily hsides z
    (Or.inr (lt_of_lt_of_le hrighty hyz)) hz

end Kakeya.Cinematic.GraphLensBridge
