import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorExtensionConstruction
import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorQuadraticTransportInputs

/-!
# Properties of the centered Taylor extension

The concrete extension uses one location and one displacement for every
function at a fixed transported point.  This common-witness form is stronger
than the public pointwise quadratic certificate and is the form needed for
metric and cinematic estimates.
-/

noncomputable section

namespace Kakeya.Cinematic

open C2Function

private lemma extension_jet_eq
    (f : C2Function) (x : UnitPoint) :
    f.extension x = f x ∧
      deriv f.extension x = f.firstDeriv x ∧
      deriv (deriv f.extension) x = f.secondDeriv x :=
  ⟨f.extension_eq_value x, f.deriv_extension_eq_firstDeriv x,
    f.secondDeriv_extension_eq_secondDeriv x⟩

lemma hasDerivAt_piecewise_Iic
    {f g f' g' : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x)
    (hval : f a = g a) (hderiv : f' a = g' a) :
    ∀ x, HasDerivAt
      (Set.piecewise (Set.Iic a) f g)
      (Set.piecewise (Set.Iic a) f' g' x) x := by
  classical
  intro x
  by_cases hx : x < a
  · have hfun :
        Set.piecewise (Set.Iic a) f g =ᶠ[nhds x] f := by
      filter_upwards [Iio_mem_nhds hx] with z hz
      exact Set.piecewise_eq_of_mem _ _ _
        (show z ≤ a from hz.le)
    have hder :
        Set.piecewise (Set.Iic a) f' g' =ᶠ[nhds x] f' := by
      filter_upwards [Iio_mem_nhds hx] with z hz
      exact Set.piecewise_eq_of_mem _ _ _
        (show z ≤ a from hz.le)
    rw [hder.eq_of_nhds]
    exact (hf x).congr_of_eventuallyEq hfun
  · by_cases hxa : x = a
    · subst x
      have hleft :
          HasDerivWithinAt
            (Set.piecewise (Set.Iic a) f g) (f' a)
            (Set.Iic a) a := by
        apply (hf a).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
        · filter_upwards [self_mem_nhdsWithin] with z hz
          exact Set.piecewise_eq_of_mem _ _ _ hz
        · change a ≤ a
          exact le_rfl
      have hright :
          HasDerivWithinAt
            (Set.piecewise (Set.Iic a) f g) (f' a)
            (Set.Ici a) a := by
        have hg' : HasDerivWithinAt g (f' a) (Set.Ici a) a := by
          rw [hderiv]
          exact (hg a).hasDerivWithinAt
        have heq :
            Set.piecewise (Set.Iic a) f g
              =ᶠ[nhdsWithin a (Set.Ici a)] g := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          by_cases hza : z = a
          · subst z
            rw [Set.piecewise_eq_of_mem _ _ _
              (by change a ≤ a; exact le_rfl), hval]
          · exact Set.piecewise_eq_of_notMem _ _ _
              (show ¬z ≤ a from not_le.mpr
                (lt_of_le_of_ne hz (Ne.symm hza)))
        exact hg'.congr_of_eventuallyEq_of_mem heq
          (by change a ≤ a; exact le_rfl)
      have hunion :
          HasDerivWithinAt
            (Set.piecewise (Set.Iic a) f g) (f' a)
            (Set.Iic a ∪ Set.Ici a) a :=
        hleft.union hright
      have huniv : Set.Iic a ∪ Set.Ici a = Set.univ := by
        ext z
        simp
      rw [huniv] at hunion
      have hfinal :
          HasDerivAt (Set.piecewise (Set.Iic a) f g) (f' a) a :=
        hasDerivWithinAt_univ.mp hunion
      rw [Set.piecewise_eq_of_mem _ _ _
        (by change a ≤ a; exact le_rfl)]
      exact hfinal
    · have hax : a < x :=
        lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hxa)
      have hfun :
          Set.piecewise (Set.Iic a) f g =ᶠ[nhds x] g := by
        filter_upwards [Ioi_mem_nhds hax] with z hz
        exact Set.piecewise_eq_of_notMem _ _ _
          (show ¬z ≤ a from not_le.mpr hz)
      have hder :
          Set.piecewise (Set.Iic a) f' g' =ᶠ[nhds x] g' := by
        filter_upwards [Ioi_mem_nhds hax] with z hz
        exact Set.piecewise_eq_of_notMem _ _ _
          (show ¬z ≤ a from not_le.mpr hz)
      rw [hder.eq_of_nhds]
      exact (hg x).congr_of_eventuallyEq hfun

private lemma hasDerivAt_leftPoly
    (f : C2Function) (I : ParameterInterval) :
    ∀ y, HasDerivAt (taylorLeftPoly f I) (taylorLeftPoly' f I y) y := by
  intro y
  have hdiff : Differentiable ℝ (taylorLeftPoly f I) := by
    change Differentiable ℝ (fun z : ℝ =>
      f.extension I.left +
        deriv f.extension I.left * (z - taylorLeft I) +
        (deriv (deriv f.extension) I.left / 2) *
          (z - taylorLeft I) ^ 2)
    fun_prop
  have h := (hdiff y).hasDerivAt
  rw [congrFun (deriv_leftPoly f I) y] at h
  exact h

private lemma hasDerivAt_midFunc
    (f : C2Function) (I : ParameterInterval) :
    ∀ y, HasDerivAt (taylorMidFunc f I) (taylorMidFunc' f I y) y := by
  intro y
  have hinner : HasDerivAt (fun z : ℝ => z - taylorShift I) 1 y :=
    (hasDerivAt_id y).sub_const (taylorShift I)
  have houter : HasDerivAt f.extension
      (deriv f.extension (y - taylorShift I))
      (y - taylorShift I) :=
    (f.extension_contDiff.differentiable (by norm_num)
      (y - taylorShift I)).hasDerivAt
  have hcomp : HasDerivAt
      (f.extension ∘ fun z : ℝ => z - taylorShift I)
      (deriv f.extension (y - taylorShift I) * 1) y :=
    houter.comp y hinner
  change HasDerivAt
    (fun z : ℝ => f.extension (z - taylorShift I))
    (deriv f.extension (y - taylorShift I)) y
  simpa only [Function.comp_def, mul_one] using hcomp

private lemma hasDerivAt_rightPoly
    (f : C2Function) (I : ParameterInterval) :
    ∀ y, HasDerivAt (taylorRightPoly f I) (taylorRightPoly' f I y) y := by
  intro y
  have hdiff : Differentiable ℝ (taylorRightPoly f I) := by
    change Differentiable ℝ (fun z : ℝ =>
      f.extension I.right +
        deriv f.extension I.right * (z - taylorRight I) +
        (deriv (deriv f.extension) I.right / 2) *
          (z - taylorRight I) ^ 2)
    fun_prop
  have h := (hdiff y).hasDerivAt
  rw [congrFun (deriv_rightPoly f I) y] at h
  exact h

private lemma hasDerivAt_leftPoly'
    (f : C2Function) (I : ParameterInterval) :
    ∀ y, HasDerivAt (taylorLeftPoly' f I)
      (deriv (deriv f.extension) I.left) y := by
  intro y
  have hid : HasDerivAt (fun z : ℝ => z - taylorLeft I) 1 y :=
    (hasDerivAt_id y).sub_const (taylorLeft I)
  have hmul : HasDerivAt
      (fun z : ℝ =>
        deriv (deriv f.extension) I.left * (z - taylorLeft I))
      (deriv (deriv f.extension) I.left) y := by
    simpa only [id_eq, mul_one] using
      hid.const_mul (deriv (deriv f.extension) I.left)
  have hconst : HasDerivAt
      (fun _ : ℝ => deriv f.extension I.left) 0 y :=
    hasDerivAt_const y _
  have hsum : HasDerivAt
      (fun z : ℝ =>
        deriv f.extension I.left +
          deriv (deriv f.extension) I.left * (z - taylorLeft I))
      ((0 : ℝ) + deriv (deriv f.extension) I.left) y :=
    hconst.add hmul
  have hfinal : HasDerivAt (taylorLeftPoly' f I)
      ((0 : ℝ) + deriv (deriv f.extension) I.left) y := by
    convert hsum using 1 <;> funext z <;> rfl
  simpa only [zero_add] using hfinal

private lemma hasDerivAt_midFunc'
    (f : C2Function) (I : ParameterInterval) :
    ∀ y, HasDerivAt (taylorMidFunc' f I)
      (deriv (deriv f.extension) (y - taylorShift I)) y := by
  intro y
  have hinner : HasDerivAt (fun z : ℝ => z - taylorShift I) 1 y :=
    (hasDerivAt_id y).sub_const (taylorShift I)
  have houter : HasDerivAt (deriv f.extension)
      (deriv (deriv f.extension) (y - taylorShift I))
      (y - taylorShift I) :=
    (f.extension_contDiff.differentiable_deriv_two
      (y - taylorShift I)).hasDerivAt
  have hcomp : HasDerivAt
      ((deriv f.extension) ∘ fun z : ℝ => z - taylorShift I)
      (deriv (deriv f.extension) (y - taylorShift I) * 1) y :=
    houter.comp y hinner
  change HasDerivAt
    (fun z : ℝ => deriv f.extension (z - taylorShift I))
    (deriv (deriv f.extension) (y - taylorShift I)) y
  simpa only [Function.comp_def, mul_one] using hcomp

private lemma hasDerivAt_rightPoly'
    (f : C2Function) (I : ParameterInterval) :
    ∀ y, HasDerivAt (taylorRightPoly' f I)
      (deriv (deriv f.extension) I.right) y := by
  intro y
  have hid : HasDerivAt (fun z : ℝ => z - taylorRight I) 1 y :=
    (hasDerivAt_id y).sub_const (taylorRight I)
  have hmul : HasDerivAt
      (fun z : ℝ =>
        deriv (deriv f.extension) I.right * (z - taylorRight I))
      (deriv (deriv f.extension) I.right) y := by
    simpa only [id_eq, mul_one] using
      hid.const_mul (deriv (deriv f.extension) I.right)
  have hconst : HasDerivAt
      (fun _ : ℝ => deriv f.extension I.right) 0 y :=
    hasDerivAt_const y _
  have hsum : HasDerivAt
      (fun z : ℝ =>
        deriv f.extension I.right +
          deriv (deriv f.extension) I.right * (z - taylorRight I))
      ((0 : ℝ) + deriv (deriv f.extension) I.right) y :=
    hconst.add hmul
  have hfinal : HasDerivAt (taylorRightPoly' f I)
      ((0 : ℝ) + deriv (deriv f.extension) I.right) y := by
    convert hsum using 1 <;> funext z <;> rfl
  simpa only [zero_add] using hfinal

lemma hasDerivAt_taylorExtensionFun
    (f : C2Function) (I : ParameterInterval) (h_len : 0 < I.length) :
    ∀ y, HasDerivAt (taylorExtensionFun f I)
      (taylorExtensionFun' f I y) y := by
  let leftMid :=
    Set.piecewise (Set.Iic (taylorLeft I))
      (taylorLeftPoly f I) (taylorMidFunc f I)
  let leftMid' :=
    Set.piecewise (Set.Iic (taylorLeft I))
      (taylorLeftPoly' f I) (taylorMidFunc' f I)
  have hleftMid : ∀ y, HasDerivAt leftMid (leftMid' y) y :=
    hasDerivAt_piecewise_Iic
      (hasDerivAt_leftPoly f I) (hasDerivAt_midFunc f I)
      (taylor_match_val_L f I)
      (by
        simpa only [deriv_leftPoly, deriv_midFunc] using
          taylor_match_deriv_L f I)
  have hlt : taylorLeft I < taylorRight I :=
    taylorLeft_lt_taylorRight I h_len
  have hmatch : leftMid (taylorRight I) =
      taylorRightPoly f I (taylorRight I) := by
    rw [show leftMid (taylorRight I) =
        taylorMidFunc f I (taylorRight I) by
      exact Set.piecewise_eq_of_notMem _ _ _ (not_le.mpr hlt)]
    exact taylor_match_val_R f I
  have hmatch' : leftMid' (taylorRight I) =
      taylorRightPoly' f I (taylorRight I) := by
    rw [show leftMid' (taylorRight I) =
        taylorMidFunc' f I (taylorRight I) by
      exact Set.piecewise_eq_of_notMem _ _ _ (not_le.mpr hlt)]
    simpa only [deriv_midFunc, deriv_rightPoly] using
      taylor_match_deriv_R f I
  simpa only [taylorExtensionFun, taylorExtensionFun', leftMid, leftMid'] using
    hasDerivAt_piecewise_Iic hleftMid (hasDerivAt_rightPoly f I)
      hmatch hmatch'

lemma hasDerivAt_taylorExtensionFun'
    (f : C2Function) (I : ParameterInterval) (h_len : 0 < I.length) :
    ∀ y, HasDerivAt (taylorExtensionFun' f I)
      (taylorExtensionFun'' f I y) y := by
  let leftMid' :=
    Set.piecewise (Set.Iic (taylorLeft I))
      (taylorLeftPoly' f I) (taylorMidFunc' f I)
  let leftMid'' :=
    Set.piecewise (Set.Iic (taylorLeft I))
      (fun _ => deriv (deriv f.extension) I.left)
      (fun y => deriv (deriv f.extension) (y - taylorShift I))
  have hleftMid : ∀ y, HasDerivAt leftMid' (leftMid'' y) y :=
    hasDerivAt_piecewise_Iic
      (hasDerivAt_leftPoly' f I) (hasDerivAt_midFunc' f I)
      (by
        simpa only [deriv_leftPoly, deriv_midFunc] using
          taylor_match_deriv_L f I)
      (by
        congr 1
        simp [taylorLeft, taylorShift])
  have hlt : taylorLeft I < taylorRight I :=
    taylorLeft_lt_taylorRight I h_len
  have hmatch : leftMid' (taylorRight I) =
      taylorRightPoly' f I (taylorRight I) := by
    rw [show leftMid' (taylorRight I) =
        taylorMidFunc' f I (taylorRight I) by
      exact Set.piecewise_eq_of_notMem _ _ _ (not_le.mpr hlt)]
    simpa only [deriv_midFunc, deriv_rightPoly] using
      taylor_match_deriv_R f I
  have hmatch' : leftMid'' (taylorRight I) =
      deriv (deriv f.extension) I.right := by
    rw [show leftMid'' (taylorRight I) =
        deriv (deriv f.extension)
          (taylorRight I - taylorShift I) by
      exact Set.piecewise_eq_of_notMem _ _ _ (not_le.mpr hlt)]
    simp [taylorRight, taylorShift]
  simpa only [taylorExtensionFun', taylorExtensionFun'', leftMid', leftMid''] using
    hasDerivAt_piecewise_Iic hleftMid (hasDerivAt_rightPoly' f I)
      hmatch hmatch'

lemma deriv_taylorExtensionFun (f : C2Function) (I : ParameterInterval)
    (h_len : 0 < I.length) :
    deriv (taylorExtensionFun f I) = taylorExtensionFun' f I := by
  funext y
  exact (hasDerivAt_taylorExtensionFun f I h_len y).deriv

lemma deriv_taylorExtensionFun' (f : C2Function) (I : ParameterInterval)
    (h_len : 0 < I.length) :
    deriv (taylorExtensionFun' f I) = taylorExtensionFun'' f I := by
  funext y
  exact (hasDerivAt_taylorExtensionFun' f I h_len y).deriv

lemma taylorExtend_firstDeriv
    (f : C2Function) (I : ParameterInterval) (K : ℝ)
    (hK : 1 ≤ K) (h_len : 0 < I.length)
    (h_short : I.IsShort (12 * K)) (y : UnitPoint) :
    (taylorExtend f I K hK h_len h_short).firstDeriv y =
      taylorExtensionFun' f I y := by
  rw [taylorExtend_deriv,
    congrFun (deriv_taylorExtensionFun f I h_len) y]

lemma taylorExtend_secondDeriv
    (f : C2Function) (I : ParameterInterval) (K : ℝ)
    (hK : 1 ≤ K) (h_len : 0 < I.length)
    (h_short : I.IsShort (12 * K)) (y : UnitPoint) :
    (taylorExtend f I K hK h_len h_short).secondDeriv y =
      taylorExtensionFun'' f I y := by
  rw [taylorExtend_deriv2, deriv_taylorExtensionFun f I h_len,
    congrFun (deriv_taylorExtensionFun' f I h_len) y]

/--
At each transported point, all source functions use the same physical base
point and the same Taylor displacement.
-/
def IsCommonCenteredQuadraticJetExtension
    (I : ParameterInterval) (transport : C2Function → C2Function) : Prop :=
  ∀ y : UnitPoint,
    ∃ x : I.LocalPoint, ∃ t : ℝ,
      |t| ≤ 1 / 2 ∧
        ∀ f : C2Function,
          transport f y =
              f x.1 + f.firstDeriv x.1 * t +
                (f.secondDeriv x.1 / 2) * t ^ 2 ∧
            (transport f).firstDeriv y =
              f.firstDeriv x.1 + f.secondDeriv x.1 * t ∧
            (transport f).secondDeriv y = f.secondDeriv x.1

lemma taylorExtend_commonQuadraticJetExtension
    (I : ParameterInterval) (K : ℝ)
    (hK : 1 ≤ K) (h_len : 0 < I.length)
    (h_short : I.IsShort (12 * K)) :
    IsCommonCenteredQuadraticJetExtension I
      (fun f => taylorExtend f I K hK h_len h_short) := by
  intro y
  have hy0 : 0 ≤ (y : ℝ) := y.2.1
  have hy1 : (y : ℝ) ≤ 1 := y.2.2
  have hleft0 : 0 < taylorLeft I :=
    taylorLeft_pos I K hK h_short
  have hright1 : taylorRight I < 1 :=
    taylorRight_lt_one I K hK h_short
  by_cases hleft : (y : ℝ) ≤ taylorLeft I
  · let xPoint : UnitPoint := ⟨I.left, I.left_mem⟩
    let x : I.LocalPoint :=
      ⟨xPoint, ⟨le_rfl, I.left_le_right⟩⟩
    let t : ℝ := (y : ℝ) - taylorLeft I
    have ht_nonpos : t ≤ 0 := by
      dsimp only [t]
      linarith
    have ht_lower : -(1 / 2 : ℝ) ≤ t := by
      dsimp only [t]
      rw [taylorLeft_eq]
      have hlen : 0 ≤ I.length := I.length_nonneg
      linarith
    refine ⟨x, t, ?_, ?_⟩
    · rw [abs_of_nonpos ht_nonpos]
      linarith
    · intro f
      have hval := eval_left (f := f) (I := I) hleft
      have hfirst := eval'_left (f := f) (I := I) hleft
      have hsecond := eval''_left (f := f) (I := I) hleft
      rw [taylorExtend_val, hval, taylorExtend_firstDeriv, hfirst,
        taylorExtend_secondDeriv, hsecond]
      rcases extension_jet_eq f xPoint with ⟨hvalue, hderiv, hderiv2⟩
      simp only [taylorLeftPoly, taylorLeftPoly', x, t]
      rw [hvalue, hderiv, hderiv2]
      exact ⟨rfl, rfl, rfl⟩
  · have hleft' : taylorLeft I < (y : ℝ) := lt_of_not_ge hleft
    by_cases hright : (y : ℝ) ≤ taylorRight I
    · have hxleft : I.left ≤ (y : ℝ) - taylorShift I := by
        dsimp only [taylorLeft] at hleft'
        linarith
      have hxright : (y : ℝ) - taylorShift I ≤ I.right := by
        dsimp only [taylorRight] at hright
        linarith
      let xPoint : UnitPoint :=
        ⟨(y : ℝ) - taylorShift I,
          ⟨I.left_mem.1.trans hxleft, hxright.trans I.right_mem.2⟩⟩
      let x : I.LocalPoint := ⟨xPoint, ⟨hxleft, hxright⟩⟩
      refine ⟨x, 0, by norm_num, ?_⟩
      intro f
      have hval := eval_mid (f := f) (I := I) hleft' hright
      have hfirst := eval'_mid (f := f) (I := I) hleft' hright
      have hsecond := eval''_mid (f := f) (I := I) hleft' hright
      rw [taylorExtend_val, hval, taylorExtend_firstDeriv, hfirst,
        taylorExtend_secondDeriv, hsecond]
      rcases extension_jet_eq f xPoint with ⟨hvalue, hderiv, hderiv2⟩
      change
        f.extension (xPoint : ℝ) =
              f xPoint + f.firstDeriv xPoint * 0 +
                (f.secondDeriv xPoint / 2) * 0 ^ 2 ∧
          deriv f.extension (xPoint : ℝ) =
              f.firstDeriv xPoint + f.secondDeriv xPoint * 0 ∧
          deriv (deriv f.extension) (xPoint : ℝ) =
              f.secondDeriv xPoint
      rw [hvalue, hderiv, hderiv2]
      norm_num
    · have hright' : taylorRight I < (y : ℝ) := lt_of_not_ge hright
      let xPoint : UnitPoint := ⟨I.right, I.right_mem⟩
      let x : I.LocalPoint :=
        ⟨xPoint, ⟨I.left_le_right, le_rfl⟩⟩
      let t : ℝ := (y : ℝ) - taylorRight I
      have ht_nonneg : 0 ≤ t := by
        dsimp only [t]
        linarith
      have ht_upper : t ≤ 1 / 2 := by
        dsimp only [t]
        rw [taylorRight_eq]
        have hlen : 0 ≤ I.length := I.length_nonneg
        linarith
      refine ⟨x, t, ?_, ?_⟩
      · rw [abs_of_nonneg ht_nonneg]
        exact ht_upper
      · intro f
        have hval := eval_right (f := f) (I := I) hright'
        have hfirst := eval'_right (f := f) (I := I) hright'
        have hsecond := eval''_right (f := f) (I := I) hright'
        rw [taylorExtend_val, hval, taylorExtend_firstDeriv, hfirst,
          taylorExtend_secondDeriv, hsecond]
        rcases extension_jet_eq f xPoint with
          ⟨hvalue, hderiv, hderiv2⟩
        simp only [taylorRightPoly, taylorRightPoly', x, t]
        rw [hvalue, hderiv, hderiv2]
        exact ⟨rfl, rfl, rfl⟩

lemma commonCenteredQuadraticJetExtension_implies_pointwise
    {I : ParameterInterval} {transport : C2Function → C2Function}
    (hcommon : IsCommonCenteredQuadraticJetExtension I transport) :
    ∀ f, IsCenteredQuadraticJetExtension I f (transport f) := by
  intro f y
  rcases hcommon y with ⟨x, t, ht, hall⟩
  exact ⟨x, t, ht, hall f⟩

lemma taylorExtend_isCenteredQuadraticJetExtension
    (f : C2Function) (I : ParameterInterval) (K : ℝ)
    (hK : 1 ≤ K) (h_len : 0 < I.length)
    (h_short : I.IsShort (12 * K)) :
    IsCenteredQuadraticJetExtension I f
      (taylorExtend f I K hK h_len h_short) :=
  commonCenteredQuadraticJetExtension_implies_pointwise
    (taylorExtend_commonQuadraticJetExtension I K hK h_len h_short) f

lemma taylorExtend_isCenteredJetCopy
    (f : C2Function) (I : ParameterInterval) (K : ℝ)
    (hK : 1 ≤ K) (h_len : 0 < I.length)
    (h_short : I.IsShort (12 * K)) :
    IsCenteredJetCopy I f (taylorExtend f I K hK h_len h_short) := by
  constructor
  · intro x
    let yReal : ℝ := (x.1 : ℝ) + (1 / 2 - I.midpoint)
    have hleft : taylorLeft I ≤ yReal := by
      dsimp only [yReal, taylorLeft, taylorShift]
      linarith [x.2.1]
    have hright : yReal ≤ taylorRight I := by
      dsimp only [yReal, taylorRight, taylorShift]
      linarith [x.2.2]
    have hy0 : 0 ≤ yReal :=
      (taylorLeft_pos I K hK h_short).le.trans hleft
    have hy1 : yReal ≤ 1 :=
      hright.trans (taylorRight_lt_one I K hK h_short).le
    let y : UnitPoint := ⟨yReal, ⟨hy0, hy1⟩⟩
    refine ⟨y, rfl, ?_⟩
    by_cases hboundary : yReal = taylorLeft I
    · have hval := eval_left (f := f) (I := I) hboundary.le
      have hfirst := eval'_left (f := f) (I := I) hboundary.le
      have hsecond := eval''_left (f := f) (I := I) hboundary.le
      have hxleft : (x.1 : ℝ) = I.left := by
        dsimp only [yReal, taylorLeft, taylorShift] at hboundary
        linarith
      have hxPoint :
          x.1 = (⟨I.left, I.left_mem⟩ : UnitPoint) := by
        apply Subtype.ext
        exact hxleft
      rw [taylorExtend_val, hval, taylorExtend_firstDeriv, hfirst,
        taylorExtend_secondDeriv, hsecond]
      rw [hxPoint]
      simpa [taylorLeftPoly, taylorLeftPoly', y, yReal, hboundary] using
        extension_jet_eq f (⟨I.left, I.left_mem⟩ : UnitPoint)
    · have hstrict : taylorLeft I < yReal :=
        lt_of_le_of_ne hleft (Ne.symm hboundary)
      have hval := eval_mid (f := f) (I := I) hstrict hright
      have hfirst := eval'_mid (f := f) (I := I) hstrict hright
      have hsecond := eval''_mid (f := f) (I := I) hstrict hright
      rw [taylorExtend_val, hval, taylorExtend_firstDeriv, hfirst,
        taylorExtend_secondDeriv, hsecond]
      simp only [taylorMidFunc, taylorMidFunc']
      have hcoord :
          yReal - taylorShift I = (x.1 : ℝ) := by
        simp [yReal, taylorShift]
      rw [hcoord]
      exact extension_jet_eq f x.1
  · intro y hy
    have hleft : taylorLeft I ≤ (y : ℝ) := by
      rw [taylorLeft_eq]
      have h := (abs_le.mp hy).1
      linarith
    have hright : (y : ℝ) ≤ taylorRight I := by
      rw [taylorRight_eq]
      have h := (abs_le.mp hy).2
      linarith
    let xReal : ℝ := (y : ℝ) - (1 / 2 - I.midpoint)
    have hxleft : I.left ≤ xReal := by
      rw [taylorLeft, taylorShift] at hleft
      dsimp only [xReal]
      linarith
    have hxright : xReal ≤ I.right := by
      rw [taylorRight, taylorShift] at hright
      dsimp only [xReal]
      linarith
    let xPoint : UnitPoint :=
      ⟨xReal, ⟨I.left_mem.1.trans hxleft, hxright.trans I.right_mem.2⟩⟩
    let x : I.LocalPoint := ⟨xPoint, ⟨hxleft, hxright⟩⟩
    refine ⟨x, rfl, ?_⟩
    have hleft' : taylorLeft I < (y : ℝ) ∨
        (y : ℝ) = taylorLeft I := by
      rcases lt_or_eq_of_le hleft with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr heq.symm
    rcases hleft' with hstrict | hboundary
    · have hval := eval_mid (f := f) (I := I) hstrict hright
      have hfirst := eval'_mid (f := f) (I := I) hstrict hright
      have hsecond := eval''_mid (f := f) (I := I) hstrict hright
      rw [taylorExtend_val, hval, taylorExtend_firstDeriv, hfirst,
        taylorExtend_secondDeriv, hsecond]
      simp only [taylorMidFunc, taylorMidFunc']
      have hcoord :
          (y : ℝ) - taylorShift I = xReal := by
        simp [xReal, taylorShift]
      rw [hcoord]
      exact extension_jet_eq f xPoint
    · have hval := eval_left (f := f) (I := I) hboundary.le
      have hfirst := eval'_left (f := f) (I := I) hboundary.le
      have hsecond := eval''_left (f := f) (I := I) hboundary.le
      rw [taylorExtend_val, hval, taylorExtend_firstDeriv, hfirst,
        taylorExtend_secondDeriv, hsecond]
      simp only [x]
      have hxPoint :
          xPoint = (⟨I.left, I.left_mem⟩ : UnitPoint) := by
        apply Subtype.ext
        dsimp only [xPoint, xReal]
        rw [hboundary, taylorLeft, taylorShift]
        ring
      rw [hxPoint]
      simpa [taylorLeftPoly, taylorLeftPoly', hboundary] using
        extension_jet_eq f (⟨I.left, I.left_mem⟩ : UnitPoint)

end Kakeya.Cinematic
