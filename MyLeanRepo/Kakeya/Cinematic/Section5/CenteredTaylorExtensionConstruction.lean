import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorExtension

/-!
# Construction and API lemmas for centered Taylor extension

Provides `taylorExtend` and location lemmas proving that the transported
function equals the translated original on the copied interval and the
quadratic Taylor polynomials outside.
-/

noncomputable section

namespace Kakeya.Cinematic

open C2Function

lemma taylor_match_val_L (f : C2Function) (I : ParameterInterval) :
    taylorLeftPoly f I (taylorLeft I) =
      taylorMidFunc f I (taylorLeft I) := by
  simp [taylorLeftPoly, taylorMidFunc, taylorLeft, taylorShift,
    ParameterInterval.midpoint]

lemma taylor_match_deriv_L (f : C2Function) (I : ParameterInterval) :
    deriv (taylorLeftPoly f I) (taylorLeft I) =
      deriv (taylorMidFunc f I) (taylorLeft I) := by
  rw [deriv_leftPoly, deriv_midFunc]
  simp [taylorLeftPoly', taylorMidFunc', taylorLeft, taylorShift]

lemma taylor_match_second_L (f : C2Function) (I : ParameterInterval) :
    deriv (deriv (taylorLeftPoly f I)) (taylorLeft I) =
      deriv (deriv (taylorMidFunc f I)) (taylorLeft I) := by
  rw [deriv2_leftPoly, deriv2_midFunc]
  simp [taylorLeft, taylorShift, ParameterInterval.midpoint]

lemma taylor_match_val_R (f : C2Function) (I : ParameterInterval) :
    taylorMidFunc f I (taylorRight I) =
      taylorRightPoly f I (taylorRight I) := by
  simp [taylorMidFunc, taylorRightPoly, taylorRight, taylorShift,
    ParameterInterval.midpoint]

lemma taylor_match_deriv_R (f : C2Function) (I : ParameterInterval) :
    deriv (taylorMidFunc f I) (taylorRight I) =
      deriv (taylorRightPoly f I) (taylorRight I) := by
  rw [deriv_midFunc, deriv_rightPoly]
  simp [taylorMidFunc', taylorRightPoly', taylorRight, taylorShift]

lemma taylor_match_second_R (f : C2Function) (I : ParameterInterval) :
    deriv (deriv (taylorMidFunc f I)) (taylorRight I) =
      deriv (deriv (taylorRightPoly f I)) (taylorRight I) := by
  rw [deriv2_midFunc, deriv2_rightPoly]
  simp [taylorRight, taylorShift, ParameterInterval.midpoint]

lemma taylorLeft_pos (I : ParameterInterval) (K : ℝ) (hK : 1 ≤ K)
    (h_short : I.IsShort (12 * K)) :
    0 < taylorLeft I := by
  have hK_pos : 0 < K := by linarith
  have h_len_bound : I.length ≤ 1 / (72 * K) := by
    have h : I.length ≤ (6 * (12 * K))⁻¹ := h_short
    have h_eq : (6 * (12 * K))⁻¹ = 1 / (72 * K) := by
      field_simp [hK_pos.ne']
      ring
    simpa [h_eq] using h
  have h_len_small : I.length ≤ 1 / 72 := by
    have hden : 72 ≤ 72 * K := by linarith
    have hdiv : 1 / (72 * K) ≤ 1 / 72 :=
      one_div_le_one_div_of_le (by norm_num) hden
    exact h_len_bound.trans hdiv
  rw [taylorLeft_eq]
  linarith

lemma taylorRight_lt_one (I : ParameterInterval) (K : ℝ) (hK : 1 ≤ K)
    (h_short : I.IsShort (12 * K)) :
    taylorRight I < 1 := by
  have hK_pos : 0 < K := by linarith
  have h_len_bound : I.length ≤ 1 / (72 * K) := by
    have h : I.length ≤ (6 * (12 * K))⁻¹ := h_short
    have h_eq : (6 * (12 * K))⁻¹ = 1 / (72 * K) := by
      field_simp [hK_pos.ne']
      ring
    simpa [h_eq] using h
  have h_len_small : I.length ≤ 1 / 72 := by
    have hden : 72 ≤ 72 * K := by linarith
    have hdiv : 1 / (72 * K) ≤ 1 / 72 :=
      one_div_le_one_div_of_le (by norm_num) hden
    exact h_len_bound.trans hdiv
  rw [taylorRight_eq]
  linarith

lemma eval_left {f : C2Function} {I : ParameterInterval} {y : ℝ}
    (hy : y ≤ taylorLeft I) :
    taylorExtensionFun f I y = taylorLeftPoly f I y := by
  dsimp only [taylorExtensionFun]
  have h1 : y ≤ taylorRight I := by
    calc
      y ≤ taylorLeft I := hy
      _ ≤ taylorRight I := by
        rw [taylorLeft_eq, taylorRight_eq]
        linarith [I.length_nonneg]
  rw [Set.piecewise_eq_of_mem (Set.Iic (taylorRight I)) _ _ h1]
  rw [Set.piecewise_eq_of_mem (Set.Iic (taylorLeft I)) _ _ hy]

lemma eval_mid {f : C2Function} {I : ParameterInterval} {y : ℝ}
    (hy1 : taylorLeft I < y) (hy2 : y ≤ taylorRight I) :
    taylorExtensionFun f I y = taylorMidFunc f I y := by
  dsimp only [taylorExtensionFun]
  rw [Set.piecewise_eq_of_mem (Set.Iic (taylorRight I)) _ _ hy2]
  rw [Set.piecewise_eq_of_notMem (Set.Iic (taylorLeft I)) _ _
    (not_le.mpr hy1)]

lemma eval_right {f : C2Function} {I : ParameterInterval} {y : ℝ}
    (hy : taylorRight I < y) :
    taylorExtensionFun f I y = taylorRightPoly f I y := by
  dsimp only [taylorExtensionFun]
  rw [Set.piecewise_eq_of_notMem (Set.Iic (taylorRight I)) _ _
    (not_le.mpr hy)]

lemma eval'_left {f : C2Function} {I : ParameterInterval} {y : ℝ}
    (hy : y ≤ taylorLeft I) :
    taylorExtensionFun' f I y = taylorLeftPoly' f I y := by
  dsimp only [taylorExtensionFun']
  have h1 : y ≤ taylorRight I := by
    calc
      y ≤ taylorLeft I := hy
      _ ≤ taylorRight I := by
        rw [taylorLeft_eq, taylorRight_eq]
        linarith [I.length_nonneg]
  rw [Set.piecewise_eq_of_mem (Set.Iic (taylorRight I)) _ _ h1]
  rw [Set.piecewise_eq_of_mem (Set.Iic (taylorLeft I)) _ _ hy]

lemma eval'_mid {f : C2Function} {I : ParameterInterval} {y : ℝ}
    (hy1 : taylorLeft I < y) (hy2 : y ≤ taylorRight I) :
    taylorExtensionFun' f I y = taylorMidFunc' f I y := by
  dsimp only [taylorExtensionFun']
  rw [Set.piecewise_eq_of_mem (Set.Iic (taylorRight I)) _ _ hy2]
  rw [Set.piecewise_eq_of_notMem (Set.Iic (taylorLeft I)) _ _
    (not_le.mpr hy1)]

lemma eval'_right {f : C2Function} {I : ParameterInterval} {y : ℝ}
    (hy : taylorRight I < y) :
    taylorExtensionFun' f I y = taylorRightPoly' f I y := by
  dsimp only [taylorExtensionFun']
  rw [Set.piecewise_eq_of_notMem (Set.Iic (taylorRight I)) _ _
    (not_le.mpr hy)]

lemma eval''_left {f : C2Function} {I : ParameterInterval} {y : ℝ}
    (hy : y ≤ taylorLeft I) :
    taylorExtensionFun'' f I y =
      deriv (deriv f.extension) I.left := by
  dsimp only [taylorExtensionFun'']
  have h1 : y ≤ taylorRight I := by
    calc
      y ≤ taylorLeft I := hy
      _ ≤ taylorRight I := by
        rw [taylorLeft_eq, taylorRight_eq]
        linarith [I.length_nonneg]
  rw [Set.piecewise_eq_of_mem (Set.Iic (taylorRight I)) _ _ h1]
  rw [Set.piecewise_eq_of_mem (Set.Iic (taylorLeft I)) _ _ hy]

lemma eval''_mid {f : C2Function} {I : ParameterInterval} {y : ℝ}
    (hy1 : taylorLeft I < y) (hy2 : y ≤ taylorRight I) :
    taylorExtensionFun'' f I y =
      deriv (deriv f.extension) (y - taylorShift I) := by
  dsimp only [taylorExtensionFun'']
  rw [Set.piecewise_eq_of_mem (Set.Iic (taylorRight I)) _ _ hy2]
  rw [Set.piecewise_eq_of_notMem (Set.Iic (taylorLeft I)) _ _
    (not_le.mpr hy1)]

lemma eval''_right {f : C2Function} {I : ParameterInterval} {y : ℝ}
    (hy : taylorRight I < y) :
    taylorExtensionFun'' f I y =
      deriv (deriv f.extension) I.right := by
  dsimp only [taylorExtensionFun'']
  rw [Set.piecewise_eq_of_notMem (Set.Iic (taylorRight I)) _ _
    (not_le.mpr hy)]

lemma taylorExtensionFun_contDiff (f : C2Function) (I : ParameterInterval)
    (h_len : 0 < I.length) :
    ContDiff ℝ 2 (taylorExtensionFun f I) := by
  classical
  let leftMid :=
    Set.piecewise (Set.Iic (taylorLeft I))
      (taylorLeftPoly f I) (taylorMidFunc f I)
  have hleft : ContDiff ℝ 2 (taylorLeftPoly f I) := by
    change ContDiff ℝ 2 (fun y : ℝ =>
      f.extension I.left +
        deriv f.extension I.left * (y - taylorLeft I) +
        (deriv (deriv f.extension) I.left / 2) *
          (y - taylorLeft I) ^ 2)
    fun_prop
  have hmid : ContDiff ℝ 2 (taylorMidFunc f I) :=
    f.extension_contDiff.comp (contDiff_id.sub contDiff_const)
  have hright : ContDiff ℝ 2 (taylorRightPoly f I) := by
    change ContDiff ℝ 2 (fun y : ℝ =>
      f.extension I.right +
        deriv f.extension I.right * (y - taylorRight I) +
        (deriv (deriv f.extension) I.right / 2) *
          (y - taylorRight I) ^ 2)
    fun_prop
  have hleftMid : ContDiff ℝ 2 leftMid :=
    piecewise2_contDiff2 hleft hmid
      (taylor_match_val_L f I)
      (taylor_match_deriv_L f I)
      (taylor_match_second_L f I)
  have hlt : taylorLeft I < taylorRight I :=
    taylorLeft_lt_taylorRight I h_len
  have hleftMid_value :
      leftMid (taylorRight I) = taylorMidFunc f I (taylorRight I) := by
    exact Set.piecewise_eq_of_notMem _ _ _ (not_le.mpr hlt)
  have hleftMid_deriv :
      deriv leftMid (taylorRight I) =
        deriv (taylorMidFunc f I) (taylorRight I) := by
    have heq :
        leftMid =ᶠ[nhds (taylorRight I)] taylorMidFunc f I := by
      filter_upwards [Ioi_mem_nhds hlt] with z hz
      exact Set.piecewise_eq_of_notMem _ _ _
        (show ¬z ≤ taylorLeft I from not_le.mpr hz)
    exact Filter.EventuallyEq.deriv_eq heq
  have hleftMid_second :
      deriv (deriv leftMid) (taylorRight I) =
        deriv (deriv (taylorMidFunc f I)) (taylorRight I) := by
    have heq :
        leftMid =ᶠ[nhds (taylorRight I)] taylorMidFunc f I := by
      filter_upwards [Ioi_mem_nhds hlt] with z hz
      exact Set.piecewise_eq_of_notMem _ _ _
        (show ¬z ≤ taylorLeft I from not_le.mpr hz)
    have hderiv :
        deriv leftMid =ᶠ[nhds (taylorRight I)]
          deriv (taylorMidFunc f I) :=
      heq.deriv
    exact hderiv.deriv_eq
  apply piecewise2_contDiff2 hleftMid hright
  · exact hleftMid_value.trans (taylor_match_val_R f I)
  · exact hleftMid_deriv.trans (taylor_match_deriv_R f I)
  · exact hleftMid_second.trans (taylor_match_second_R f I)

/--
Translate `f` to center `I` at `1/2` and extend with endpoint Taylor
quadratics.
-/
def taylorExtend (f : C2Function) (I : ParameterInterval) (K : ℝ)
    (hK : 1 ≤ K) (h_len : 0 < I.length)
    (h_short : I.IsShort (12 * K)) :
    C2Function where
  value :=
    ⟨fun x => taylorExtensionFun f I x,
      (taylorExtensionFun_contDiff f I h_len).continuous.comp
        continuous_subtype_val⟩
  firstDeriv :=
    ⟨fun x => deriv (taylorExtensionFun f I) x,
      ((taylorExtensionFun_contDiff f I h_len).continuous_deriv
        (by norm_num)).comp continuous_subtype_val⟩
  secondDeriv :=
    ⟨fun x => deriv (deriv (taylorExtensionFun f I)) x,
      (by
        have h1 : ContDiff ℝ 1 (deriv (taylorExtensionFun f I)) :=
          (taylorExtensionFun_contDiff f I h_len).deriv'
        exact (h1.continuous_deriv (by norm_num)).comp
          continuous_subtype_val)⟩
  hasExtension :=
    ⟨taylorExtensionFun f I, taylorExtensionFun_contDiff f I h_len,
      fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

@[simp]
lemma taylorExtend_val (f : C2Function) (I : ParameterInterval) (K : ℝ)
    (hK : 1 ≤ K) (h_len : 0 < I.length)
    (h_short : I.IsShort (12 * K)) (y : UnitPoint) :
    taylorExtend f I K hK h_len h_short y =
      taylorExtensionFun f I y :=
  rfl

@[simp]
lemma taylorExtend_deriv (f : C2Function) (I : ParameterInterval) (K : ℝ)
    (hK : 1 ≤ K) (h_len : 0 < I.length)
    (h_short : I.IsShort (12 * K)) (y : UnitPoint) :
    (taylorExtend f I K hK h_len h_short).firstDeriv y =
      deriv (taylorExtensionFun f I) y :=
  rfl

@[simp]
lemma taylorExtend_deriv2 (f : C2Function) (I : ParameterInterval) (K : ℝ)
    (hK : 1 ≤ K) (h_len : 0 < I.length)
    (h_short : I.IsShort (12 * K)) (y : UnitPoint) :
    (taylorExtend f I K hK h_len h_short).secondDeriv y =
      deriv (deriv (taylorExtensionFun f I)) y :=
  rfl

end Kakeya.Cinematic
