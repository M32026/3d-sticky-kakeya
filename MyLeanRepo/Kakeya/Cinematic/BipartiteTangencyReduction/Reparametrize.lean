import MyLeanRepo.Kakeya.Cinematic.Geometry
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Reparametrize C2Functions over a ParameterInterval

Given `f : C2Function` and `I : ParameterInterval`, produce `f.reparam I`
whose value at `x` is `f(I.left + x * I.length)`.  The derivatives scale by
`I.length` and `I.length ^ 2` respectively.
-/

noncomputable section

namespace Kakeya.Cinematic

open Set

namespace ParameterInterval

def reparamPhi (I : ParameterInterval) (x : ℝ) : ℝ :=
  I.left + x * I.length

lemma reparamPhi_mem_unitInterval (I : ParameterInterval) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    I.reparamPhi x ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 : 0 ≤ x := hx.1
  have h2 : x ≤ 1 := hx.2
  have h3 : 0 ≤ I.length := I.length_nonneg
  have h4 : 0 ≤ I.left := I.left_mem.1
  have h5 : I.right ≤ 1 := I.right_mem.2
  have h6 : 0 ≤ x * I.length := by positivity
  have h7 : x * I.length ≤ I.length := by nlinarith
  have h8 : I.left + x * I.length ≤ I.right := by
    calc
      I.left + x * I.length ≤ I.left + I.length := by gcongr
      _ = I.right := by
        have h9 : I.length = I.right - I.left := by rfl
        rw [h9] <;> ring
  have h10 : 0 ≤ I.left + x * I.length := add_nonneg h4 h6
  have h11 : I.left + x * I.length ≤ 1 := le_trans h8 h5
  exact ⟨h10, h11⟩

lemma reparamPhi_continuous (I : ParameterInterval) : Continuous I.reparamPhi := by
  have h : Continuous (fun x : ℝ => I.left + x * I.length) := by fun_prop
  exact h

end ParameterInterval

namespace C2Function

/-- The point map `x ↦ I.left + x * I.length` on UnitPoint. -/
def phiMap (I : ParameterInterval) (x : UnitPoint) : UnitPoint :=
  ⟨I.reparamPhi (x : ℝ), I.reparamPhi_mem_unitInterval x.property⟩

lemma phiMap_continuous (I : ParameterInterval) : Continuous (phiMap I) := by
  have h1 : Continuous (fun x : UnitPoint => I.reparamPhi (x : ℝ)) :=
    I.reparamPhi_continuous.comp (continuous_induced_dom)
  have h2 : ∀ (x : UnitPoint), I.reparamPhi (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    fun x => I.reparamPhi_mem_unitInterval x.property
  exact Continuous.subtype_mk h1 h2

private lemma pointwise_bound_dist {f g : C(UnitPoint, ℝ)} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ (x : UnitPoint), |f x - g x| ≤ M) : dist f g ≤ M := by
  have h' : ‖f - g‖ ≤ M := by
    rw [ContinuousMap.norm_le (f - g) hM]
    intro x; simpa [Real.norm_eq_abs] using h x
  have hdist : dist f g = ‖f - g‖ := by rw [dist_eq_norm] <;> rfl
  rw [hdist]; exact h'

/-- Reparametrize f over interval I. -/
def reparam (f : C2Function) (I : ParameterInterval) : C2Function :=
  let phi := phiMap I
  let v : C(UnitPoint, ℝ) :=
    ⟨fun x => f.value (phi x), by
      have hc : Continuous phi := phiMap_continuous I
      exact f.value.continuous.comp hc⟩
  let d1 : C(UnitPoint, ℝ) :=
    ⟨fun x => I.length * f.firstDeriv (phi x), by
      have hc : Continuous phi := phiMap_continuous I
      fun_prop⟩
  let d2 : C(UnitPoint, ℝ) :=
    ⟨fun x => I.length ^ 2 * f.secondDeriv (phi x), by
      have hc : Continuous phi := phiMap_continuous I
      fun_prop⟩
  let g : ℝ → ℝ := fun y => f.extension (I.reparamPhi y)
  have h_cd : ContDiff ℝ 2 f.extension :=
    (Classical.choose_spec f.hasExtension).1
  have hg_cd : ContDiff ℝ 2 g :=
    h_cd.comp (contDiff_const.add (contDiff_id.mul contDiff_const))
  have h_f_diff : Differentiable ℝ f.extension :=
    h_cd.differentiable (by norm_num)
  have h_f1_cd : ContDiff ℝ 1 (deriv f.extension) :=
    h_cd.deriv'
  have h_f1_diff : Differentiable ℝ (deriv f.extension) :=
    h_f1_cd.differentiable (by norm_num)
  have h_affine : ∀ (z : ℝ), HasDerivAt I.reparamPhi I.length z := by
    intro z
    have h_eq : I.reparamPhi = (fun y : ℝ => I.length * y + I.left) := by
      funext y; simp [ParameterInterval.reparamPhi] <;> ring
    rw [h_eq]
    have h1 : HasDerivAt (fun y : ℝ => I.length * y) I.length z := by
      simpa [mul_one] using HasDerivAt.const_mul I.length (hasDerivAt_id z)
    exact h1.add_const I.left
  have h_deriv1 : ∀ (z : ℝ),
      HasDerivAt g (I.length * deriv f.extension (I.reparamPhi z)) z := by
    intro z
    have h_fa : DifferentiableAt ℝ f.extension (I.reparamPhi z) :=
      h_f_diff (I.reparamPhi z)
    have h_comp : HasDerivAt (f.extension ∘ I.reparamPhi)
        (deriv f.extension (I.reparamPhi z) * I.length) z :=
      h_fa.hasDerivAt.comp z (h_affine z)
    have h_func : (f.extension ∘ I.reparamPhi) = g := by
      funext y; rfl
    have h_deriv_eq : deriv f.extension (I.reparamPhi z) * I.length =
        I.length * deriv f.extension (I.reparamPhi z) := by ring
    rw [h_func] at h_comp
    rw [h_deriv_eq] at h_comp
    exact h_comp
  let g1 : ℝ → ℝ := fun y => I.length * deriv f.extension (I.reparamPhi y)
  have hg1_eq : deriv g = g1 := by
    funext y
    exact (h_deriv1 y).deriv
  have h_deriv2 : ∀ (z : ℝ),
      HasDerivAt g1 (I.length ^ 2 * deriv (deriv f.extension) (I.reparamPhi z)) z := by
    intro z
    have h_f1a : DifferentiableAt ℝ (deriv f.extension) (I.reparamPhi z) :=
      h_f1_diff (I.reparamPhi z)
    have h_inner : HasDerivAt (fun y => deriv f.extension (I.reparamPhi y))
        (deriv (deriv f.extension) (I.reparamPhi z) * I.length) z :=
      h_f1a.hasDerivAt.comp z (h_affine z)
    have h_cm : HasDerivAt (fun y => I.length * deriv f.extension (I.reparamPhi y))
        (I.length * (deriv (deriv f.extension) (I.reparamPhi z) * I.length)) z :=
      HasDerivAt.const_mul I.length h_inner
    have h_final_deriv : I.length * (deriv (deriv f.extension) (I.reparamPhi z) * I.length) =
        I.length ^ 2 * deriv (deriv f.extension) (I.reparamPhi z) := by ring
    rw [h_final_deriv] at h_cm
    exact h_cm
  { value := v
    firstDeriv := d1
    secondDeriv := d2
    hasExtension := by
      refine ⟨g, hg_cd, ?_, ?_, ?_⟩
      · intro x
        have h_phi : (phiMap I x : ℝ) = I.reparamPhi (x : ℝ) := by
          simp [phiMap, ParameterInterval.reparamPhi] <;> rfl
        have h2 : f.extension (↑(phiMap I x)) = f.value (phiMap I x) :=
          f.extension_eq_value (phiMap I x)
        rw [h_phi] at h2
        exact h2
      · intro x
        have h_eq : deriv g (x : ℝ) = I.length * deriv f.extension (I.reparamPhi (x : ℝ)) := by
          rw [hg1_eq] <;> rfl
        have h_phi : (phiMap I x : ℝ) = I.reparamPhi (x : ℝ) := by
          simp [phiMap, ParameterInterval.reparamPhi] <;> rfl
        have h9 : deriv f.extension (I.reparamPhi (x : ℝ)) = f.firstDeriv (phiMap I x) := by
          have h_tmp := f.deriv_extension_eq_firstDeriv (phiMap I x)
          rw [h_phi] at h_tmp
          exact h_tmp
        rw [h_eq, h9] <;> rfl
      · intro x
        have h_deriv2_x := h_deriv2 (x : ℝ)
        have h_deriv_g1 : HasDerivAt (deriv g)
            (I.length ^ 2 * deriv (deriv f.extension) (I.reparamPhi (x : ℝ))) (x : ℝ) := by
          convert h_deriv2_x using 1
        have h_eq2 : deriv (deriv g) (x : ℝ) =
            I.length ^ 2 * deriv (deriv f.extension) (I.reparamPhi (x : ℝ)) :=
          h_deriv_g1.deriv
        have h_phi : (phiMap I x : ℝ) = I.reparamPhi (x : ℝ) := by
          simp [phiMap, ParameterInterval.reparamPhi] <;> rfl
        have h10 : deriv (deriv f.extension) (I.reparamPhi (x : ℝ)) =
            f.secondDeriv (phiMap I x) := by
          have h_tmp := f.secondDeriv_extension_eq_secondDeriv (phiMap I x)
          rw [h_phi] at h_tmp
          exact h_tmp
        have h_phi2 : phi x = phiMap I x := by rfl
        have h_d2 : d2 x = I.length ^ 2 * f.secondDeriv (phiMap I x) := by
          have h1 : d2 x = I.length ^ 2 * f.secondDeriv (phi x) := by rfl
          rw [h1, h_phi2]
        rw [h_eq2, h10, h_d2] }

@[simp] lemma reparam_apply (f : C2Function) (I : ParameterInterval) (x : UnitPoint) :
    (f.reparam I) x = f (phiMap I x) := by rfl

@[simp] lemma reparam_firstDeriv (f : C2Function) (I : ParameterInterval) (x : UnitPoint) :
    (f.reparam I).firstDeriv x = I.length * f.firstDeriv (phiMap I x) := by rfl

@[simp] lemma reparam_secondDeriv (f : C2Function) (I : ParameterInterval) (x : UnitPoint) :
    (f.reparam I).secondDeriv x = I.length ^ 2 * f.secondDeriv (phiMap I x) := by rfl

lemma reparam_intersection_iff (f g : C2Function) (I : ParameterInterval) (x : UnitPoint) :
    (f.reparam I) x = (g.reparam I) x ↔
      f (phiMap I x) = g (phiMap I x) := by
  simp [reparam_apply]

lemma reparam_deriv_eq_iff (f g : C2Function) (I : ParameterInterval)
    (hI : 0 < I.length) (x : UnitPoint) :
    (f.reparam I).firstDeriv x = (g.reparam I).firstDeriv x ↔
      f.firstDeriv (phiMap I x) = g.firstDeriv (phiMap I x) := by
  simp [reparam_firstDeriv, mul_eq_mul_left_iff, hI.ne']

lemma reparam_transverse_iff (f g : C2Function) (I : ParameterInterval)
    (hI : 0 < I.length) (x : UnitPoint) :
    (f.reparam I).firstDeriv x ≠ (g.reparam I).firstDeriv x ↔
      f.firstDeriv (phiMap I x) ≠ g.firstDeriv (phiMap I x) := by
  exact (reparam_deriv_eq_iff f g I hI x).not

lemma reparam_c2Distance_le (f g : C2Function) (I : ParameterInterval) :
    c2Distance (f.reparam I) (g.reparam I) ≤ max 1 (I.length ^ 2) * c2Distance f g := by
  let M := max 1 (I.length ^ 2)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM2 : I.length ^ 2 ≤ M := le_max_right _ _
  have hM_nonneg : 0 ≤ M := by linarith
  let phi := phiMap I
  have h_val : dist (f.reparam I).value (g.reparam I).value ≤ M * dist f.value g.value := by
    have h : ∀ (x : UnitPoint), |(f.reparam I) x - (g.reparam I) x| ≤ M * dist f.value g.value := by
      intro x
      let y := phi x
      have h4 : dist (f.value y) (g.value y) ≤ dist f.value g.value :=
        ContinuousMap.dist_apply_le_dist y
      have h5 : |f.value y - g.value y| = dist (f.value y) (g.value y) := by
        simp [Real.dist_eq]
      have h6 : |f.value y - g.value y| ≤ dist f.value g.value := by
        rw [h5]; exact h4
      have h_y_eq : y = phiMap I x := by rfl
      have h7 : (f.reparam I) x - (g.reparam I) x = f.value y - g.value y := by
        have h71 : (f.reparam I) x = f.value y := by
          calc
            (f.reparam I) x = f (phiMap I x) := reparam_apply f I x
            _ = f.value (phiMap I x) := by rfl
            _ = f.value y := by rw [h_y_eq]
        have h72 : (g.reparam I) x = g.value y := by
          calc
            (g.reparam I) x = g (phiMap I x) := reparam_apply g I x
            _ = g.value (phiMap I x) := by rfl
            _ = g.value y := by rw [h_y_eq]
        rw [h71, h72]
      rw [h7]
      have h8 : |f.value y - g.value y| ≤ M * |f.value y - g.value y| :=
        le_mul_of_one_le_left (abs_nonneg _) hM1
      have h9 : M * |f.value y - g.value y| ≤ M * dist f.value g.value :=
        mul_le_mul_of_nonneg_left h6 (by linarith)
      exact le_trans h8 h9
    exact pointwise_bound_dist (by positivity) h
  have h_deriv1 : dist (f.reparam I).firstDeriv (g.reparam I).firstDeriv ≤
      M * dist f.firstDeriv g.firstDeriv := by
    have h : ∀ (x : UnitPoint),
        |(f.reparam I).firstDeriv x - (g.reparam I).firstDeriv x| ≤
        M * dist f.firstDeriv g.firstDeriv := by
      intro x
      let y := phi x
      have h4 : dist (f.firstDeriv y) (g.firstDeriv y) ≤ dist f.firstDeriv g.firstDeriv :=
        ContinuousMap.dist_apply_le_dist y
      have h5 : |f.firstDeriv y - g.firstDeriv y| = dist (f.firstDeriv y) (g.firstDeriv y) := by
        simp [Real.dist_eq]
      have h6 : |f.firstDeriv y - g.firstDeriv y| ≤ dist f.firstDeriv g.firstDeriv := by
        rw [h5]; exact h4
      have hlen : |I.length| ≤ M := by
        have h1 : 0 ≤ I.length := I.length_nonneg
        have h2 : |I.length| = I.length := abs_of_nonneg h1
        rw [h2]
        by_cases h : I.length ≤ 1
        · linarith [hM1]
        · have h3 : I.length ≤ I.length ^ 2 := by nlinarith
          linarith [hM2]
      have h_y_eq : y = phiMap I x := by rfl
      have h_diff : (f.reparam I).firstDeriv x - (g.reparam I).firstDeriv x =
          I.length * (f.firstDeriv y - g.firstDeriv y) := by
        have h1 : (f.reparam I).firstDeriv x = I.length * f.firstDeriv y := by
          rw [reparam_firstDeriv, h_y_eq]
        have h2 : (g.reparam I).firstDeriv x = I.length * g.firstDeriv y := by
          rw [reparam_firstDeriv, h_y_eq]
        rw [h1, h2] <;> ring
      rw [h_diff]
      calc
        |I.length * (f.firstDeriv y - g.firstDeriv y)|
          = |I.length| * |f.firstDeriv y - g.firstDeriv y| := by rw [abs_mul]
        _ ≤ M * |f.firstDeriv y - g.firstDeriv y| := by gcongr <;> exact hlen
        _ ≤ M * dist f.firstDeriv g.firstDeriv := by gcongr
    exact pointwise_bound_dist (by positivity) h
  have h_deriv2 : dist (f.reparam I).secondDeriv (g.reparam I).secondDeriv ≤
      M * dist f.secondDeriv g.secondDeriv := by
    have h : ∀ (x : UnitPoint),
        |(f.reparam I).secondDeriv x - (g.reparam I).secondDeriv x| ≤
        M * dist f.secondDeriv g.secondDeriv := by
      intro x
      let y := phi x
      have h4 : dist (f.secondDeriv y) (g.secondDeriv y) ≤ dist f.secondDeriv g.secondDeriv :=
        ContinuousMap.dist_apply_le_dist y
      have h5 : |f.secondDeriv y - g.secondDeriv y| = dist (f.secondDeriv y) (g.secondDeriv y) := by
        simp [Real.dist_eq]
      have h6 : |f.secondDeriv y - g.secondDeriv y| ≤ dist f.secondDeriv g.secondDeriv := by
        rw [h5]; exact h4
      have h_y_eq : y = phiMap I x := by rfl
      have h_diff : (f.reparam I).secondDeriv x - (g.reparam I).secondDeriv x =
          I.length ^ 2 * (f.secondDeriv y - g.secondDeriv y) := by
        have h1 : (f.reparam I).secondDeriv x = I.length ^ 2 * f.secondDeriv y := by
          rw [reparam_secondDeriv, h_y_eq]
        have h2 : (g.reparam I).secondDeriv x = I.length ^ 2 * g.secondDeriv y := by
          rw [reparam_secondDeriv, h_y_eq]
        rw [h1, h2] <;> ring
      rw [h_diff]
      have h_abs2 : |I.length ^ 2| = I.length ^ 2 := by
        rw [abs_of_nonneg] <;> positivity
      calc
        |I.length ^ 2 * (f.secondDeriv y - g.secondDeriv y)|
          = |I.length ^ 2| * |f.secondDeriv y - g.secondDeriv y| := by rw [abs_mul]
        _ = I.length ^ 2 * |f.secondDeriv y - g.secondDeriv y| := by rw [h_abs2]
        _ ≤ M * |f.secondDeriv y - g.secondDeriv y| := by gcongr <;> exact hM2
        _ ≤ M * dist f.secondDeriv g.secondDeriv := by gcongr
    exact pointwise_bound_dist (by positivity) h
  have h_expand : c2Distance (f.reparam I) (g.reparam I) =
      max (dist (f.reparam I).value (g.reparam I).value)
        (max (dist (f.reparam I).firstDeriv (g.reparam I).firstDeriv)
          (dist (f.reparam I).secondDeriv (g.reparam I).secondDeriv)) := by
    simp [c2Distance_eq_dist, C2Function.toJet, Prod.dist_eq] <;> rfl
  rw [h_expand]
  have h_orig : c2Distance f g =
      max (dist f.value g.value) (max (dist f.firstDeriv g.firstDeriv) (dist f.secondDeriv g.secondDeriv)) := by
    simp [c2Distance_eq_dist, C2Function.toJet, Prod.dist_eq] <;> rfl
  have h1 : dist (f.reparam I).value (g.reparam I).value ≤ M * c2Distance f g := by
    calc
      dist (f.reparam I).value (g.reparam I).value
        ≤ M * dist f.value g.value := h_val
      _ ≤ M * c2Distance f g := by
        rw [h_orig]; gcongr; apply le_max_left
  have h2 : dist (f.reparam I).firstDeriv (g.reparam I).firstDeriv ≤ M * c2Distance f g := by
    calc
      dist (f.reparam I).firstDeriv (g.reparam I).firstDeriv
        ≤ M * dist f.firstDeriv g.firstDeriv := h_deriv1
      _ ≤ M * c2Distance f g := by
        rw [h_orig]; gcongr; apply le_max_of_le_right; apply le_max_left
  have h3 : dist (f.reparam I).secondDeriv (g.reparam I).secondDeriv ≤ M * c2Distance f g := by
    calc
      dist (f.reparam I).secondDeriv (g.reparam I).secondDeriv
        ≤ M * dist f.secondDeriv g.secondDeriv := h_deriv2
      _ ≤ M * c2Distance f g := by
        rw [h_orig]; gcongr; apply le_max_of_le_right; apply le_max_right
  exact max_le h1 (max_le h2 h3)

/-- If two reparametrizations are equal, the original functions agree on the interval carrier. -/
lemma reparam_eq_on_carrier (f g : C2Function) (I : ParameterInterval)
    (h : f.reparam I = g.reparam I) (y : UnitPoint) (hy : y ∈ I.carrier) :
    f y = g y := by
  have h_y1 : I.left ≤ (y : ℝ) := hy.1
  have h_y2 : (y : ℝ) ≤ I.right := hy.2
  have hx : ∃ (x : UnitPoint), phiMap I x = y := by
    by_cases hI_pos : 0 < I.length
    · let x_val : ℝ := ((y : ℝ) - I.left) / I.length
      have hx0 : 0 ≤ x_val := by
        apply div_nonneg <;> linarith
      have hx1 : x_val ≤ 1 := by
        have h : (y : ℝ) - I.left ≤ I.length := by
          simp [ParameterInterval.length] <;> linarith
        exact (div_le_one hI_pos).mpr h
      let x : UnitPoint := ⟨x_val, ⟨hx0, hx1⟩⟩
      have hphi : I.reparamPhi (x : ℝ) = (y : ℝ) := by
        simp [x, ParameterInterval.reparamPhi, x_val] <;> field_simp [hI_pos.ne'] <;> ring
      have h_phi : phiMap I x = y := by
        apply Subtype.ext; simpa [phiMap] using hphi
      exact ⟨x, h_phi⟩
    · have h_not_pos : ¬(0 < I.length) := hI_pos
      have hI_eq : I.length = 0 := by linarith [I.length_nonneg]
      have h_right_eq : I.right = I.left := by
        have h_len : I.length = I.right - I.left := by rfl
        rw [h_len] at hI_eq
        linarith
      have h_y_eq : (y : ℝ) = I.left := by
        have h1 : I.left ≤ (y : ℝ) := hy.1
        have h2 : (y : ℝ) ≤ I.right := hy.2
        rw [h_right_eq] at h2
        linarith
      have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
      let x : UnitPoint := ⟨0, h01⟩
      have hphi : I.reparamPhi (x : ℝ) = (y : ℝ) := by
        have h : I.reparamPhi (x : ℝ) = I.left := by
          simp [x, ParameterInterval.reparamPhi, hI_eq] <;> ring
        rw [h, h_y_eq]
      have h_phi : phiMap I x = y := by
        apply Subtype.ext; simpa [phiMap] using hphi
      exact ⟨x, h_phi⟩
  rcases hx with ⟨x, h_phi⟩
  have h3 : (f.reparam I) x = (g.reparam I) x := by rw [h]
  simpa [reparam_apply, h_phi] using h3

end C2Function

end Kakeya.Cinematic
