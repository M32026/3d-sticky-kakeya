import MyLeanRepo.Kakeya.Cinematic.Statements
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Vertical scaling for bipartite tangency reductions

Positive scalar multiplication preserves the ratio `delta / t`, the
cinematic curvature inequalities, rectangle tangency, and the parameter
interval.  It supplies the harmless normalization from `t > 1` to `t = 1`
used before applying the paper's rectangle geometry.
-/

noncomputable section

namespace Kakeya.Cinematic

lemma continuousMap_dist_smul {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {s : ℝ} (hs : 0 ≤ s) (f g : C(α, ℝ)) :
    dist (s • f) (s • g) = s * dist f g := by
  have h_nonneg : 0 ≤ s * dist f g := by positivity
  have h1 : ∀ (x : α), dist ((s • f) x) ((s • g) x) ≤ s * dist f g := by
    intro x
    have h2 : dist ((s • f) x) ((s • g) x) =
        |s * f x - s * g x| := by rfl
    rw [h2]
    have h3 : |s * f x - s * g x| = s * |f x - g x| := by
      calc
        |s * f x - s * g x| = |s * (f x - g x)| := by ring_nf
        _ = |s| * |f x - g x| := by rw [abs_mul]
        _ = s * |f x - g x| := by rw [abs_of_nonneg hs]
    rw [h3]
    have h4 : dist (f x) (g x) ≤ dist f g :=
      (ContinuousMap.dist_le dist_nonneg).mp le_rfl x
    have h5 : |f x - g x| ≤ dist f g := by
      have h6 : dist (f x) (g x) = |f x - g x| := by rfl
      rw [h6] at h4
      exact h4
    gcongr
  have h5 : dist (s • f) (s • g) ≤ s * dist f g :=
    (ContinuousMap.dist_le h_nonneg).mpr h1
  by_cases h_s : s = 0
  · simp [h_s]
  · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm h_s)
    have h6 : ∀ (x : α),
        dist (f x) (g x) ≤ (1 / s) * dist (s • f) (s • g) := by
      intro x
      have h7 : dist (f x) (g x) = |f x - g x| := by rfl
      rw [h7]
      have h8 : dist ((s • f) x) ((s • g) x) ≤
          dist (s • f) (s • g) :=
        (ContinuousMap.dist_le dist_nonneg).mp le_rfl x
      have h9 : |s * f x - s * g x| ≤ dist (s • f) (s • g) := by
        have h10 : dist ((s • f) x) ((s • g) x) =
            |s * f x - s * g x| := by rfl
        rw [h10] at h8
        exact h8
      have h11 : s * |f x - g x| = |s * f x - s * g x| := by
        calc
          s * |f x - g x| = |s| * |f x - g x| := by
            rw [abs_of_nonneg hs]
          _ = |s * (f x - g x)| := by rw [← abs_mul]
          _ = |s * f x - s * g x| := by ring_nf
      have h12 : s * |f x - g x| ≤ dist (s • f) (s • g) := by
        rw [h11]
        exact h9
      calc
        |f x - g x| = (s * |f x - g x|) / s := by
          field_simp [hs_pos.ne']
        _ ≤ dist (s • f) (s • g) / s := by gcongr
        _ = (1 / s) * dist (s • f) (s • g) := by ring
    have h14 : 0 ≤ (1 / s) * dist (s • f) (s • g) := by positivity
    have h15 : dist f g ≤ (1 / s) * dist (s • f) (s • g) :=
      (ContinuousMap.dist_le h14).mpr h6
    have h16 : s * dist f g ≤ dist (s • f) (s • g) := by
      calc
        s * dist f g ≤
            s * ((1 / s) * dist (s • f) (s • g)) := by gcongr
        _ = dist (s • f) (s • g) := by
          field_simp [hs_pos.ne']
    exact le_antisymm h5 h16

def C2Function.smul (s : ℝ) (f : C2Function) : C2Function :=
  { value := s • f.value
    firstDeriv := s • f.firstDeriv
    secondDeriv := s • f.secondDeriv
    hasExtension := by
      rcases f.hasExtension with ⟨e, he_diff, h1, h2, h3⟩
      let hdiff : ContDiff ℝ 2 e := he_diff
      have hderiv : Differentiable ℝ e :=
        ContDiff.differentiable hdiff (by norm_num)
      have hderiv2 : Differentiable ℝ (deriv e) :=
        ContDiff.differentiable_deriv_two hdiff
      refine ⟨s • e, ?_, ?_, ?_, ?_⟩
      · exact hdiff.const_smul s
      · intro x
        simpa [h1] using rfl
      · intro x
        have hd : DifferentiableAt ℝ e x := hderiv.differentiableAt
        have h4 : deriv (s • e) x = s * deriv e x := by
          exact (hd.hasDerivAt.const_mul s).deriv
        rw [h4, h2 x]
        rfl
      · intro x
        have hderiv1 : deriv (s • e) = s • deriv e := by
          funext y
          have hd : DifferentiableAt ℝ e y := hderiv.differentiableAt
          exact (hd.hasDerivAt.const_mul s).deriv
        rw [hderiv1]
        have hd2 : DifferentiableAt ℝ (deriv e) x :=
          hderiv2.differentiableAt
        have h5 : deriv (s • deriv e) x = s * deriv (deriv e) x := by
          exact (hd2.hasDerivAt.const_mul s).deriv
        rw [h5, h3 x]
        rfl }

instance : SMul ℝ C2Function := ⟨C2Function.smul⟩

@[simp]
theorem C2Function.smul_value (s : ℝ) (f : C2Function) :
    (s • f).value = s • f.value := rfl

@[simp]
theorem C2Function.smul_firstDeriv (s : ℝ) (f : C2Function) :
    (s • f).firstDeriv = s • f.firstDeriv := rfl

@[simp]
theorem C2Function.smul_secondDeriv (s : ℝ) (f : C2Function) :
    (s • f).secondDeriv = s • f.secondDeriv := rfl

theorem C2Function.smul_apply (s : ℝ) (f : C2Function) (x : UnitPoint) :
    (s • f) x = s * f x := by
  simp [C2Function.smul]

lemma max_mul_nonneg {s a b : ℝ} (hs : 0 ≤ s) :
    max (s * a) (s * b) = s * max a b := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, max_eq_right (mul_le_mul_of_nonneg_left hab hs)]
  · rw [max_eq_left hba, max_eq_left (mul_le_mul_of_nonneg_left hba hs)]

theorem c2Distance_smul {s : ℝ} (hs : 0 ≤ s) (f g : C2Function) :
    c2Distance (s • f) (s • g) = s * c2Distance f g := by
  simp only [c2Distance_eq_dist]
  have hvalue :
      dist (s • f).value (s • g).value = s * dist f.value g.value :=
    continuousMap_dist_smul hs f.value g.value
  have hfirst :
      dist (s • f).firstDeriv (s • g).firstDeriv =
        s * dist f.firstDeriv g.firstDeriv :=
    continuousMap_dist_smul hs f.firstDeriv g.firstDeriv
  have hsecond :
      dist (s • f).secondDeriv (s • g).secondDeriv =
        s * dist f.secondDeriv g.secondDeriv :=
    continuousMap_dist_smul hs f.secondDeriv g.secondDeriv
  change
    max (dist (s • f).value (s • g).value)
        (max (dist (s • f).firstDeriv (s • g).firstDeriv)
          (dist (s • f).secondDeriv (s • g).secondDeriv)) =
      s * max (dist f.value g.value)
        (max (dist f.firstDeriv g.firstDeriv)
          (dist f.secondDeriv g.secondDeriv))
  rw [hvalue, hfirst, hsecond, max_mul_nonneg hs, max_mul_nonneg hs]

theorem jetGap_smul {s : ℝ} (hs : 0 ≤ s) (f g : C2Function)
    (x : UnitPoint) :
    jetGap (s • f) (s • g) x = s * jetGap f g x := by
  have habs : ∀ a b : ℝ, |s * a - s * b| = s * |a - b| := by
    intro a b
    calc
      |s * a - s * b| = |s * (a - b)| := by ring_nf
      _ = |s| * |a - b| := by rw [abs_mul]
      _ = s * |a - b| := by rw [abs_of_nonneg hs]
  have h1 : |(s • f) x - (s • g) x| = s * |f x - g x| := by
    rw [C2Function.smul_apply, C2Function.smul_apply]
    exact habs (f x) (g x)
  have h2 :
      |(s • f).firstDeriv x - (s • g).firstDeriv x| =
        s * |f.firstDeriv x - g.firstDeriv x| :=
    habs (f.firstDeriv x) (g.firstDeriv x)
  have h3 :
      |(s • f).secondDeriv x - (s • g).secondDeriv x| =
        s * |f.secondDeriv x - g.secondDeriv x| :=
    habs (f.secondDeriv x) (g.secondDeriv x)
  simp only [jetGap]
  rw [h1, h2, h3]
  ring

theorem HasCinematicCurvature.smul {K : ℝ} {family : Set C2Function}
    (h : HasCinematicCurvature family K)
    {s : ℝ} (hs_pos : 0 < s) (hs_le : s ≤ 1) :
    HasCinematicCurvature (Set.image (fun f => s • f) family) K := by
  constructor
  · rintro f ⟨f', hf', rfl⟩ g ⟨g', hg', rfl⟩
    rw [c2Distance_smul hs_pos.le]
    calc
      s * c2Distance f' g' ≤ s * K := by gcongr; exact h.1 hf' hg'
      _ ≤ 1 * K := by
        gcongr
        exact (dist_nonneg.trans (h.1 hf' hg')).trans' (by positivity)
      _ = K := one_mul K
  · rintro f ⟨f', hf', rfl⟩ g ⟨g', hg', rfl⟩ x
    rw [c2Distance_smul hs_pos.le, jetGap_smul hs_pos.le]
    nlinarith [h.2 hf' hg' x]

namespace CurvilinearRectangle

def smul {δ t : ℝ} (s : ℝ) (hs : 0 < s)
    (R : CurvilinearRectangle δ t) :
    CurvilinearRectangle (s * δ) (s * t) :=
  { function := s • R.function
    interval := R.interval
    interval_length := by
      rw [R.interval_length]
      congr 1
      field_simp [hs.ne'] }

end CurvilinearRectangle

theorem CurvilinearRectangle.IsLambdaTangent.smul
    {δ t : ℝ} {R : CurvilinearRectangle δ t}
    {f : C2Function} {lambda : ℝ} {s : ℝ}
    (hs : 0 < s) (h : R.IsLambdaTangent f lambda) :
    (R.smul s hs).IsLambdaTangent (s • f) lambda := by
  intro p hp
  have h1 : p.1 ∈ (R.smul s hs).interval.carrier := hp.1
  have hR_scaled : (s • R.function) p.1 = s * R.function p.1 :=
    C2Function.smul_apply s R.function p.1
  have hq_in_R : |p.2 / s - R.function p.1| ≤ δ := by
    have h5 : |p.2 - (s • R.function) p.1| ≤ s * δ := hp.2
    rw [hR_scaled] at h5
    have h7 :
        |p.2 - s * R.function p.1| =
          s * |p.2 / s - R.function p.1| := by
      rw [show p.2 - s * R.function p.1 =
          s * (p.2 / s - R.function p.1) by
        field_simp [hs.ne']]
      rw [abs_mul, abs_of_pos hs]
    rw [h7] at h5
    exact le_of_mul_le_mul_left h5 hs
  let q : UnitPoint × ℝ := (p.1, p.2 / s)
  have hq_carrier : q ∈ R.carrier := ⟨h1, hq_in_R⟩
  have hq_tangent : |q.2 - f q.1| ≤ lambda * δ := h q hq_carrier
  rw [C2Function.smul_apply]
  have h10 :
      |p.2 - s * f p.1| = s * |p.2 / s - f p.1| := by
    rw [show p.2 - s * f p.1 = s * (p.2 / s - f p.1) by
      field_simp [hs.ne']]
    rw [abs_mul, abs_of_pos hs]
  rw [h10]
  have h13 :
      s * |p.2 / s - f p.1| ≤ s * (lambda * δ) := by
    gcongr
  simpa [mul_assoc, mul_left_comm, mul_comm] using h13

theorem CurvilinearRectangle.IsOverCentralQuarterOf.smul
    {δ t : ℝ} {R : CurvilinearRectangle δ t}
    {I : ParameterInterval} {s : ℝ} (hs : 0 < s)
    (h : R.IsOverCentralQuarterOf I) :
    (R.smul s hs).IsOverCentralQuarterOf I :=
  h

end Kakeya.Cinematic
