import MyLeanRepo.Kakeya.Cinematic.Statements
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# PYZ Lemma 20: geometry of comparable rectangles

Proof uses CommonTangentRectangleStatement to obtain a C²-distance bound
proportional to t in the regime λt ≤ 1. When λt > 1, the crude diameter
bound suffices because 1/t < λ makes the extension error O(λ³δ).
-/

noncomputable section

open Set

namespace Kakeya.Cinematic

/-- General close-graph lemma: if |f-h| ≤ B on [a,b] and |f''-h''| ≤ K' on [0,1],
then |f-h| ≤ B + D*(2B/L + K'*L + K'*D) on [l,r], where [l,r] extends [a,b]
by at most D on each side. -/
lemma close_graph_lemma
    {f h : C2Function} {K B L D : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hLpos : 0 < L) (hD : 0 ≤ D)
    (hsecond : ∀ x : UnitPoint, |f.secondDeriv x - h.secondDeriv x| ≤ K)
    {a b l r : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (hl : 0 ≤ l) (hr : r ≤ 1) (hlr : l ≤ r)
    (hla : l ≤ a) (hbr : b ≤ r)
    (hLen : b - a = L)
    (hval : ∀ x : UnitPoint, a ≤ (x : ℝ) → (x : ℝ) ≤ b → |f x - h x| ≤ B)
    (hdist_l : a - l ≤ D) (hdist_r : r - b ≤ D) :
    ∀ (x : UnitPoint), l ≤ (x : ℝ) → (x : ℝ) ≤ r →
      |f x - h x| ≤ B + D * (2 * B / L + K * L + K * D) := by
  let φ := f.extension - h.extension
  let ψ := deriv φ
  have hf_cd : ContDiff ℝ 2 f.extension := C2Function.extension_contDiff f
  have hh_cd : ContDiff ℝ 2 h.extension := C2Function.extension_contDiff h
  have hφ_cd : ContDiff ℝ 2 φ := ContDiff.sub hf_cd hh_cd
  have hφ_diff : Differentiable ℝ φ := ContDiff.differentiable hφ_cd (by norm_num)
  have hψ_cd : ContDiff ℝ 1 ψ := ContDiff.deriv' hφ_cd
  have hψ_diff : Differentiable ℝ ψ := ContDiff.differentiable hψ_cd (by norm_num)
  have hf_diff : Differentiable ℝ f.extension := ContDiff.differentiable hf_cd (by norm_num)
  have hh_diff : Differentiable ℝ h.extension := ContDiff.differentiable hh_cd (by norm_num)
  have hf2_diff : Differentiable ℝ (deriv f.extension) := ContDiff.differentiable_deriv_two hf_cd
  have hh2_diff : Differentiable ℝ (deriv h.extension) := ContDiff.differentiable_deriv_two hh_cd
  have hχ_bound : ∀ z ∈ Set.Icc (0 : ℝ) 1, |deriv ψ z| ≤ K := by
    intro z hz
    let z' : UnitPoint := ⟨z, hz⟩
    have h_deriv1 : deriv φ = deriv f.extension - deriv h.extension := by
      funext x
      exact deriv_sub (hf_diff.differentiableAt) (hh_diff.differentiableAt)
    have h_deriv2 : deriv ψ = deriv (deriv f.extension) - deriv (deriv h.extension) := by
      funext x
      have hψ_eq : ψ = deriv f.extension - deriv h.extension := h_deriv1
      rw [hψ_eq]
      exact deriv_sub (hf2_diff.differentiableAt) (hh2_diff.differentiableAt)
    have h1 : deriv ψ z = f.secondDeriv z' - h.secondDeriv z' := by
      have h4 : deriv ψ z = (deriv (deriv f.extension) - deriv (deriv h.extension)) z := by
        rw [h_deriv2]
      rw [h4]
      have h5 : (deriv (deriv f.extension) - deriv (deriv h.extension)) z =
          deriv (deriv f.extension) z - deriv (deriv h.extension) z := by rfl
      rw [h5]
      have h6 : deriv (deriv f.extension) z = f.secondDeriv z' :=
        C2Function.secondDeriv_extension_eq_secondDeriv f z'
      have h7 : deriv (deriv h.extension) z = h.secondDeriv z' :=
        C2Function.secondDeriv_extension_eq_secondDeriv h z'
      rw [h6, h7] <;> rfl
    rw [h1]; exact hsecond z'
  have h_ab_lt : a < b := by linarith
  have hMVT : ∃ c ∈ Set.Ioo a b, ψ c = (φ b - φ a) / (b - a) :=
    exists_deriv_eq_slope φ h_ab_lt hφ_diff.continuous.continuousOn hφ_diff.differentiableOn
  rcases hMVT with ⟨c, hc, hc_eq⟩
  have hac : a < c := hc.1
  have hcb : c < b := hc.2
  have hc_in : c ∈ Set.Icc a b := ⟨hac.le, hcb.le⟩
  have hc01 : 0 ≤ c ∧ c ≤ 1 := ⟨by linarith, by linarith⟩
  let c' : UnitPoint := ⟨c, hc01⟩
  let a' : UnitPoint := ⟨a, ⟨ha, by linarith⟩⟩
  let b' : UnitPoint := ⟨b, ⟨by linarith, hb⟩⟩
  have hφ_a : φ a = f a' - h a' := by
    have h1 : f.extension a = f a' := C2Function.extension_eq_value f a'
    have h2 : h.extension a = h a' := C2Function.extension_eq_value h a'
    have h3 : φ a = f.extension a - h.extension a := by rfl
    rw [h3, h1, h2]
  have hφ_b : φ b = f b' - h b' := by
    have h1 : f.extension b = f b' := C2Function.extension_eq_value f b'
    have h2 : h.extension b = h b' := C2Function.extension_eq_value h b'
    have h3 : φ b = f.extension b - h.extension b := by rfl
    rw [h3, h1, h2]
  have h_φa : |φ a| ≤ B := by rw [hφ_a]; exact hval a' (by linarith) (by linarith)
  have h_φb : |φ b| ≤ B := by rw [hφ_b]; exact hval b' (by linarith) (by linarith)
  have hψ_c : |ψ c| ≤ 2 * B / L := by
    rw [hc_eq, hLen]
    calc
      |(φ b - φ a) / L| = |φ b - φ a| / L := by rw [abs_div, abs_of_pos hLpos]
      _ ≤ (|φ b| + |φ a|) / L := by gcongr; exact abs_sub _ _
      _ ≤ (B + B) / L := by gcongr
      _ = 2 * B / L := by ring
  -- ψ is K-Lipschitz on Icc 0 1, using direct mean value inequality
  have hψ_lip : ∀ (x y : ℝ), x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      |ψ y - ψ x| ≤ K * |y - x| := by
    intro x y hx hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z _ => hψ_diff.differentiableAt)
      (fun z hz => by simpa [Real.norm_eq_abs] using hχ_bound z hz)
      (convex_Icc 0 1) hx hy
    simpa [Real.norm_eq_abs] using h
  have hz01 : ∀ z ∈ Set.Icc a b, z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨le_trans ha hz.1, le_trans hz.2 hb⟩
  have hc01' : c ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  -- Inner bound: |ψ z| ≤ 2B/L + K*L for z ∈ Icc a b
  have hψ_inner : ∀ z ∈ Set.Icc a b, |ψ z| ≤ 2 * B / L + K * L := by
    intro z hz
    have h2 : |ψ z - ψ c| ≤ K * |z - c| := by
      have h2' := hψ_lip z c (hz01 z hz) hc01'
      have h3 : |ψ c - ψ z| = |ψ z - ψ c| := by rw [abs_sub_comm]
      have h4 : |c - z| = |z - c| := by rw [abs_sub_comm]
      rw [h3, h4] at h2'; exact h2'
    have h3 : |z - c| ≤ b - a := by
      rw [abs_le]
      constructor <;> linarith [hz.1, hz.2, hc_in.1, hc_in.2]
    have h4 : |z - c| ≤ L := by
      rw [←hLen]; exact h3
    have h5 : |ψ z| ≤ |ψ c| + |ψ z - ψ c| := by
      have h6 := abs_add_le (ψ c) (ψ z - ψ c)
      have h7 : ψ c + (ψ z - ψ c) = ψ z := by ring
      rw [h7] at h6
      exact h6
    calc
      |ψ z| ≤ |ψ c| + |ψ z - ψ c| := h5
      _ ≤ 2 * B / L + K * |z - c| := by linarith
      _ ≤ 2 * B / L + K * L := by gcongr
  -- Outer bound: |ψ z| ≤ 2B/L + K*L + K*D for z ∈ Icc l r
  have hz01_outer : ∀ z ∈ Set.Icc l r, z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨le_trans hl hz.1, le_trans hz.2 hr⟩
  have ha01 : a ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hb01 : b ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hψ_outer : ∀ z ∈ Set.Icc l r, |ψ z| ≤ 2 * B / L + K * L + K * D := by
    intro z hz
    have hzl : l ≤ z := hz.1
    have hzr : z ≤ r := hz.2
    have hz01' : z ∈ Set.Icc (0 : ℝ) 1 := hz01_outer z hz
    by_cases h : z ∈ Set.Icc a b
    · have h4 : |ψ z| ≤ 2 * B / L + K * L := hψ_inner z h
      have h5 : 0 ≤ K * D := by positivity
      linarith
    · have h_left : z < a ∨ b < z := by
        by_contra h'
        push Not at h'
        have : z ∈ Set.Icc a b := ⟨h'.1, h'.2⟩
        exact h this
      rcases h_left with (hleft | hright)
      · -- z < a
        have h5 : |ψ z - ψ a| ≤ K * |z - a| := by
          have h5' := hψ_lip z a hz01' ha01
          have h6 : |ψ a - ψ z| = |ψ z - ψ a| := by rw [abs_sub_comm]
          have h7 : |a - z| = |z - a| := by rw [abs_sub_comm]
          rw [h6, h7] at h5'; exact h5'
        have h6 : a - z ≤ D := by linarith [hdist_l]
        have h7 : |z - a| = a - z := by
          rw [abs_of_neg (show z - a < 0 by linarith)] <;> linarith
        have h8 : |z - a| ≤ D := by linarith
        have h9 : |ψ a| ≤ 2 * B / L + K * L := hψ_inner a ⟨by linarith, by linarith⟩
        have h10 : |ψ z| ≤ |ψ a| + |ψ z - ψ a| := by
          have h11 := abs_add_le (ψ a) (ψ z - ψ a)
          have h12 : ψ a + (ψ z - ψ a) = ψ z := by ring
          rw [h12] at h11
          exact h11
        calc
          |ψ z| ≤ |ψ a| + |ψ z - ψ a| := h10
          _ ≤ (2 * B / L + K * L) + K * |z - a| := by gcongr
          _ ≤ (2 * B / L + K * L) + K * D := by gcongr
      · -- b < z
        have h5 : |ψ z - ψ b| ≤ K * |z - b| := by
          have h5' := hψ_lip z b hz01' hb01
          have h6 : |ψ b - ψ z| = |ψ z - ψ b| := by rw [abs_sub_comm]
          have h7 : |b - z| = |z - b| := by rw [abs_sub_comm]
          rw [h6, h7] at h5'; exact h5'
        have h6 : z - b ≤ D := by linarith [hdist_r]
        have h7 : |z - b| = z - b := by
          rw [abs_of_pos (show 0 < z - b by linarith)] <;> linarith
        have h8 : |z - b| ≤ D := by linarith
        have h9 : |ψ b| ≤ 2 * B / L + K * L := hψ_inner b ⟨by linarith, by linarith⟩
        have h10 : |ψ z| ≤ |ψ b| + |ψ z - ψ b| := by
          have h11 := abs_add_le (ψ b) (ψ z - ψ b)
          have h12 : ψ b + (ψ z - ψ b) = ψ z := by ring
          rw [h12] at h11
          exact h11
        calc
          |ψ z| ≤ |ψ b| + |ψ z - ψ b| := h10
          _ ≤ (2 * B / L + K * L) + K * |z - b| := by gcongr
          _ ≤ (2 * B / L + K * L) + K * D := by gcongr
  let M := 2 * B / L + K * L + K * D
  have hM_nonneg : 0 ≤ M := by positivity
  -- φ is M-Lipschitz on Icc l r
  have hφ_lip : ∀ (x y : ℝ), x ∈ Set.Icc l r → y ∈ Set.Icc l r →
      |φ y - φ x| ≤ M * |y - x| := by
    intro x y hx hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z _ => hφ_diff.differentiableAt)
      (fun z hz => by simpa [Real.norm_eq_abs] using hψ_outer z hz)
      (convex_Icc l r) hx hy
    simpa [Real.norm_eq_abs] using h
  intro x hxl hxr
  let y : ℝ := (x : ℝ)
  have hy : y ∈ Set.Icc l r := ⟨hxl, hxr⟩
  have hφ_y : φ y = f x - h x := by
    have h1 : f.extension y = f x := C2Function.extension_eq_value f x
    have h2 : h.extension y = h x := C2Function.extension_eq_value h x
    have h3 : φ y = f.extension y - h.extension y := by rfl
    rw [h3, h1, h2]
  by_cases h_in : y ∈ Set.Icc a b
  · -- y ∈ Icc a b
    have h10 : |φ y| ≤ B := by
      rw [hφ_y]; exact hval x h_in.1 h_in.2
    have h11 : |f x - h x| ≤ B := by
      rw [←hφ_y]; exact h10
    have h12 : 0 ≤ D * M := by positivity
    have h13 : |f x - h x| ≤ B + D * M := by
      calc |f x - h x| ≤ B := h11
           _ ≤ B + D * M := by linarith
    simpa [M] using h13
  · -- y ∉ Icc a b
    have h_left : y < a ∨ b < y := by
      by_contra h'
      push Not at h'
      have : y ∈ Set.Icc a b := ⟨h'.1, h'.2⟩
      exact h_in this
    rcases h_left with (hleft | hright)
    · -- y < a
      have ha_in : a ∈ Set.Icc l r := ⟨by linarith, by linarith⟩
      have h12 : |φ y - φ a| ≤ M * |y - a| := by
        have h12' := hφ_lip y a hy ha_in
        have h13 : |φ a - φ y| = |φ y - φ a| := by rw [abs_sub_comm]
        have h14 : |a - y| = |y - a| := by rw [abs_sub_comm]
        rw [h13, h14] at h12'; exact h12'
      have h13 : |y - a| ≤ D := by
        have h14 : a - y ≤ D := by linarith [hdist_l]
        have h15 : |y - a| = a - y := by
          rw [abs_of_neg (show y - a < 0 by linarith)] <;> linarith
        linarith
      have h16 : |φ a| ≤ B := by
        rw [hφ_a]; exact hval a' (by linarith) (by linarith)
      have h17 : |φ y| ≤ |φ a| + |φ y - φ a| := by
        have h18 := abs_add_le (φ a) (φ y - φ a)
        have h19 : φ a + (φ y - φ a) = φ y := by ring
        rw [h19] at h18
        exact h18
      have h18 : |φ y| ≤ B + M * D := by
        calc
          |φ y| ≤ |φ a| + |φ y - φ a| := h17
          _ ≤ B + M * |y - a| := by gcongr
          _ ≤ B + M * D := by gcongr
      have h19 : |f x - h x| ≤ B + M * D := by
        have h20 : |f x - h x| = |φ y| := by rw [hφ_y]
        rw [h20]; exact h18
      have h21 : B + M * D = B + D * M := by ring
      rw [h21] at h19
      simpa [M] using h19
    · -- b < y
      have hb_in : b ∈ Set.Icc l r := ⟨by linarith, by linarith⟩
      have h12 : |φ y - φ b| ≤ M * |y - b| := by
        have h12' := hφ_lip y b hy hb_in
        have h13 : |φ b - φ y| = |φ y - φ b| := by rw [abs_sub_comm]
        have h14 : |b - y| = |y - b| := by rw [abs_sub_comm]
        rw [h13, h14] at h12'; exact h12'
      have h13 : |y - b| ≤ D := by
        have h14 : y - b ≤ D := by linarith [hdist_r]
        have h15 : |y - b| = y - b := by
          rw [abs_of_pos (show 0 < y - b by linarith)] <;> linarith
        linarith
      have h16 : |φ b| ≤ B := by
        rw [hφ_b]; exact hval b' (by linarith) (by linarith)
      have h17 : |φ y| ≤ |φ b| + |φ y - φ b| := by
        have h18 := abs_add_le (φ b) (φ y - φ b)
        have h19 : φ b + (φ y - φ b) = φ y := by ring
        rw [h19] at h18
        exact h18
      have h18 : |φ y| ≤ B + M * D := by
        calc
          |φ y| ≤ |φ b| + |φ y - φ b| := h17
          _ ≤ B + M * |y - b| := by gcongr
          _ ≤ B + M * D := by gcongr
      have h19 : |f x - h x| ≤ B + M * D := by
        have h20 : |f x - h x| = |φ y| := by rw [hφ_y]
        rw [h20]; exact h18
      have h21 : B + M * D = B + D * M := by ring
      rw [h21] at h19
      simpa [M] using h19

lemma carrier_imp_interval {δ t : ℝ} (W : CurvilinearRectangle δ t)
    (p : UnitPoint × ℝ) (h : p ∈ W.carrier) :
    p.1 ∈ W.interval.carrier := by
  have h' : p.1 ∈ W.interval.carrier ∧ |p.2 - W.function p.1| ≤ δ := by
    simpa [CurvilinearRectangle.carrier, verticalNeighborhoodOn, Set.mem_setOf_eq] using h
  exact h'.1

lemma carrier_imp_bound {δ t : ℝ} (W : CurvilinearRectangle δ t)
    (p : UnitPoint × ℝ) (h : p ∈ W.carrier) :
    |p.2 - W.function p.1| ≤ δ := by
  have h' : p.1 ∈ W.interval.carrier ∧ |p.2 - W.function p.1| ≤ δ := by
    simpa [CurvilinearRectangle.carrier, verticalNeighborhoodOn, Set.mem_setOf_eq] using h
  exact h'.2

/-- The tangency parameter is non-negative whenever the centered carrier is nonempty. -/
lemma tangencyParameterOn_nonneg_of_point
    {I : ParameterInterval} {f g : C2Function} {x : UnitPoint}
    (hx : x ∈ I.centeredCarrier (1 / 2)) :
    0 ≤ tangencyParameterOn I f g := by
  let Sset := {r : ℝ | ∃ y ∈ I.centeredCarrier (1 / 2),
      r = |f y - g y| + |f.firstDeriv y - g.firstDeriv y|}
  have hS_nonempty : Sset.Nonempty := by
    refine' ⟨|f x - g x| + |f.firstDeriv x - g.firstDeriv x|, _⟩
    exact ⟨x, hx, rfl⟩
  have h4 : ∀ r ∈ Sset, 0 ≤ r := by
    intro r hr
    rcases hr with ⟨y, _, rfl⟩
    positivity
  exact le_csInf hS_nonempty h4

lemma distance_le_of_tangency_product_bound
    {delta tangency distance C t : ℝ}
    (hdelta : 0 < delta)
    (htangency : 0 ≤ tangency)
    (hdistance : 0 ≤ distance)
    (hproduct :
      (tangency + delta) * distance ≤ C * delta * t) :
    distance ≤ C * t := by
  have hscaled : delta * distance ≤ delta * (C * t) := by
    calc
      delta * distance
          ≤ (tangency + delta) * distance := by
            nlinarith [mul_nonneg htangency hdistance]
      _ ≤ C * delta * t := hproduct
      _ = delta * (C * t) := by ring
  exact le_of_mul_le_mul_left hscaled hdelta

def CommonTangentRectangleBound (K D C : ℝ) : Prop :=
  ∀ family : Set C2Function,
    IsCinematicFamily family K D →
    ∀ I : ParameterInterval, I.IsControlled K →
      ∀ delta t : ℝ, 0 < delta → delta ≤ t → t ≤ 1 →
        ∀ R : CurvilinearRectangle delta t,
          R.function ∈ family →
          R.IsOverCentralQuarterOf I →
          ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
            R.IsLambdaTangent f 5 →
            R.IsLambdaTangent g 5 →
            (tangencyParameterOn I f g + delta) * c2Distance f g ≤
              C * delta * t

lemma c2Distance_to_common_rectangle_small_scale
    {K D C delta t lambda : ℝ}
    {family : Set C2Function} {I : ParameterInterval}
    (hCommon : CommonTangentRectangleBound K D C)
    (hC : 0 ≤ C)
    (hFamily : IsCinematicFamily family K D)
    (hI : I.IsControlled K)
    (hdelta : 0 < delta) (hdt : delta ≤ t)
    (hlambda : 1 ≤ lambda) (hsmall : lambda * t ≤ 1)
    (Q : CurvilinearRectangle delta t)
    (W : CurvilinearRectangle (lambda * delta) t)
    (hQfam : Q.function ∈ family)
    (hWfam : W.function ∈ family)
    (hQquarter : Q.IsOverCentralQuarterOf I)
    (hQcont : Q.carrier ⊆ W.carrier) :
    c2Distance Q.function W.function ≤ C * lambda * t := by
  have ht : 0 < t := hdelta.trans_le hdt
  let delta' := lambda * delta
  let t' := lambda * t
  have hdelta'_pos : 0 < delta' := by
    dsimp only [delta']
    positivity
  have hdt' : delta' ≤ t' := by
    dsimp only [delta', t']
    gcongr
  have ht'_one : t' ≤ 1 := by
    simpa only [t'] using hsmall
  have hQvalue :
      ∀ x ∈ Q.interval.carrier,
        |Q.function x - W.function x| ≤ delta' := by
    intro x hx
    have hQgraph : (x, Q.function x) ∈ Q.carrier := by
      exact ⟨hx, by simpa using hdelta.le⟩
    have hWgraph := hQcont hQgraph
    simpa [delta'] using carrier_imp_bound W (x, Q.function x) hWgraph
  let Q' : CurvilinearRectangle delta' t' :=
    { function := Q.function
      interval := Q.interval
      interval_length := by
        have hratio : delta' / t' = delta / t := by
          dsimp only [delta', t']
          have hlambda_pos : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambda
          field_simp [ht.ne', hlambda_pos.ne']
        simpa [hratio] using Q.interval_length }
  have hQ'_quarter : Q'.IsOverCentralQuarterOf I := hQquarter
  have hQ'_tangent_self : Q'.IsLambdaTangent Q.function 5 := by
    intro p hp
    exact hp.2.trans (by nlinarith [hdelta'_pos])
  have hQ'_tangent_common : Q'.IsLambdaTangent W.function 5 := by
    intro p hp
    have hp_bound : |p.2 - Q.function p.1| ≤ delta' := hp.2
    have hgap := hQvalue p.1 hp.1
    calc
      |p.2 - W.function p.1| =
          |(p.2 - Q.function p.1) +
            (Q.function p.1 - W.function p.1)| := by
              congr 1
              ring
      _ ≤ |p.2 - Q.function p.1| +
          |Q.function p.1 - W.function p.1| := abs_add_le _ _
      _ ≤ delta' + delta' := by
        gcongr
      _ ≤ 5 * delta' := by nlinarith
  let qleft : UnitPoint := ⟨Q.interval.left, Q.interval.left_mem⟩
  have hleft_mem : qleft ∈ Q.interval.carrier := by
    have hleft :
        Q.interval.left ≤ (qleft : ℝ) ∧
          (qleft : ℝ) ≤ Q.interval.right := by
      simp only [qleft]
      exact ⟨le_rfl, Q.interval.left_le_right⟩
    simpa [ParameterInterval.carrier] using hleft
  have hcentered :
      qleft ∈ I.centeredCarrier (1 / 2) := by
    have hquarter := hQquarter hleft_mem
    simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq] at hquarter ⊢
    have hlength : 0 ≤ I.length := I.length_nonneg
    calc
      |(qleft : ℝ) - I.midpoint|
          ≤ (1 / 4 : ℝ) * I.length / 2 := hquarter
      _ ≤ (1 / 2 : ℝ) * I.length / 2 := by
        gcongr
        norm_num
  have htangency : 0 ≤ tangencyParameterOn I Q.function W.function :=
    tangencyParameterOn_nonneg_of_point hcentered
  by_cases heq : Q.function = W.function
  · rw [heq, c2Distance_eq_dist, dist_self]
    exact mul_nonneg (mul_nonneg hC (zero_le_one.trans hlambda)) ht.le
  · have hproduct :=
      hCommon family hFamily I hI delta' t'
        hdelta'_pos hdt' ht'_one Q'
        hQfam hQ'_quarter Q.function hQfam W.function hWfam heq
        hQ'_tangent_self hQ'_tangent_common
    have hdistance : 0 ≤ c2Distance Q.function W.function := by
      simp only [c2Distance_eq_dist]
      exact dist_nonneg
    have hbound : c2Distance Q.function W.function ≤ C * t' :=
      distance_le_of_tangency_product_bound
        hdelta'_pos htangency hdistance hproduct
    calc
      c2Distance Q.function W.function ≤ C * t' := hbound
      _ = C * lambda * t := by
        dsimp only [t']
        ring

lemma secondDeriv_sub_le_of_c2Distance_le
    {f h : C2Function} {bound : ℝ}
    (hdistance : c2Distance f h ≤ bound) :
    ∀ x : UnitPoint,
      |f.secondDeriv x - h.secondDeriv x| ≤ bound := by
  intro x
  exact (abs_secondDeriv_sub_le_c2Distance f h x).trans hdistance

lemma close_graph_of_c2Distance_le
    {f h : C2Function} {K B L D : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hLpos : 0 < L) (hD : 0 ≤ D)
    (hdistance : c2Distance f h ≤ K)
    {a b l r : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (hl : 0 ≤ l) (hr : r ≤ 1) (hlr : l ≤ r)
    (hla : l ≤ a) (hbr : b ≤ r)
    (hLen : b - a = L)
    (hval : ∀ x : UnitPoint, a ≤ (x : ℝ) → (x : ℝ) ≤ b → |f x - h x| ≤ B)
    (hdist_l : a - l ≤ D) (hdist_r : r - b ≤ D) :
    ∀ (x : UnitPoint), l ≤ (x : ℝ) → (x : ℝ) ≤ r →
      |f x - h x| ≤ B + D * (2 * B / L + K * L + K * D) := by
  exact close_graph_lemma hK hB hLpos hD
    (secondDeriv_sub_le_of_c2Distance_le hdistance)
    ha hb hab hl hr hlr hla hbr hLen hval hdist_l hdist_r

lemma graph_difference_of_common_bounds
    {f g h : C2Function} {l r bound target : ℝ}
    (hf :
      ∀ x : UnitPoint, l ≤ (x : ℝ) → (x : ℝ) ≤ r →
        |f x - h x| ≤ bound)
    (hg :
      ∀ x : UnitPoint, l ≤ (x : ℝ) → (x : ℝ) ≤ r →
        |g x - h x| ≤ bound)
    (hdouble : 2 * bound ≤ target) :
    ∀ x : UnitPoint, l ≤ (x : ℝ) → (x : ℝ) ≤ r →
      |f x - g x| ≤ target := by
  intro x hxl hxr
  have htriangle :
      |f x - g x| ≤ |f x - h x| + |h x - g x| := by
    have heq : f x - g x = (f x - h x) + (h x - g x) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hreverse : |h x - g x| = |g x - h x| := abs_sub_comm _ _
  rw [hreverse] at htriangle
  calc
    |f x - g x| ≤ |f x - h x| + |g x - h x| := htriangle
    _ ≤ bound + bound := by
      gcongr
      · exact hf x hxl hxr
      · exact hg x hxl hxr
    _ = 2 * bound := by ring
    _ ≤ target := hdouble

lemma graph_difference_of_c2Distance_bounds
    {f g h : C2Function}
    {K B L D aF bF aG bG l r bound target : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hLpos : 0 < L) (hD : 0 ≤ D)
    (hfDistance : c2Distance f h ≤ K)
    (hgDistance : c2Distance g h ≤ K)
    (haF : 0 ≤ aF) (hbF : bF ≤ 1) (habF : aF ≤ bF)
    (haG : 0 ≤ aG) (hbG : bG ≤ 1) (habG : aG ≤ bG)
    (hl : 0 ≤ l) (hr : r ≤ 1) (hlr : l ≤ r)
    (hlaF : l ≤ aF) (hbFr : bF ≤ r)
    (hlaG : l ≤ aG) (hbGr : bG ≤ r)
    (hLenF : bF - aF = L) (hLenG : bG - aG = L)
    (hvalF :
      ∀ x : UnitPoint, aF ≤ (x : ℝ) → (x : ℝ) ≤ bF →
        |f x - h x| ≤ B)
    (hvalG :
      ∀ x : UnitPoint, aG ≤ (x : ℝ) → (x : ℝ) ≤ bG →
        |g x - h x| ≤ B)
    (hdistF_l : aF - l ≤ D) (hdistF_r : r - bF ≤ D)
    (hdistG_l : aG - l ≤ D) (hdistG_r : r - bG ≤ D)
    (herror : B + D * (2 * B / L + K * L + K * D) ≤ bound)
    (hdouble : 2 * bound ≤ target) :
    ∀ x : UnitPoint, l ≤ (x : ℝ) → (x : ℝ) ≤ r →
      |f x - g x| ≤ target := by
  have hfClose := @close_graph_of_c2Distance_le f h K B L D
    hK hB hLpos hD hfDistance
    aF bF l r haF hbF habF hl hr hlr hlaF hbFr
    hLenF hvalF hdistF_l hdistF_r
  have hgClose := @close_graph_of_c2Distance_le g h K B L D
    hK hB hLpos hD hgDistance
    aG bG l r haG hbG habG hl hr hlr hlaG hbGr
    hLenG hvalG hdistG_l hdistG_r
  apply graph_difference_of_common_bounds
    (fun x hxl hxr => (hfClose x hxl hxr).trans herror)
    (fun x hxl hxr => (hgClose x hxl hxr).trans herror)
    hdouble

/-- Algebra bound for Case B (λt ≤ 1): the extension error is bounded by
(3 + 2*C₁)*λ³δ when the second derivative bound is K' = C₁*λ*t. -/
lemma comparable_rectangles_caseB_algebra
    {delta t lambda C₁ : ℝ}
    (hdelta : 0 < delta) (h_tpos : 0 < t) (hlambda : 1 ≤ lambda)
    (hC₁_pos : 0 < C₁)
    (K' : ℝ) (hK'_eq : K' = C₁ * lambda * t) :
    lambda * delta + Real.sqrt (lambda * delta / t) * (2 * (lambda * delta) / Real.sqrt (delta / t) + K' * Real.sqrt (delta / t) + K' * Real.sqrt (lambda * delta / t))
    ≤ (3 + 2 * C₁) * lambda^3 * delta := by
  set D := Real.sqrt (lambda * delta / t) with hD
  set L := Real.sqrt (delta / t) with hL
  have h_pos1 : 0 ≤ lambda * delta / t := by positivity
  have h_pos2 : 0 ≤ delta / t := by positivity
  have h_pos3 : 0 ≤ lambda := by linarith
  have h_div : D / L = Real.sqrt lambda := by
    rw [hD, hL]
    have h : Real.sqrt (lambda * delta / t) / Real.sqrt (delta / t) = Real.sqrt ((lambda * delta / t) / (delta / t)) := by
      rw [← Real.sqrt_div h_pos1 (delta / t)]
    rw [h]
    have h2 : (lambda * delta / t) / (delta / t) = lambda := by
      field_simp [h_tpos.ne', hdelta.ne'] <;> ring
    rw [h2]
  have h_DL : D * L = Real.sqrt lambda * (delta / t) := by
    rw [hD, hL]
    have h1 : Real.sqrt (lambda * delta / t) = Real.sqrt lambda * Real.sqrt (delta / t) := by
      have h2 : lambda * delta / t = lambda * (delta / t) := by ring
      have h3 : Real.sqrt (lambda * (delta / t)) = Real.sqrt lambda * Real.sqrt (delta / t) :=
        Real.sqrt_mul h_pos3 (delta / t)
      have h4 : Real.sqrt (lambda * delta / t) = Real.sqrt (lambda * (delta / t)) := by rw [h2]
      rw [h4]; exact h3
    rw [h1]
    have h3 : Real.sqrt (delta / t) * Real.sqrt (delta / t) = delta / t := by
      have h4 : Real.sqrt (delta / t) * Real.sqrt (delta / t) = (Real.sqrt (delta / t)) ^ 2 := by ring
      rw [h4, Real.sq_sqrt h_pos2]
    have h5 : (Real.sqrt lambda * Real.sqrt (delta / t)) * Real.sqrt (delta / t) = Real.sqrt lambda * (delta / t) := by
      calc
        (Real.sqrt lambda * Real.sqrt (delta / t)) * Real.sqrt (delta / t)
          = Real.sqrt lambda * (Real.sqrt (delta / t) * Real.sqrt (delta / t)) := by ring
        _ = Real.sqrt lambda * (delta / t) := by rw [h3]
    exact h5
  have h_D2 : D ^ 2 = lambda * delta / t := by
    rw [hD]; exact Real.sq_sqrt h_pos1
  have h_sqrt_le : Real.sqrt lambda ≤ lambda ^ 2 := by
    have h5 : Real.sqrt lambda ≤ Real.sqrt (lambda ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    have h6 : Real.sqrt (lambda ^ 2) = lambda := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h_pos3]
    have h7 : lambda ≤ lambda ^ 2 := by nlinarith
    rw [h6] at h5
    linarith
  have h1 : D * (2 * (lambda * delta) / L) = 2 * lambda * delta * Real.sqrt lambda := by
    have h : D * (2 * (lambda * delta) / L) = 2 * lambda * delta * (D / L) := by ring
    rw [h, h_div] <;> ring
  have h2 : D * (K' * L) = C₁ * lambda * Real.sqrt lambda * delta := by
    have h_eq : D * (K' * L) = K' * (D * L) := by ring
    rw [h_eq, h_DL, hK'_eq]
    field_simp [h_tpos.ne'] <;> ring
  have h3 : D * (K' * D) = C₁ * lambda ^ 2 * delta := by
    have h_eq : D * (K' * D) = K' * D ^ 2 := by ring
    rw [h_eq, h_D2, hK'_eq]
    field_simp [h_tpos.ne'] <;> ring
  have h4 : 2 * lambda * delta * Real.sqrt lambda ≤ 2 * lambda ^ 3 * delta := by
    have h5 : Real.sqrt lambda ≤ lambda ^ 2 := h_sqrt_le
    have h6 : 0 ≤ 2 * lambda * delta := by positivity
    calc
      2 * lambda * delta * Real.sqrt lambda
        ≤ 2 * lambda * delta * (lambda ^ 2) := by gcongr
      _ = 2 * lambda ^ 3 * delta := by ring
  have h5 : C₁ * lambda * Real.sqrt lambda * delta ≤ C₁ * lambda ^ 3 * delta := by
    have h6 : Real.sqrt lambda ≤ lambda ^ 2 := h_sqrt_le
    have h7 : 0 ≤ C₁ * lambda * delta := by positivity
    calc
      C₁ * lambda * Real.sqrt lambda * delta
        ≤ C₁ * lambda * (lambda ^ 2) * delta := by gcongr
      _ = C₁ * lambda ^ 3 * delta := by ring
  have h6 : C₁ * lambda ^ 2 * delta ≤ C₁ * lambda ^ 3 * delta := by
    have h7 : 0 ≤ C₁ * delta := by positivity
    have h8 : lambda ^ 2 ≤ lambda ^ 3 := by nlinarith
    gcongr
  have h7 : lambda * delta ≤ lambda ^ 3 * delta := by
    have h8 : 1 ≤ lambda ^ 2 := by nlinarith
    have h9 : 0 ≤ lambda * delta := by positivity
    calc
      lambda * delta
        = 1 * (lambda * delta) := by ring
      _ ≤ lambda ^ 2 * (lambda * delta) := by gcongr
      _ = lambda ^ 3 * delta := by ring
  have h_expand : D * (2 * (lambda * delta) / L + K' * L + K' * D)
      = D * (2 * (lambda * delta) / L) + D * (K' * L) + D * (K' * D) := by ring
  rw [h_expand, h1, h2, h3]
  linarith

/-- Algebra bound for Case A (λt > 1): the extension error is bounded by
(3 + 2*K)*λ³δ when the second derivative bound is K. -/
lemma comparable_rectangles_caseA_algebra
    {delta t lambda K : ℝ}
    (hdelta : 0 < delta) (h_tpos : 0 < t) (hlambda : 1 ≤ lambda)
    (hK : 0 ≤ K) (h_dtover_t : delta / t < lambda * delta) :
    lambda * delta + Real.sqrt (lambda * delta / t) * (2 * (lambda * delta) / Real.sqrt (delta / t) + K * Real.sqrt (delta / t) + K * Real.sqrt (lambda * delta / t))
    ≤ (3 + 2 * K) * lambda^3 * delta := by
  set D := Real.sqrt (lambda * delta / t) with hD
  set L := Real.sqrt (delta / t) with hL
  have h_pos1 : 0 ≤ lambda * delta / t := by positivity
  have h_pos2 : 0 ≤ delta / t := by positivity
  have h_pos3 : 0 ≤ lambda := by linarith
  have h_div : D / L = Real.sqrt lambda := by
    rw [hD, hL]
    have h : Real.sqrt (lambda * delta / t) / Real.sqrt (delta / t) = Real.sqrt ((lambda * delta / t) / (delta / t)) := by
      rw [← Real.sqrt_div h_pos1 (delta / t)]
    rw [h]
    have h2 : (lambda * delta / t) / (delta / t) = lambda := by
      field_simp [h_tpos.ne', hdelta.ne'] <;> ring
    rw [h2]
  have h_DL : D * L = Real.sqrt lambda * (delta / t) := by
    rw [hD, hL]
    have h1 : Real.sqrt (lambda * delta / t) = Real.sqrt lambda * Real.sqrt (delta / t) := by
      have h2 : lambda * delta / t = lambda * (delta / t) := by ring
      have h3 : Real.sqrt (lambda * (delta / t)) = Real.sqrt lambda * Real.sqrt (delta / t) :=
        Real.sqrt_mul h_pos3 (delta / t)
      have h4 : Real.sqrt (lambda * delta / t) = Real.sqrt (lambda * (delta / t)) := by rw [h2]
      rw [h4]; exact h3
    rw [h1]
    have h3 : Real.sqrt (delta / t) * Real.sqrt (delta / t) = delta / t := by
      have h4 : Real.sqrt (delta / t) * Real.sqrt (delta / t) = (Real.sqrt (delta / t)) ^ 2 := by ring
      rw [h4, Real.sq_sqrt h_pos2]
    have h5 : (Real.sqrt lambda * Real.sqrt (delta / t)) * Real.sqrt (delta / t) = Real.sqrt lambda * (delta / t) := by
      calc
        (Real.sqrt lambda * Real.sqrt (delta / t)) * Real.sqrt (delta / t)
          = Real.sqrt lambda * (Real.sqrt (delta / t) * Real.sqrt (delta / t)) := by ring
        _ = Real.sqrt lambda * (delta / t) := by rw [h3]
    exact h5
  have h_D2 : D ^ 2 = lambda * delta / t := by
    rw [hD]; exact Real.sq_sqrt h_pos1
  have h_sqrt_le : Real.sqrt lambda ≤ lambda ^ 2 := by
    have h5 : Real.sqrt lambda ≤ Real.sqrt (lambda ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    have h6 : Real.sqrt (lambda ^ 2) = lambda := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h_pos3]
    have h7 : lambda ≤ lambda ^ 2 := by nlinarith
    rw [h6] at h5
    linarith
  have h1 : D * (2 * (lambda * delta) / L) = 2 * lambda * delta * Real.sqrt lambda := by
    have h : D * (2 * (lambda * delta) / L) = 2 * lambda * delta * (D / L) := by ring
    rw [h, h_div] <;> ring
  have h2 : D * (K * L) = K * Real.sqrt lambda * (delta / t) := by
    have h_eq : D * (K * L) = K * (D * L) := by ring
    rw [h_eq, h_DL] <;> ring
  have h3 : D * (K * D) = K * (lambda * delta / t) := by
    have h_eq : D * (K * D) = K * D ^ 2 := by ring
    rw [h_eq, h_D2] <;> ring
  have h4 : 2 * lambda * delta * Real.sqrt lambda ≤ 2 * lambda ^ 3 * delta := by
    have h5 : Real.sqrt lambda ≤ lambda ^ 2 := h_sqrt_le
    have h6 : 0 ≤ 2 * lambda * delta := by positivity
    calc
      2 * lambda * delta * Real.sqrt lambda
        ≤ 2 * lambda * delta * (lambda ^ 2) := by gcongr
      _ = 2 * lambda ^ 3 * delta := by ring
  have h5 : K * Real.sqrt lambda * (delta / t) ≤ K * lambda ^ 3 * delta := by
    have h6 : Real.sqrt lambda * (delta / t) ≤ lambda ^ 3 * delta := by
      have h7 : delta / t ≤ lambda * delta := h_dtover_t.le
      have h8 : Real.sqrt lambda ≤ lambda ^ 2 := h_sqrt_le
      have h9 : 0 ≤ Real.sqrt lambda := by positivity
      calc
        Real.sqrt lambda * (delta / t)
          ≤ Real.sqrt lambda * (lambda * delta) := by gcongr
        _ = lambda * Real.sqrt lambda * delta := by ring
        _ ≤ lambda * (lambda ^ 2) * delta := by gcongr
        _ = lambda ^ 3 * delta := by ring
    have h10 : K * (Real.sqrt lambda * (delta / t)) ≤ K * (lambda ^ 3 * delta) := mul_le_mul_of_nonneg_left h6 hK
    have h11 : K * Real.sqrt lambda * (delta / t) = K * (Real.sqrt lambda * (delta / t)) := by ring
    have h12 : K * lambda ^ 3 * delta = K * (lambda ^ 3 * delta) := by ring
    rw [h11, h12]; exact h10
  have h6 : K * (lambda * delta / t) ≤ K * lambda ^ 3 * delta := by
    have h7 : lambda * delta / t ≤ lambda ^ 2 * delta := by
      have h8 : delta / t ≤ lambda * delta := h_dtover_t.le
      calc
        lambda * delta / t
          = lambda * (delta / t) := by ring
        _ ≤ lambda * (lambda * delta) := by gcongr
        _ = lambda ^ 2 * delta := by ring
    have h10 : K * (lambda * delta / t) ≤ K * (lambda ^ 2 * delta) := mul_le_mul_of_nonneg_left h7 hK
    have h11 : lambda ^ 2 * delta ≤ lambda ^ 3 * delta := by
      have h12 : 1 ≤ lambda := hlambda
      have h13 : 0 ≤ delta := by positivity
      nlinarith
    have h14 : K * (lambda ^ 2 * delta) ≤ K * (lambda ^ 3 * delta) := mul_le_mul_of_nonneg_left h11 hK
    have h15 : K * lambda ^ 3 * delta = K * (lambda ^ 3 * delta) := by ring
    rw [h15]
    exact le_trans h10 h14
  have h7 : lambda * delta ≤ lambda ^ 3 * delta := by
    have h8 : 1 ≤ lambda ^ 2 := by nlinarith
    have h9 : 0 ≤ lambda * delta := by positivity
    calc
      lambda * delta
        = 1 * (lambda * delta) := by ring
      _ ≤ lambda ^ 2 * (lambda * delta) := by gcongr
      _ = lambda ^ 3 * delta := by ring
  have h_expand : D * (2 * (lambda * delta) / L + K * L + K * D)
      = D * (2 * (lambda * delta) / L) + D * (K * L) + D * (K * D) := by ring
  rw [h_expand, h1, h2, h3]
  linarith

lemma comparable_rectangles_caseB_target_bound
    {K C₁ lambda delta : ℝ}
    (hK : 1 ≤ K) (hC₁ : 0 < C₁)
    (hlambda : 1 ≤ lambda) (hdelta : 0 < delta) :
    2 * ((3 + 2 * C₁) * lambda ^ 3 * delta) ≤
      (6 + 4 * K + 4 * C₁) * Real.rpow lambda 3 * delta := by
  have h_rpow : Real.rpow lambda 3 = lambda ^ 3 := by
    simp [Real.rpow_natCast]
  rw [h_rpow]
  have hscale : 0 < lambda ^ 3 * delta := by positivity
  nlinarith

lemma comparable_rectangles_caseA_target_bound
    {K C₁ lambda delta : ℝ}
    (hK : 1 ≤ K) (hC₁ : 0 < C₁)
    (hlambda : 1 ≤ lambda) (hdelta : 0 < delta) :
    2 * ((3 + 2 * K) * lambda ^ 3 * delta) ≤
      (6 + 4 * K + 4 * C₁) * Real.rpow lambda 3 * delta := by
  have h_rpow : Real.rpow lambda 3 = lambda ^ 3 := by
    simp [Real.rpow_natCast]
  rw [h_rpow]
  have hscale : 0 < lambda ^ 3 * delta := by positivity
  nlinarith

theorem comparable_rectangles_have_close_graphs
    (hCommon : CommonTangentRectangleStatement) :
    ComparableRectanglesStatement := by
  intro K D hK hD
  rcases hCommon K D hK hD with ⟨C₁, hC₁_pos, hCommon_prop⟩
  let C := 6 + 4 * K + 4 * C₁
  use C
  constructor
  · have h₁ : 0 < K := by linarith
    have h₂ : 0 < C₁ := hC₁_pos
    linarith
  intro family hFamily I hI delta t lambda hdelta hdt hlambda R S hRfam hSfam hRquarter hSquarter hComparable
  have h_exists : ∃ (U : CurvilinearRectangle (lambda * delta) t),
      U.function ∈ family ∧ R.carrier ∪ S.carrier ⊆ U.carrier := by
    simpa [CurvilinearRectangle.AreLambdaComparable] using hComparable
  set L := Real.sqrt (delta / t) with hL_def
  set Dbound := Real.sqrt (lambda * delta / t) with hD_def
  set B := lambda * delta with hB_def
  have h_tpos : 0 < t := by linarith
  have hLpos : 0 < L := by rw [hL_def]; exact Real.sqrt_pos.mpr (by positivity)
  have hDpos : 0 ≤ Dbound := by rw [hD_def]; exact Real.sqrt_nonneg _
  have h_lenR : R.interval.length = L := by simpa [hL_def] using R.interval_length
  rcases h_exists with ⟨Wrect, hWfam, hWcont⟩
  ·
    let hfn : C2Function := Wrect.function
    let f := R.function
    let g := S.function
    set aR := R.interval.left with haR_def
    set bR := R.interval.right with hbR_def
    set aS := S.interval.left with haS_def
    set bS := S.interval.right with hbS_def
    set aW := Wrect.interval.left with haW_def
    set bW := Wrect.interval.right with hbW_def
    set l := min aR aS with hl_def
    set r := max bR bS with hr_def
    have h_lenW : Wrect.interval.length = Dbound := by
      exact Wrect.interval_length
    have h_aR01 : 0 ≤ aR ∧ aR ≤ 1 := R.interval.left_mem
    have h_bR01 : 0 ≤ bR ∧ bR ≤ 1 := R.interval.right_mem
    have h_aS01 : 0 ≤ aS ∧ aS ≤ 1 := S.interval.left_mem
    have h_bS01 : 0 ≤ bS ∧ bS ≤ 1 := S.interval.right_mem
    let aR' : UnitPoint := ⟨aR, h_aR01⟩
    let bR' : UnitPoint := ⟨bR, h_bR01⟩
    let aS' : UnitPoint := ⟨aS, h_aS01⟩
    let bS' : UnitPoint := ⟨bS, h_bS01⟩
    have hRcarrier_sub_Wcarrier := by
      show R.interval.carrier ⊆ Wrect.interval.carrier
      intro x hx
      have h1 : (x, f x) ∈ R.carrier := by
        have h2 : |f x - f x| ≤ delta := by simpa using hdelta.le
        exact ⟨hx, h2⟩
      have h2 : (x, f x) ∈ R.carrier ∪ S.carrier := Or.inl h1
      have h3 : (x, f x) ∈ Wrect.carrier := hWcont h2
      exact carrier_imp_interval Wrect (x, f x) h3
    have hScarrier_sub_Wcarrier := by
      show S.interval.carrier ⊆ Wrect.interval.carrier
      intro x hx
      have h1 : (x, g x) ∈ S.carrier := by
        have h2 : |g x - g x| ≤ delta := by simpa using hdelta.le
        exact ⟨hx, h2⟩
      have h2 : (x, g x) ∈ R.carrier ∪ S.carrier := Or.inr h1
      have h3 : (x, g x) ∈ Wrect.carrier := hWcont h2
      exact carrier_imp_interval Wrect (x, g x) h3
    have hR_val : ∀ x ∈ R.interval.carrier, |f x - hfn x| ≤ B := by
      intro x hx
      have h1 : (x, f x) ∈ R.carrier := by
        have h2 : |f x - f x| ≤ delta := by simpa using hdelta.le
        exact ⟨hx, h2⟩
      have h3 : (x, f x) ∈ Wrect.carrier := hWcont (Or.inl h1)
      have h4 := carrier_imp_bound Wrect (x, f x) h3
      simpa [hfn, B] using h4
    have hS_val : ∀ x ∈ S.interval.carrier, |g x - hfn x| ≤ B := by
      intro x hx
      have h1 : (x, g x) ∈ S.carrier := by
        have h2 : |g x - g x| ≤ delta := by simpa using hdelta.le
        exact ⟨hx, h2⟩
      have h3 : (x, g x) ∈ Wrect.carrier := hWcont (Or.inr h1)
      have h4 := carrier_imp_bound Wrect (x, g x) h3
      simpa [hfn, B] using h4
    have h_aR_in_Rcarrier : aR' ∈ R.interval.carrier := by
      have h : aR ≤ (aR' : ℝ) ∧ (aR' : ℝ) ≤ bR := by
        simp [aR', haR_def] <;> exact R.interval.left_le_right
      simpa [ParameterInterval.carrier] using h
    have h_bR_in_Rcarrier : bR' ∈ R.interval.carrier := by
      have h : aR ≤ (bR' : ℝ) ∧ (bR' : ℝ) ≤ bR := by
        simp [bR', hbR_def] <;> exact R.interval.left_le_right
      simpa [ParameterInterval.carrier] using h
    have hU_left_le_aR : aW ≤ aR := by
      have h : aR' ∈ Wrect.interval.carrier := hRcarrier_sub_Wcarrier h_aR_in_Rcarrier
      have h5 : Wrect.interval.left ≤ (aR' : ℝ) ∧ (aR' : ℝ) ≤ Wrect.interval.right := by
        simpa [ParameterInterval.carrier, Set.mem_setOf_eq] using h
      have h7 : aW ≤ (aR' : ℝ) := by
        simpa [haW_def] using h5.1
      simpa [aR'] using h7
    have h_bR_le_U_right : bR ≤ bW := by
      have h : bR' ∈ Wrect.interval.carrier := hRcarrier_sub_Wcarrier h_bR_in_Rcarrier
      have h5 : Wrect.interval.left ≤ (bR' : ℝ) ∧ (bR' : ℝ) ≤ Wrect.interval.right := by
        simpa [ParameterInterval.carrier, Set.mem_setOf_eq] using h
      have h7 : (bR' : ℝ) ≤ bW := by
        simpa [hbW_def] using h5.2
      simpa [bR'] using h7
    have h_aS_in_Scarrier : aS' ∈ S.interval.carrier := by
      have h : aS ≤ (aS' : ℝ) ∧ (aS' : ℝ) ≤ bS := by
        simp [aS', haS_def] <;> exact S.interval.left_le_right
      simpa [ParameterInterval.carrier] using h
    have h_bS_in_Scarrier : bS' ∈ S.interval.carrier := by
      have h : aS ≤ (bS' : ℝ) ∧ (bS' : ℝ) ≤ bS := by
        simp [bS', hbS_def] <;> exact S.interval.left_le_right
      simpa [ParameterInterval.carrier] using h
    have hU_left_le_aS : aW ≤ aS := by
      have h : aS' ∈ Wrect.interval.carrier := hScarrier_sub_Wcarrier h_aS_in_Scarrier
      have h5 : Wrect.interval.left ≤ (aS' : ℝ) ∧ (aS' : ℝ) ≤ Wrect.interval.right := by
        simpa [ParameterInterval.carrier, Set.mem_setOf_eq] using h
      have h7 : aW ≤ (aS' : ℝ) := by
        simpa [haW_def] using h5.1
      simpa [aS'] using h7
    have h_bS_le_U_right : bS ≤ bW := by
      have h : bS' ∈ Wrect.interval.carrier := hScarrier_sub_Wcarrier h_bS_in_Scarrier
      have h5 : Wrect.interval.left ≤ (bS' : ℝ) ∧ (bS' : ℝ) ≤ Wrect.interval.right := by
        simpa [ParameterInterval.carrier, Set.mem_setOf_eq] using h
      have h7 : (bS' : ℝ) ≤ bW := by
        simpa [hbW_def] using h5.2
      simpa [bS'] using h7
    have h_l_ge_aW : aW ≤ l := by
      simp only [hl_def, le_min_iff]
      exact ⟨hU_left_le_aR, hU_left_le_aS⟩
    have h_r_le_bW : r ≤ bW := by
      simp only [hr_def, max_le_iff]
      exact ⟨h_bR_le_U_right, h_bS_le_U_right⟩
    have h_first : r - l ≤ Dbound := by
      calc
        r - l ≤ bW - aW := by linarith
        _ = Wrect.interval.length := by
          have h_len1 : Wrect.interval.length = Wrect.interval.right - Wrect.interval.left := by
            unfold ParameterInterval.length <;> rfl
          rw [h_len1, haW_def, hbW_def]
        _ = Dbound := h_lenW
    have hR_ab : aR ≤ bR := R.interval.left_le_right
    have hS_ab : aS ≤ bS := S.interval.left_le_right
    have hlr : l ≤ r := by
      simp only [hl_def, hr_def]
      have h1 : min aR aS ≤ aR := min_le_left aR aS
      have h2 : aR ≤ bR := hR_ab
      have h3 : bR ≤ max bR bS := le_max_left bR bS
      linarith
    have hlaR : l ≤ aR := by
      simp only [hl_def, min_le_iff]
      exact Or.inl le_rfl
    have hbRr : bR ≤ r := by
      simp only [hr_def, le_max_iff]
      exact Or.inl le_rfl
    have hlaS : l ≤ aS := by
      simp only [hl_def, min_le_iff]
      exact Or.inr le_rfl
    have hbS_r : bS ≤ r := by
      simp only [hr_def, le_max_iff]
      exact Or.inr le_rfl
    have hdist_R_l : aR - l ≤ Dbound := by
      have h : aR - l ≤ aR - aW := by have h2 : aW ≤ l := h_l_ge_aW; linarith
      linarith [h_first]
    have hdist_R_r : r - bR ≤ Dbound := by
      have h : r - bR ≤ bW - bR := by have h2 : r ≤ bW := h_r_le_bW; linarith
      linarith [h_first]
    have hdist_S_l : aS - l ≤ Dbound := by
      have h : aS - l ≤ aS - aW := by have h2 : aW ≤ l := h_l_ge_aW; linarith
      linarith [h_first]
    have hdist_S_r : r - bS ≤ Dbound := by
      have h : r - bS ≤ bW - bS := by have h2 : r ≤ bW := h_r_le_bW; linarith
      linarith [h_first]
    have hR_val' : ∀ (x : UnitPoint), aR ≤ (x : ℝ) → (x : ℝ) ≤ bR → |f x - hfn x| ≤ B := by
      intro x h1 h2
      have h3 : x ∈ R.interval.carrier := by simp [ParameterInterval.carrier] <;> exact ⟨h1, h2⟩
      exact hR_val x h3
    have hS_val' : ∀ (x : UnitPoint), aS ≤ (x : ℝ) → (x : ℝ) ≤ bS → |g x - hfn x| ≤ B := by
      intro x h1 h2
      have h3 : x ∈ S.interval.carrier := by simp [ParameterInterval.carrier] <;> exact ⟨h1, h2⟩
      exact hS_val x h3
    have hLenR : bR - aR = L := by simpa [ParameterInterval.length, hL_def] using R.interval_length
    have hLenS : bS - aS = L := by simpa [ParameterInterval.length, hL_def] using S.interval_length
    have hl0 : 0 ≤ l := by
      have h1 : 0 ≤ aR := h_aR01.1
      have h2 : 0 ≤ aS := h_aS01.1
      simp only [hl_def, le_min_iff] <;> exact ⟨h1, h2⟩
    have hr1 : r ≤ 1 := by
      have h1 : bR ≤ 1 := h_bR01.2
      have h2 : bS ≤ 1 := h_bS01.2
      simp only [hr_def, max_le_iff] <;> exact ⟨h1, h2⟩
    by_cases h_case : lambda * t ≤ 1
    · -- Case B: λ * t ≤ 1, use hCommon with scaled rectangle
      have hCommon_bound : CommonTangentRectangleBound K D C₁ :=
        hCommon_prop
      have hRcont : R.carrier ⊆ Wrect.carrier := by
        intro p hp
        exact hWcont (Or.inl hp)
      have hScont : S.carrier ⊆ Wrect.carrier := by
        intro p hp
        exact hWcont (Or.inr hp)
      have h_c2_fh : c2Distance f hfn ≤ C₁ * lambda * t := by
        simpa only [f, hfn] using
          c2Distance_to_common_rectangle_small_scale
            hCommon_bound hC₁_pos.le hFamily hI hdelta hdt hlambda h_case
            R Wrect hRfam hWfam hRquarter hRcont
      have h_c2_gh : c2Distance g hfn ≤ C₁ * lambda * t := by
        simpa only [g, hfn] using
          c2Distance_to_common_rectangle_small_scale
            hCommon_bound hC₁_pos.le hFamily hI hdelta hdt hlambda h_case
            S Wrect hSfam hWfam hSquarter hScont
      let K' := C₁ * lambda * t
      have hK'_nonneg : 0 ≤ K' := by
        dsimp only [K']
        exact mul_nonneg
          (mul_nonneg hC₁_pos.le (zero_le_one.trans hlambda)) h_tpos.le
      have hB_nonneg : 0 ≤ B := by
        dsimp only [B]
        positivity
      have h_alg : B + Dbound * (2 * B / L + K' * L + K' * Dbound) ≤ (3 + 2 * C₁) * lambda^3 * delta :=
        comparable_rectangles_caseB_algebra hdelta h_tpos hlambda hC₁_pos K' rfl
      have h6 : 2 * ((3 + 2 * C₁) * lambda^3 * delta) ≤
          C * Real.rpow lambda 3 * delta := by
        simpa only [C] using
          comparable_rectangles_caseB_target_bound hK hC₁_pos hlambda hdelta
      have h_graph_difference :=
        @graph_difference_of_c2Distance_bounds f g hfn
          K' B L Dbound aR bR aS bS l r
          ((3 + 2 * C₁) * lambda^3 * delta)
          (C * Real.rpow lambda 3 * delta)
          hK'_nonneg hB_nonneg hLpos hDpos
          h_c2_fh h_c2_gh
          h_aR01.1 h_bR01.2 hR_ab
          h_aS01.1 h_bS01.2 hS_ab
          hl0 hr1 hlr hlaR hbRr hlaS hbS_r
          hLenR hLenS hR_val' hS_val'
          hdist_R_l hdist_R_r hdist_S_l hdist_S_r
          h_alg h6
      constructor
      · simpa [hr_def, hl_def] using h_first
      · intro x hx
        have hxl : l ≤ (x : ℝ) := by
          simpa [CurvilinearRectangle.intervalHullCarrier, hl_def] using hx.1
        have hxr : (x : ℝ) ≤ r := by
          simpa [CurvilinearRectangle.intervalHullCarrier, hr_def] using hx.2
        exact h_graph_difference x hxl hxr
    · -- Case A: λ * t > 1, crude K bound suffices
      let K' := K
      have hK'_nonneg : 0 ≤ K' := by linarith
      have h_c2_fh : c2Distance f hfn ≤ K := hFamily.1 hRfam hWfam
      have h_c2_gh : c2Distance g hfn ≤ K := hFamily.1 hSfam hWfam
      have hB_nonneg : 0 ≤ B := by
        dsimp only [B]
        positivity
      have h_lt : 1 < lambda * t := by linarith
      have h_alg : B + Dbound * (2 * B / L + K' * L + K' * Dbound) ≤ (3 + 2 * K) * lambda^3 * delta :=
        have h_dtover_t : delta / t < lambda * delta := by
          have h1 : 1 / t < lambda := by
            have h2 : 1 / t < (lambda * t) / t := by gcongr
            have h3 : (lambda * t) / t = lambda := by field_simp [h_tpos.ne'] <;> ring
            rw [h3] at h2; exact h2
          calc
            delta / t = delta * (1 / t) := by ring
            _ < delta * lambda := by gcongr
            _ = lambda * delta := by ring
        comparable_rectangles_caseA_algebra hdelta h_tpos hlambda (by linarith) h_dtover_t
      have h6 : 2 * ((3 + 2 * K) * lambda^3 * delta) ≤
          C * Real.rpow lambda 3 * delta := by
        simpa only [C] using
          comparable_rectangles_caseA_target_bound hK hC₁_pos hlambda hdelta
      have h_graph_difference :=
        @graph_difference_of_c2Distance_bounds f g hfn
          K' B L Dbound aR bR aS bS l r
          ((3 + 2 * K) * lambda^3 * delta)
          (C * Real.rpow lambda 3 * delta)
          hK'_nonneg hB_nonneg hLpos hDpos
          h_c2_fh h_c2_gh
          h_aR01.1 h_bR01.2 hR_ab
          h_aS01.1 h_bS01.2 hS_ab
          hl0 hr1 hlr hlaR hbRr hlaS hbS_r
          hLenR hLenS hR_val' hS_val'
          hdist_R_l hdist_R_r hdist_S_l hdist_S_r
          h_alg h6
      constructor
      · simpa [hr_def, hl_def] using h_first
      · intro x hx
        have hxl : l ≤ (x : ℝ) := by
          simpa [CurvilinearRectangle.intervalHullCarrier, hl_def] using hx.1
        have hxr : (x : ℝ) ≤ r := by
          simpa [CurvilinearRectangle.intervalHullCarrier, hr_def] using hx.2
        exact h_graph_difference x hxl hxr

end Kakeya.Cinematic
