module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.Defs
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.DerivativeStratification
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.WhitneyThreshold
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard.General

open MeasureTheory Module
open scoped ContDiff

lemma helper_k0 {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E m → F} {K : Set (E m)} (hK : IsCompact K) (hf : ContDiff ℝ 0 f) :
    ∀ ε > 0, ∃ δ > 0, ∀ (x : E m), x ∈ K → ∀ (y : E m), y ∈ K → ‖y - x‖ < δ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ 0 := by
  intro ε hε
  have h1 : ContinuousOn f K := hf.continuous.continuousOn
  have h2 : UniformContinuousOn f K := by
    exact IsCompact.uniformContinuousOn_of_continuous hK h1
  have h_main : ∃ δ > 0, ∀ (x : E m), x ∈ K → ∀ (y : E m), y ∈ K → dist x y < δ → dist (f x) (f y) < ε := by
    exact Metric.uniformContinuousOn_iff.mp h2 ε hε
  rcases h_main with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, fun x hx y hy hxy => ?_⟩
  have h_dist1 : dist x y < δ := by
    have h11 : dist x y = ‖x - y‖ := by rw [dist_eq_norm]
    rw [h11]
    have h12 : ‖x - y‖ = ‖y - x‖ := by rw [show x - y = -(y - x) by abel]; rw [norm_neg]
    rw [h12]
    exact hxy
  have h_dist2 : dist (f x) (f y) < ε := hδ x hx y hy h_dist1
  have h91 : ‖f x - f y‖ < ε := by simpa [dist_eq_norm] using h_dist2
  have h9 : ‖f y - f x‖ < ε := by
    have h10 : f y - f x = -(f x - f y) := by abel
    rw [h10, norm_neg]
    exact h91
  have h10 : ε * ‖y - x‖ ^ 0 = ε := by simp
  rw [h10]
  exact le_of_lt h9

lemma norm_le_of_mem_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x y z : E}
    (hz : z ∈ segment ℝ x y) : ‖z - x‖ ≤ ‖y - x‖ := by
  rcases segment_eq_image ℝ x y ▸ hz with ⟨t, ht, rfl⟩
  have h1 : 0 ≤ t := ht.1
  have h2 : t ≤ 1 := ht.2
  set w : E := (1 - t) • x + t • y with hw
  have h3 : w - x = t • (y - x) := by
    simp [hw, smul_sub, sub_smul]
    abel
  have h4 : ‖w - x‖ = |t| * ‖y - x‖ := by
    rw [h3]
    exact norm_smul t (y - x)
  have h5 : |t| ≤ 1 := by
    have h6 : 0 ≤ t := h1
    have h7 : t ≤ 1 := h2
    rw [abs_of_nonneg h6]
    linarith
  have hnorm_nonneg : 0 ≤ ‖y - x‖ := norm_nonneg _
  have h9 : |t| * ‖y - x‖ ≤ 1 * ‖y - x‖ := by
    exact mul_le_mul_of_nonneg_right h5 hnorm_nonneg
  have h6 : ‖w - x‖ ≤ ‖y - x‖ := by
    rw [h4]
    simpa using h9
  exact h6

lemma exists_convex_compact_superset {m : ℕ} (K : Set (E m)) (hK : IsCompact K) :
    ∃ (K' : Set (E m)), IsCompact K' ∧ Convex ℝ K' ∧ K ⊆ K' := by
  by_cases hK_empty : K = ∅
  · subst hK_empty
    let K' := Metric.closedBall (0 : E m) 1
    refine' ⟨K', _, _, _⟩
    · exact isCompact_closedBall 0 1
    · exact convex_closedBall 0 1
    · simp
  · have hK_nonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
    let f : E m → ℝ := fun x => ‖x‖
    have h_cont : Continuous f := by exact continuous_norm
    have h_contOn : ContinuousOn f K := h_cont.continuousOn
    have h3 : ∃ (x₀ : E m), x₀ ∈ K ∧ ∀ x ∈ K, f x ≤ f x₀ := hK.exists_isMaxOn hK_nonempty h_contOn
    rcases h3 with ⟨x₀, hx₀K, hle⟩
    let R : ℝ := f x₀ + 1
    have hR_pos : 0 < R := by positivity
    let K' := Metric.closedBall (0 : E m) R
    refine' ⟨K', _, _, _⟩
    · exact isCompact_closedBall 0 R
    · exact convex_closedBall 0 R
    · intro x hx
      have h4 : f x ≤ f x₀ := hle x hx
      have h5 : f x ≤ R := by
        dsimp only [R, f]
        linarith
      simpa [K', Metric.mem_closedBall, f] using h5

lemma round1_main_inductive_general (m : ℕ) (k : ℕ) :
    ∀ {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]
        (f : E m → F) (_ : ContDiff ℝ k f) (Z : Set (E m))
        (_ : ∀ x ∈ Z, ∀ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ k → iteratedFDeriv ℝ ℓ f x = 0)
        (K' : Set (E m)) (_ : IsCompact K') (_ : Convex ℝ K'),
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Z ∩ K', ∀ y ∈ K',
        ‖y - x‖ < δ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ k := by
  induction k with
  | zero =>
    intro F _ _ f hf _ _ K' hK'compact _ ε hε
    have h1 := helper_k0 (K := K') hK'compact hf ε hε
    rcases h1 with ⟨δ, hδ_pos, h2⟩
    refine' ⟨δ, hδ_pos, _⟩
    intro x hx y hy hxy
    have hxK' : x ∈ K' := hx.2
    have h3 := h2 x hxK' y hy hxy
    simpa using h3
  | succ k ih =>
    intro F _ _ f hf Z hZ K' hK'compact hK'convex ε hε
    let G := (E m →L[ℝ] F)
    let g : E m → G := fun x => fderiv ℝ f x
    have h_iff : ContDiff ℝ (k + 1) f ↔ ∃ (g' : E m → G), ContDiff ℝ k g' ∧ ∀ (x : E m), HasFDerivAt f (g' x) x := contDiff_succ_iff_hasFDerivAt
    have h2 : ∃ (g' : E m → G), ContDiff ℝ k g' ∧ ∀ (x : E m), HasFDerivAt f (g' x) x := h_iff.mp hf
    rcases h2 with ⟨g', hg', h_eq_hasFDeriv⟩
    have h_g'_eq_g : g' = g := by
      funext x
      have h4 : fderiv ℝ f x = g' x := (h_eq_hasFDeriv x).fderiv
      exact Eq.symm h4
    rw [h_g'_eq_g] at hg'
    let hg : ContDiff ℝ k g := hg'
    have hZg : ∀ x ∈ Z, ∀ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ k → iteratedFDeriv ℝ ℓ g x = 0 := by
      intro x hx ℓ hℓ
      have h1 : 1 ≤ ℓ + 1 ∧ ℓ + 1 ≤ k + 1 := by omega
      have h2 : iteratedFDeriv ℝ (ℓ + 1) f x = 0 := hZ x hx (ℓ + 1) h1
      have h3 : iteratedFDeriv ℝ (ℓ + 1) f x = ((continuousMultilinearCurryRightEquiv' ℝ ℓ (E m) F).symm (iteratedFDeriv ℝ ℓ g x)) := by
        exact iteratedFDeriv_succ_eq_comp_right (f := f) (n := ℓ) (x := x)
      rw [h3] at h2
      exact (continuousMultilinearCurryRightEquiv' ℝ ℓ (E m) F).symm.injective h2
    have h_main_ih := ih g hg Z hZg K' hK'compact hK'convex ε hε
    rcases h_main_ih with ⟨δ, hδ_pos, hδ⟩
    refine' ⟨δ, hδ_pos, _⟩
    intro x hx y hy hxy
    have hx1 : x ∈ Z ∩ K' := hx
    have hxZ : x ∈ Z := hx1.1
    have hxK' : x ∈ K' := hx1.2
    have h_yK' : y ∈ K' := hy
    have h1 : iteratedFDeriv ℝ 1 f x = 0 := hZ x hxZ 1 ⟨by norm_num, by omega⟩
    have h2 : ‖iteratedFDeriv ℝ 1 f x‖ = ‖fderiv ℝ f x‖ := norm_iteratedFDeriv_one (f := f) (x := x)
    have h3 : ‖fderiv ℝ f x‖ = 0 := by
      rw [←h2, h1]
      simp
    have h_gx_eq_0 : g x = 0 := by
      simpa [g, norm_eq_zero] using h3
    let C := ε * ‖y - x‖ ^ k
    have h_deriv_bound : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z‖ ≤ C := by
      intro z hz
      have hzK' : z ∈ K' := hK'convex.segment_subset hxK' h_yK' hz
      have h_norm_zx : ‖z - x‖ ≤ ‖y - x‖ := norm_le_of_mem_segment hz
      have h_lt : ‖z - x‖ < δ := by linarith
      have h4 : x ∈ Z ∩ K' := ⟨hxZ, hxK'⟩
      have h5 : ‖g z - g x‖ ≤ ε * ‖z - x‖ ^ k := hδ x h4 z hzK' h_lt
      rw [h_gx_eq_0, sub_zero] at h5
      have h6 : ‖g z‖ ≤ ε * ‖z - x‖ ^ k := h5
      have h7 : ε * ‖z - x‖ ^ k ≤ ε * ‖y - x‖ ^ k := by
        gcongr
      exact le_trans h6 h7
    have h_seg_conv : Convex ℝ (segment ℝ x y) := by
      exact convex_segment x y
    have h_x_in_seg : x ∈ segment ℝ x y := left_mem_segment ℝ x y
    have h_y_in_seg : y ∈ segment ℝ x y := right_mem_segment ℝ x y
    have h_ne_zero : (↑(k + 1) : WithTop ℕ∞) ≠ 0 := by
      simp
    have h_diff : Differentiable ℝ f := hf.differentiable h_ne_zero
    have h_diff' : ∀ z ∈ segment ℝ x y, DifferentiableAt ℝ f z := by
      intro z _
      exact h_diff.differentiableAt
    have h_final : ‖f y - f x‖ ≤ C * ‖y - x‖ := by
      apply Convex.norm_image_sub_le_of_norm_fderiv_le (s := segment ℝ x y) h_diff' h_deriv_bound h_seg_conv h_x_in_seg h_y_in_seg
    have h_goal : C * ‖y - x‖ = ε * ‖y - x‖ ^ (k + 1) := by
      dsimp only [C]
      ring
    rw [h_goal] at h_final
    exact h_final

/-- Lemma 13 (Uniform flat Taylor estimate).
    If f is C^k and D^ℓ f = 0 on Z for all 1 ≤ ℓ ≤ k, then on any compact set K,
    for all ε > 0 there exists δ > 0 such that for all x ∈ Z ∩ K, y ∈ K with
    ‖y - x‖ < δ, we have ‖f y - f x‖ ≤ ε * ‖y - x‖^k.
    This follows from Taylor's theorem with vanishing derivatives. -/
theorem flat_taylor_estimate {m n k : ℕ} (f : E m → E n)
    (hf : ContDiff ℝ k f) (Z : Set (E m))
    (hZ : ∀ x ∈ Z, ∀ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ k →
      iteratedFDeriv ℝ ℓ f x = 0)
    (K : Set (E m)) (hK : IsCompact K) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Z ∩ K, ∀ y ∈ K,
      ‖y - x‖ < δ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ k := by
  have h_main : ∃ (K' : Set (E m)), IsCompact K' ∧ Convex ℝ K' ∧ K ⊆ K' :=
    exists_convex_compact_superset K hK
  rcases h_main with ⟨K', hK'compact, hK'convex, hKsub⟩
  have h_ih := round1_main_inductive_general m k f hf Z hZ K' hK'compact hK'convex
  intro ε hε
  have h_exists : ∃ δ > 0, ∀ x ∈ Z ∩ K', ∀ y ∈ K', ‖y - x‖ < δ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ k := h_ih ε hε
  rcases h_exists with ⟨δ, hδ_pos, hδ⟩
  refine' ⟨δ, hδ_pos, _⟩
  intro x hx y hy hxy
  have hxZ : x ∈ Z := hx.1
  have hxK : x ∈ K := hx.2
  have hxK' : x ∈ K' := hKsub hxK
  have hx' : x ∈ Z ∩ K' := ⟨hxZ, hxK'⟩
  have hyK' : y ∈ K' := hKsub hy
  exact hδ x hx' y hyK' hxy

lemma helper_global_holder {m n k : ℕ} (f : E m → E n)
    (hf : ContDiff ℝ k f) (Z : Set (E m))
    (hZ : ∀ x ∈ Z, ∀ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ k → iteratedFDeriv ℝ ℓ f x = 0)
    (K' : Set (E m)) (hK'compact : IsCompact K') (hK'convex : Convex ℝ K') :
    ∃ (C : NNReal), HolderOnWith C k f (Z ∩ K') := by
  have h_main_est : ∃ δ > 0, ∀ x ∈ Z ∩ K', ∀ y ∈ K', ‖y - x‖ < δ → ‖f y - f x‖ ≤ (1 : ℝ) * ‖y - x‖ ^ k :=
    round1_main_inductive_general m k f hf Z hZ K' hK'compact hK'convex 1 zero_lt_one
  rcases h_main_est with ⟨δ, hδ_pos, hδ⟩
  let g : E m → ℝ := fun z => ‖f z‖
  have h_norm_cont : Continuous g := hf.continuous.norm
  have hK'_compact_image : IsCompact (g '' K') := hK'compact.image h_norm_cont
  have h1 : Bornology.IsBounded (g '' K') := hK'_compact_image.isBounded
  have h2 : BddAbove (g '' K') := h1.bddAbove
  rcases h2 with ⟨B, hB⟩
  have hB' : ∀ (z : E m), z ∈ K' → g z ≤ B := by
    intro z hz
    have h3 : g z ∈ g '' K' := ⟨z, hz, rfl⟩
    exact hB h3
  set B' : ℝ := max B 0 with hB'_def
  have hB'_nonneg : 0 ≤ B' := by positivity
  have hB'' : ∀ (z : E m), z ∈ K' → ‖f z‖ ≤ B' := by
    intro z hz
    have h4 : g z ≤ B := hB' z hz
    have h5 : B ≤ B' := by
      rw [hB'_def]
      exact le_max_left _ _
    linarith
  set C0 : ℝ := max (1 : ℝ) (2 * B' / δ ^ k) with hC0_def
  have hC0_nonneg : 0 ≤ C0 := by positivity
  set C : NNReal := ⟨C0, hC0_nonneg⟩
  have h_ineq : ∀ (x : E m), x ∈ Z ∩ K' → ∀ (y : E m), y ∈ K' → ‖f y - f x‖ ≤ (C : ℝ) * ‖y - x‖ ^ k := by
    intro x hx y hy
    by_cases h : ‖y - x‖ < δ
    · have h4 : ‖f y - f x‖ ≤ (1 : ℝ) * ‖y - x‖ ^ k := hδ x hx y hy h
      have h6 : (1 : ℝ) ≤ C0 := by
        rw [hC0_def]
        exact le_max_left _ _
      have h7 : 0 ≤ ‖y - x‖ ^ k := by positivity
      have h5 : (1 : ℝ) * ‖y - x‖ ^ k ≤ C0 * ‖y - x‖ ^ k := by
        exact mul_le_mul_of_nonneg_right h6 h7
      exact h4.trans h5
    · have h' : δ ≤ ‖y - x‖ := by
        by_contra h''
        exact h (by linarith)
      have h81 : ‖f y‖ ≤ B' := hB'' y hy
      have h82 : ‖f x‖ ≤ B' := hB'' x hx.2
      have h8 : ‖f y - f x‖ ≤ 2 * B' := by
        calc
          ‖f y - f x‖ ≤ ‖f y‖ + ‖f x‖ := norm_sub_le _ _
          _ ≤ B' + B' := by linarith
          _ = 2 * B' := by ring
      have h9 : δ ^ k ≤ ‖y - x‖ ^ k := by
        gcongr
      have h11 : 2 * B' / δ ^ k ≤ C0 := by
        rw [hC0_def]
        exact le_max_right _ _
      have h12 : 0 < δ ^ k := by positivity
      have h10 : 2 * B' ≤ C0 * ‖y - x‖ ^ k := by
        calc
          2 * B' = (2 * B' / δ ^ k) * δ ^ k := by field_simp [h12.ne']
          _ ≤ (2 * B' / δ ^ k) * ‖y - x‖ ^ k := by gcongr
          _ ≤ C0 * ‖y - x‖ ^ k := by gcongr
      exact h8.trans h10
  have h_holder_ineq : ∀ (x : E m), x ∈ Z ∩ K' → ∀ (y : E m), y ∈ Z ∩ K' → ‖f y - f x‖ ≤ (C : ℝ) * ‖y - x‖ ^ k := by
    intro x hx y hy
    have hy' : y ∈ K' := hy.2
    exact h_ineq x hx y hy'
  have h_final : HolderOnWith C k f (Z ∩ K') := by
    rw [HolderOnWith]
    intro x hx y hy
    set z : ℝ := ‖x - y‖ with hz_def
    have hz_nonneg : 0 ≤ z := by positivity
    have h_norm_eq : ‖y - x‖ = z := by
      have h : ‖y - x‖ = ‖-(x - y)‖ := by rw [show y - x = -(x - y) by abel]
      rw [h, norm_neg]
    have h_real1 : ‖f y - f x‖ ≤ (C : ℝ) * z ^ k := by
      have h' := h_holder_ineq x hx y hy
      rw [h_norm_eq] at h'
      exact h'
    have h1 : ‖f x - f y‖ = ‖f y - f x‖ := by
      rw [show f x - f y = -(f y - f x) by abel]
      rw [norm_neg]
    have h_goal : ‖f x - f y‖ ≤ (C : ℝ) * z ^ k := by
      calc
        ‖f x - f y‖ = ‖f y - f x‖ := h1
        _ ≤ (C : ℝ) * z ^ k := h_real1
    have h_nonneg1 : 0 ≤ ‖f x - f y‖ := by positivity
    have hC_nonneg : 0 ≤ (C : ℝ) := C.prop
    have hzk_nonneg : 0 ≤ z ^ k := by positivity
    have h_eq1 : ENNReal.ofReal ((C : ℝ) * z ^ k) = ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (z ^ k) := by
      exact ENNReal.ofReal_mul hC_nonneg
    have h_eq2 : ENNReal.ofReal (C : ℝ) = (C : ENNReal) := by
      exact ENNReal.ofReal_coe_nnreal
    have h_eq3 : ENNReal.ofReal (z ^ k) = (ENNReal.ofReal z) ^ (k : ℝ) := by
      simp [ENNReal.ofReal_pow hz_nonneg]
    have h_eq : ENNReal.ofReal ((C : ℝ) * z ^ k) = (C : ENNReal) * (ENNReal.ofReal z) ^ (k : ℝ) := by
      rw [h_eq1, h_eq2, h_eq3]
    have h_edist : edist (f x) (f y) = ENNReal.ofReal ‖f x - f y‖ := by
      simp [edist_dist, dist_eq_norm]
    rw [h_edist]
    have h3 : edist x y = ENNReal.ofReal z := by
      simp [edist_dist, dist_eq_norm, hz_def]
    rw [h3]
    have h4 : ENNReal.ofReal ‖f x - f y‖ ≤ ENNReal.ofReal ((C : ℝ) * z ^ k) := ENNReal.ofReal_le_ofReal h_goal
    rw [h_eq] at h4
    exact h4
  exact ⟨C, h_final⟩

lemma exists_int_half_approx (x : ℝ) : ∃ (z : ℤ), |x - (z : ℝ)| ≤ 1 / 2 := by
  let z₁ : ℤ := Int.floor x
  have h1 : (z₁ : ℝ) ≤ x := Int.floor_le x
  have h2 : x < (z₁ : ℝ) + 1 := Int.lt_floor_add_one x
  by_cases h : x - (z₁ : ℝ) ≤ 1 / 2
  · use z₁
    have h3 : x - (z₁ : ℝ) ≥ 0 := by linarith
    have h4 : |x - (z₁ : ℝ)| = x - (z₁ : ℝ) := by
      rw [abs_of_nonneg h3]
    rw [h4]
    linarith
  · have h' : x - (z₁ : ℝ) > 1 / 2 := by exact not_le.mp h
    have h_pos : ((z₁ + 1 : ℤ) : ℝ) - x > 0 := by
      simp [h2]
    have h_le : ((z₁ + 1 : ℤ) : ℝ) - x ≤ 1 / 2 := by
      have h9 : x - (z₁ : ℝ) > 1 / 2 := h'
      have h10 : x < (z₁ : ℝ) + 1 := h2
      simp at *
      linarith
    use z₁ + 1
    have h8 : |x - ((z₁ + 1 : ℤ) : ℝ)| = ((z₁ + 1 : ℤ) : ℝ) - x := by
      have h9 : x - ((z₁ + 1 : ℤ) : ℝ) < 0 := by linarith
      rw [abs_of_neg h9]
      linarith
    rw [h8]
    exact h_le
lemma exists_int_multiple_approx (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ∃ (z : ℤ), |a - (z : ℝ) * s| ≤ s / 2 := by
  have h1 : ∃ (z : ℤ), |(a / s) - (z : ℝ)| ≤ 1 / 2 := exists_int_half_approx (a / s)
  rcases h1 with ⟨z, hz⟩
  have h_eq : a - (z : ℝ) * s = s * ((a / s) - (z : ℝ)) := by
    have h4 : s * (a / s) = a := by
      field_simp [hs.ne']
    rw [mul_sub]
    rw [h4]
    ring
  have h2 : |a - (z : ℝ) * s| = s * |(a / s) - (z : ℝ)| := by
    rw [h_eq]
    rw [abs_mul, abs_of_pos hs]
  have h3 : s * |(a / s) - (z : ℝ)| ≤ s / 2 := by
    have h4 : s * |(a / s) - (z : ℝ)| ≤ s * (1 / 2 : ℝ) := by
      gcongr
    have h5 : s * (1 / 2 : ℝ) = s / 2 := by ring
    rw [h5] at h4
    exact h4
  refine' ⟨z, _⟩
  rw [h2]
  exact h3

/-- Lemma 14 (Flat image volume estimate).
    If kn > m and D^ℓ f = 0 on Z for all 1 ≤ ℓ ≤ k, then vol_n(f(Z)) = 0.
    Proof: f is Hölder continuous on Z, so dimH(f(Z)) ≤ dimH(Z)/k ≤ m/k < n
    (since k*n > m), hence dimH(f(Z)) < n, so the n-dimensional Hausdorff measure
    (which equals Lebesgue volume) is zero. -/
theorem flat_image_volume_zero {m n k : ℕ} (hkn : k * n > m)
    (f : E m → E n) (hf : ContDiff ℝ k f) (Z : Set (E m))
    (hZ : ∀ x ∈ Z, ∀ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ k →
      iteratedFDeriv ℝ ℓ f x = 0) :
    volume (f '' Z) = 0 := by
  have hk_pos : 0 < k := by
    by_contra h
    have h' : k = 0 := by omega
    rw [h'] at hkn
    omega
  have hn_pos : 0 < n := by
    by_contra h
    have h' : n = 0 := by omega
    rw [h'] at hkn
    omega
  have h_sigma : ∃ (K : ℕ → Set (E m)), (∀ i, IsCompact (K i)) ∧ (⋃ i, K i) = (Set.univ : Set (E m)) := by
    exact SigmaCompactSpace.exists_compact_covering
  rcases h_sigma with ⟨K, hK_compact, hK_univ⟩
  have h_main : ∀ i : ℕ, volume (f '' (Z ∩ K i)) = 0 := by
    intro i
    have h1 : ∃ (K' : Set (E m)), IsCompact K' ∧ Convex ℝ K' ∧ K i ⊆ K' :=
      exists_convex_compact_superset (K i) (hK_compact i)
    rcases h1 with ⟨K', hK'compact, hK'convex, hKi_sub_K'⟩
    have hZK' : (Z ∩ K i) ⊆ K' := by
      intro x hx
      exact hKi_sub_K' hx.2
    have hZ' : ∀ x ∈ (Z ∩ K i), ∀ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ k → iteratedFDeriv ℝ ℓ f x = 0 := by
      intro x hx ℓ hℓ
      exact hZ x hx.1 ℓ hℓ
    have h2 : ∃ (C : NNReal), HolderOnWith C k f ((Z ∩ K i) ∩ K') :=
      helper_global_holder f hf (Z ∩ K i) hZ' K' hK'compact hK'convex
    rcases h2 with ⟨C, hC⟩
    have h3 : (Z ∩ K i) ⊆ (Z ∩ K i) ∩ K' := by
      intro x hx
      exact ⟨hx, hZK' hx⟩
    have h41 : (Z ∩ K i) ∩ K' ⊆ Z ∩ K i := by
      intro x hx
      exact hx.1
    have h4 : (Z ∩ K i) = (Z ∩ K i) ∩ K' := Set.Subset.antisymm h3 h41
    have h5 : dimH (f '' (Z ∩ K i)) ≤ dimH (Z ∩ K i) / (k : ENNReal) := by
      rw [h4]
      exact hC.dimH_image_le (by exact_mod_cast hk_pos)
    have h6 : dimH (Z ∩ K i) ≤ (m : ENNReal) := by
      have h61 : (Z ∩ K i) ⊆ (Set.univ : Set (E m)) := Set.subset_univ _
      have h62 : dimH (Z ∩ K i) ≤ dimH (Set.univ : Set (E m)) := dimH_mono h61
      have h63 : dimH (Set.univ : Set (E m)) = Module.finrank ℝ (E m) :=
        Real.dimH_univ_eq_finrank (E m)
      have h64 : Module.finrank ℝ (E m) = m := by simp [E]
      rw [h63, h64] at h62
      exact_mod_cast h62
    have h7 : dimH (f '' (Z ∩ K i)) ≤ (m : ENNReal) / (k : ENNReal) := by
      calc
        dimH (f '' (Z ∩ K i)) ≤ dimH (Z ∩ K i) / (k : ENNReal) := h5
        _ ≤ (m : ENNReal) / (k : ENNReal) := by gcongr
    have h8 : (m : ENNReal) / (k : ENNReal) < (n : ENNReal) := by
      have h9 : (m : ℝ) / (k : ℝ) < (n : ℝ) := by
        have h10 : (k : ℝ) > 0 := by exact_mod_cast hk_pos
        have h11 : (m : ℝ) < (k : ℝ) * (n : ℝ) := by exact_mod_cast hkn
        calc
          (m : ℝ) / (k : ℝ) < ((k : ℝ) * (n : ℝ)) / (k : ℝ) := by gcongr
          _ = (n : ℝ) := by
            field_simp [h10.ne']
      have h10 : (m : ENNReal) / (k : ENNReal) = ENNReal.ofReal ((m : ℝ) / (k : ℝ)) := by
        rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hk_pos)]
        simp
      have h11 : (n : ENNReal) = ENNReal.ofReal (n : ℝ) := by simp
      rw [h10, h11]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr h9
    have h9 : dimH (f '' (Z ∩ K i)) < (n : ENNReal) := h7.trans_lt h8
    have h10 : (MeasureTheory.Measure.hausdorffMeasure (n : ℝ)) (f '' (Z ∩ K i)) = 0 :=
      hausdorffMeasure_of_dimH_lt (d := n) h9
    have h71 : (MeasureTheory.Measure.euclideanHausdorffMeasure n : Measure (E n)) (f '' (Z ∩ K i)) = 0 := by
      rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def n]
      simp [h10]
    have h_eq : (MeasureTheory.Measure.euclideanHausdorffMeasure n : Measure (E n)) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
    exact by
      calc
        volume (f '' (Z ∩ K i))
          = (MeasureTheory.Measure.euclideanHausdorffMeasure n : Measure (E n)) (f '' (Z ∩ K i)) := by rw [h_eq]
        _ = 0 := h71
  have h_cover : f '' Z ⊆ ⋃ i : ℕ, f '' (Z ∩ K i) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h_x_in_univ : x ∈ (⋃ i : ℕ, K i) := by
      rw [hK_univ]
      trivial
    rcases Set.mem_iUnion.mp h_x_in_univ with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨x, ⟨hx, hi⟩, rfl⟩⟩
  have h_null : volume (⋃ i : ℕ, f '' (Z ∩ K i)) = 0 :=
    measure_iUnion_null h_main
  exact measure_mono_null h_cover h_null

/-- Lemma 16 (Flat set C_k has null image).
    Let k = m - n + 1. Then vol_n(f(C_k)) = 0.
    Combines lemmas 14 and 15.
    Since f is C^∞, it is certainly C^k, so Lemma 14 applies. -/
theorem flat_set_image_null {m n : ℕ} (hnm : 0 < n ∧ n < m)
    (f : E m → E n) (hf : ContDiff ℝ ∞ f) :
    let k := m - n + 2
    volume (f '' flatStratum f k) = 0 := by
  let k := m - n + 2
  have hfk : ContDiff ℝ k f := hf.of_le (by exact_mod_cast le_top)
  have hZ : ∀ x ∈ flatStratum f k, ∀ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ k →
    iteratedFDeriv ℝ ℓ f x = 0 := by
    intro x hx ℓ hℓ
    exact hx ℓ hℓ
  have hkn_strict : k * n > m := by
    have h1 : k = m - n + 2 := by rfl
    rw [h1]
    have h2 : m > n := hnm.2
    have h3 : 0 < n := hnm.1
    have h4 : (m - n + 2) * n > m := by
      have h5 : m ≥ n + 1 := by omega
      set d := m - n with hd_def
      have hd_pos : 0 < d := by omega
      have h6 : (d + 2) * n > d + n := by
        nlinarith
      have h7 : d + n = m := by omega
      rw [h7] at h6
      exact h6
    exact h4
  exact flat_image_volume_zero hkn_strict f hfk (flatStratum f k) hZ

end ForMathlib.Analysis.Calculus.Sard.General
