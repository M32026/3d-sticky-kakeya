import MyLeanRepo.Kakeya.Cinematic.Definitions
import MyLeanRepo.Kakeya.Cinematic.Geometry
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Finset.Card
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Infrastructure for the local cinematic assembly

This module compares metric graph neighborhoods with vertical neighborhoods,
records uniform two-jet bounds inside a fixed cinematic family, and identifies
multiplicity with the corresponding finite filtered cardinality.
-/

noncomputable section

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

namespace Kakeya.Cinematic

lemma localAssembly_graph_neighborhood_exists
    {f : C2Function} {δ : ℝ} {p : ℝ × ℝ}
    (h : p ∈ graphNeighborhood f δ) :
    ∃ x' : UnitPoint,
      |p.1 - (x' : ℝ)| < δ ∧ |p.2 - f x'| < δ := by
  rw [graphNeighborhood, mem_thickening_iff] at h
  rcases h with ⟨q, hq, hdist⟩
  have hq1 : q.1 ∈ unitInterval := hq.1
  let x' : UnitPoint := ⟨q.1, hq1⟩
  have hq_eq : q = ((x' : ℝ), f x') := by
    ext
    · rfl
    · exact hq.2
  rw [hq_eq, Prod.dist_eq] at hdist
  have h1 : |p.1 - (x' : ℝ)| < δ := by
    have : dist p.1 (x' : ℝ) < δ :=
      (le_max_left _ _).trans_lt hdist
    simpa [Real.dist_eq] using this
  have h2 : |p.2 - f x'| < δ := by
    have : dist p.2 (f x') < δ :=
      (le_max_right _ _).trans_lt hdist
    simpa [Real.dist_eq] using this
  exact ⟨x', h1, h2⟩

lemma localAssembly_vertical_bound_with_derivative
    {f : C2Function} {M δ : ℝ}
    {x x' : UnitPoint} {y : ℝ}
    (hderiv : ∀ z : UnitPoint, |f.firstDeriv z| ≤ M)
    (h1 : |(x : ℝ) - (x' : ℝ)| < δ)
    (h2 : |y - f x'| < δ) :
    |y - f x| ≤ (1 + M) * δ := by
  have hM_nonneg : 0 ≤ M := by
    exact (abs_nonneg _).trans (hderiv x)
  have h3 : |f x - f x'| ≤ M * |(x : ℝ) - (x' : ℝ)| := by
    have hdiff : Differentiable ℝ f.extension :=
      ContDiff.differentiable f.extension_contDiff (by norm_num)
    have hdiffAt :
        ∀ z ∈ (Set.Icc 0 1 : Set ℝ),
          DifferentiableAt ℝ f.extension z :=
      fun z _ => hdiff.differentiableAt
    have hbound :
        ∀ z ∈ (Set.Icc 0 1 : Set ℝ),
          ‖deriv f.extension z‖ ≤ M := by
      intro z hz
      let z' : UnitPoint := ⟨z, hz⟩
      rw [f.deriv_extension_eq_firstDeriv z']
      simpa [Real.norm_eq_abs] using hderiv z'
    have h :=
      Convex.norm_image_sub_le_of_norm_deriv_le
        hdiffAt hbound (convex_Icc 0 1) x.prop x'.prop
    rw [f.extension_eq_value, f.extension_eq_value] at h
    simpa [Real.norm_eq_abs, abs_sub_comm] using h
  have h4 : |f x - f x'| ≤ M * δ := by
    exact h3.trans (mul_le_mul_of_nonneg_left h1.le hM_nonneg)
  have h5 : |y - f x| ≤ |y - f x'| + |f x' - f x| := by
    have h6 : y - f x = (y - f x') + (f x' - f x) := by ring
    rw [h6]
    simpa [Real.norm_eq_abs] using
      norm_add_le (y - f x') (f x' - f x)
  calc
    |y - f x| ≤ |y - f x'| + |f x' - f x| := h5
    _ = |y - f x'| + |f x - f x'| := by
      congr 1
      exact abs_sub_comm (f x') (f x)
    _ ≤ δ + M * δ := add_le_add h2.le h4
    _ = (1 + M) * δ := by ring

lemma localAssembly_cinematic_uniform_bounds
    {family : Set C2Function} {K D : ℝ}
    (hcinematic : IsCinematicFamily family K D)
    {f₀ : C2Function} (hf₀ : f₀ ∈ family) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ f ∈ family, ∀ x : UnitPoint,
        |f x| ≤ M ∧
          |f.firstDeriv x| ≤ M ∧
          |f.secondDeriv x| ≤ M := by
  let M_val := ‖f₀.value‖ + K
  let M_der := ‖f₀.firstDeriv‖ + K
  let M_der2 := ‖f₀.secondDeriv‖ + K
  let M := max M_val (max M_der M_der2)
  have hM_nonneg : 0 ≤ M := by
    dsimp only [M, M_val]
    exact le_max_of_le_left (add_nonneg (norm_nonneg _) (by
      have := hcinematic.1 hf₀ hf₀
      simpa using this))
  refine ⟨M, hM_nonneg, ?_⟩
  intro f hf x
  have hdist : c2Distance f f₀ ≤ K := hcinematic.1 hf hf₀
  have h1 : |f x - f₀ x| ≤ K :=
    (abs_value_sub_le_c2Distance f f₀ x).trans hdist
  have h2 : |f.firstDeriv x - f₀.firstDeriv x| ≤ K :=
    (abs_firstDeriv_sub_le_c2Distance f f₀ x).trans hdist
  have h3 : |f.secondDeriv x - f₀.secondDeriv x| ≤ K :=
    (abs_secondDeriv_sub_le_c2Distance f f₀ x).trans hdist
  have h4 : |f x| ≤ M_val := by
    calc
      |f x| ≤ |f₀ x| + |f x - f₀ x| := by
        have h : f x = f₀ x + (f x - f₀ x) := by ring
        rw [h]
        simpa [Real.norm_eq_abs] using
          norm_add_le (f₀ x) (f x - f₀ x)
      _ ≤ ‖f₀.value‖ + K :=
        add_le_add (ContinuousMap.norm_coe_le_norm f₀.value x) h1
      _ = M_val := rfl
  have h5 : |f.firstDeriv x| ≤ M_der := by
    calc
      |f.firstDeriv x| ≤
          |f₀.firstDeriv x| +
            |f.firstDeriv x - f₀.firstDeriv x| := by
        have h :
            f.firstDeriv x =
              f₀.firstDeriv x +
                (f.firstDeriv x - f₀.firstDeriv x) := by
          ring
        rw [h]
        simpa [Real.norm_eq_abs] using
          norm_add_le (f₀.firstDeriv x)
            (f.firstDeriv x - f₀.firstDeriv x)
      _ ≤ ‖f₀.firstDeriv‖ + K :=
        add_le_add
          (ContinuousMap.norm_coe_le_norm f₀.firstDeriv x) h2
      _ = M_der := rfl
  have h6 : |f.secondDeriv x| ≤ M_der2 := by
    calc
      |f.secondDeriv x| ≤
          |f₀.secondDeriv x| +
            |f.secondDeriv x - f₀.secondDeriv x| := by
        have h :
            f.secondDeriv x =
              f₀.secondDeriv x +
                (f.secondDeriv x - f₀.secondDeriv x) := by
          ring
        rw [h]
        simpa [Real.norm_eq_abs] using
          norm_add_le (f₀.secondDeriv x)
            (f.secondDeriv x - f₀.secondDeriv x)
      _ ≤ ‖f₀.secondDeriv‖ + K :=
        add_le_add
          (ContinuousMap.norm_coe_le_norm f₀.secondDeriv x) h3
      _ = M_der2 := rfl
  exact
    ⟨h4.trans (le_max_left _ _),
      h5.trans ((le_max_left _ _).trans (le_max_right _ _)),
      h6.trans ((le_max_right _ _).trans (le_max_right _ _))⟩

lemma localAssembly_representative_multiplicity
    {F : FiniteFunctionFamily} {δ : ℝ}
    {E₀ : Set (ℝ × ℝ)} {μ : ℕ}
    (hE₀ : ∀ p ∈ E₀, (μ : ℝ) ≤ multiplicity F δ p)
    {p : ℝ × ℝ} (hp : p ∈ E₀) :
    μ ≤ (F.toFinset.filter
      (fun f => p ∈ graphNeighborhood f δ)).card := by
  have h1 : (μ : ℝ) ≤ multiplicity F δ p := hE₀ p hp
  have h2 :
      multiplicity F δ p =
        ∑ f ∈ F.toFinset,
          if p ∈ graphNeighborhood f δ then (1 : ℝ) else 0 := by
    unfold multiplicity
    apply Finset.sum_congr rfl
    intro f _
    simp [Set.indicator_apply]
  rw [h2] at h1
  have h3 :
      (∑ f ∈ F.toFinset,
        if p ∈ graphNeighborhood f δ then (1 : ℝ) else 0) =
          ((F.toFinset.filter
            (fun f => p ∈ graphNeighborhood f δ)).card : ℝ) := by
    rw [Finset.sum_ite]
    simp
  rw [h3] at h1
  exact_mod_cast h1

lemma localAssembly_cinematic_family_lipschitz_bound
    {family : Set C2Function} {K D : ℝ}
    (hfamily : IsCinematicFamily family K D)
    (hfamily_nonempty : family.Nonempty) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ f ∈ family, ∀ x y : UnitPoint,
        |f x - f y| ≤ L * |(x : ℝ) - (y : ℝ)| := by
  rcases hfamily_nonempty with ⟨f₀, hf₀⟩
  rcases localAssembly_cinematic_uniform_bounds hfamily hf₀ with
    ⟨L, hL, hbounds⟩
  refine ⟨L, hL, ?_⟩
  intro f hf x y
  have hderiv : ∀ z : UnitPoint, |f.firstDeriv z| ≤ L :=
    fun z => (hbounds f hf z).2.1
  have hdiff : Differentiable ℝ f.extension :=
    ContDiff.differentiable f.extension_contDiff (by norm_num)
  have hdiffAt :
      ∀ z ∈ (Set.Icc 0 1 : Set ℝ),
        DifferentiableAt ℝ f.extension z :=
    fun z _ => hdiff.differentiableAt
  have hderiv_real :
      ∀ z ∈ (Set.Icc 0 1 : Set ℝ),
        ‖deriv f.extension z‖ ≤ L := by
    intro z hz
    let z' : UnitPoint := ⟨z, hz⟩
    rw [f.deriv_extension_eq_firstDeriv z']
    simpa [Real.norm_eq_abs] using hderiv z'
  have h :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      hdiffAt hderiv_real (convex_Icc 0 1) x.prop y.prop
  rw [f.extension_eq_value, f.extension_eq_value] at h
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

lemma localAssembly_graphNeighborhood_to_vertical
    {f : C2Function} {δ L : ℝ}
    (hderiv : ∀ z : UnitPoint, |f.firstDeriv z| ≤ L)
    {p : ℝ × ℝ} (hp1 : p.1 ∈ unitInterval)
    (h : p ∈ graphNeighborhood f δ) :
    |p.2 - f ⟨p.1, hp1⟩| ≤ (1 + L) * δ := by
  rcases localAssembly_graph_neighborhood_exists h with
    ⟨x', hx', hy'⟩
  let x : UnitPoint := ⟨p.1, hp1⟩
  have hx : |(x : ℝ) - (x' : ℝ)| < δ := by
    simpa [x] using hx'
  exact localAssembly_vertical_bound_with_derivative hderiv hx hy'

lemma graphNeighborhood_to_vertical_of_uniform_bound
    {family : Set C2Function} {L δ : ℝ}
    (hbound : HasUniformFirstDerivativeBound family L)
    {f : C2Function} (hf : f ∈ family)
    {p : ℝ × ℝ} (hp1 : p.1 ∈ unitInterval)
    (hp : p ∈ graphNeighborhood f δ) :
    |p.2 - f ⟨p.1, hp1⟩| ≤ (1 + L) * δ := by
  exact localAssembly_graphNeighborhood_to_vertical
    (hbound hf) hp1 hp

lemma multiplicity_le_vertical_of_uniform_bound
    {family : Set C2Function} {L δ : ℝ}
    (hbound : HasUniformFirstDerivativeBound family L)
    {F : FiniteFunctionFamily} (hF : F.carrier ⊆ family)
    {p : ℝ × ℝ} (hp1 : p.1 ∈ unitInterval) :
    multiplicity F δ p ≤
      ∑ f ∈ F.toFinset,
        (if |p.2 - f ⟨p.1, hp1⟩| ≤ (1 + L) * δ
          then (1 : ℝ) else 0) := by
  classical
  unfold multiplicity
  apply Finset.sum_le_sum
  intro f hf
  have hf_carrier : f ∈ F.carrier :=
    F.finite.mem_toFinset.mp hf
  by_cases hp : p ∈ graphNeighborhood f δ
  · rw [Set.indicator_of_mem hp]
    have hvertical :=
      localAssembly_graphNeighborhood_to_vertical
        (hbound (hF hf_carrier)) hp1 hp
    simp only [if_pos hvertical]
    norm_num
  · rw [Set.indicator_of_notMem hp]
    split_ifs <;> norm_num

lemma localAssembly_metric_multiplicity_to_vertical
    {family : Set C2Function} {K D δ : ℝ}
    (hfamily : IsCinematicFamily family K D)
    (hfamily_nonempty : family.Nonempty)
    {F : FiniteFunctionFamily} (hF : F.carrier ⊆ family)
    {p : ℝ × ℝ} (hp1 : p.1 ∈ unitInterval) :
    ∃ L : ℝ, 0 ≤ L ∧
      multiplicity F δ p ≤
        ∑ f ∈ F.toFinset,
          (if |p.2 - f ⟨p.1, hp1⟩| ≤ (1 + L) * δ
            then (1 : ℝ) else 0) := by
  classical
  rcases hfamily_nonempty with ⟨f₀, hf₀⟩
  rcases localAssembly_cinematic_uniform_bounds hfamily
      hf₀ with
    ⟨L, hL, hbounds⟩
  refine ⟨L, hL, ?_⟩
  unfold multiplicity
  apply Finset.sum_le_sum
  intro f hf
  have hf_carrier : f ∈ F.carrier :=
    F.finite.mem_toFinset.mp hf
  by_cases hp : p ∈ graphNeighborhood f δ
  · rw [Set.indicator_of_mem hp]
    have hvertical :=
      localAssembly_graphNeighborhood_to_vertical
        (fun z => (hbounds f (hF hf_carrier) z).2.1) hp1 hp
    simp only [if_pos hvertical]
    norm_num
  · rw [Set.indicator_of_notMem hp]
    split_ifs <;> norm_num

end Kakeya.Cinematic
