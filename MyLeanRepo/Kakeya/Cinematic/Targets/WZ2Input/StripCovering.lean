import MyLeanRepo.Kakeya.Cinematic.Definitions
import MyLeanRepo.Kakeya.Cinematic.Translation
import MyLeanRepo.Kakeya.Cinematic.Targets.WZ2Input.IntegrableMultiplicity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Strip covering lemma for cinematic multiplicity

## Main result

`strip_covering_integral_bound`: if every unit vertical strip has integral ≤ B_strip,
then the global integral is ≤ 3*(2*M+5)*B_strip.
-/

noncomputable section

open Kakeya.Cinematic MeasureTheory Set

namespace Kakeya.Cinematic

/-! ### Uniform value bounds from the cinematic diameter -/

/--
A nonempty cinematic family is uniformly bounded in value after choosing one
anchor function. The bound may depend on the fixed family, which is sufficient
for `WZ2CinematicInput` because its scale threshold is chosen after the family.
-/
lemma IsCinematicFamily.exists_uniform_value_bound
    {family : Set C2Function} {K D : ℝ}
    (hfamily : IsCinematicFamily family K D)
    (hne : family.Nonempty) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ f ∈ family, ∀ x : UnitPoint, |f x| ≤ M := by
  rcases hne with ⟨f₀, hf₀⟩
  refine ⟨‖f₀.value‖ + max K 0, by positivity, ?_⟩
  intro f hf x
  have h_anchor : |f₀ x| ≤ ‖f₀.value‖ :=
    ContinuousMap.norm_coe_le_norm f₀.value x
  have h_diff : |f x - f₀ x| ≤ K := by
    exact (abs_value_sub_le_c2Distance f f₀ x).trans (hfamily.1 hf hf₀)
  have h_triangle : |f x| ≤ |f x - f₀ x| + |f₀ x| := by
    calc
      |f x| = |(f x - f₀ x) + f₀ x| := by ring_nf
      _ ≤ |f x - f₀ x| + |f₀ x| := abs_add_le _ _
  calc
    |f x| ≤ |f x - f₀ x| + |f₀ x| := h_triangle
    _ ≤ K + ‖f₀.value‖ := add_le_add h_diff h_anchor
    _ ≤ ‖f₀.value‖ + max K 0 := by
      have hK : K ≤ max K 0 := le_max_left K 0
      linarith

/-! ### Multiplicity under vertical translation -/

theorem multiplicity_translate_pointwise (F : FiniteFunctionFamily) (δ c : ℝ)
    (p : ℝ × ℝ) :
    multiplicity (F.translate c) δ p = multiplicity F δ (p.1, p.2 - c) := by
  classical
  have h_inj : Function.Injective (fun f : C2Function => f.translate c) :=
    C2Function.translate_injective c
  have h_toFinset : (F.translate c).toFinset =
      F.toFinset.image (fun f => f.translate c) := by
    ext f
    simp only [FiniteFunctionFamily.toFinset, Set.Finite.mem_toFinset,
      FiniteFunctionFamily.translate, Set.mem_image, Finset.mem_image] <;> rfl
  simp only [multiplicity]
  rw [h_toFinset]
  let g : C2Function → ℝ := fun f' => (graphNeighborhood f' δ).indicator (fun _ => 1) p
  have h_injOn : Set.InjOn (fun f : C2Function => f.translate c) (↑F.toFinset) :=
    fun x _ y _ h => h_inj h
  have h_sum : ∑ f' ∈ F.toFinset.image (fun f => f.translate c), g f' =
      ∑ f ∈ F.toFinset, g (f.translate c) :=
    Finset.sum_image h_injOn
  rw [h_sum]
  apply Finset.sum_congr rfl
  intro f _
  have h_iff : p ∈ graphNeighborhood (f.translate c) δ ↔
      (p.1, p.2 - c) ∈ graphNeighborhood f δ := by
    simp only [graphNeighborhood, Metric.mem_thickening_iff]
    constructor
    · rintro ⟨q, hq, hdist⟩
      have hq1 : q.1 ∈ unitInterval := hq.1
      let q' : ℝ × ℝ := (q.1, q.2 - c)
      have hq'_graph : q' ∈ functionGraph f := by
        simp only [q', functionGraph, Set.mem_setOf_eq]
        have hq2 : q.2 = (f.translate c) ⟨q.1, hq1⟩ := hq.2
        exact ⟨hq1, by simp [C2Function.translate_apply, hq2] <;> linarith⟩
      have h_dist' : dist (p.1, p.2 - c) q' = dist p q := by
        simp [q', Prod.dist_eq, Real.dist_eq] <;> rfl
      exact ⟨q', hq'_graph, by rw [h_dist']; exact hdist⟩
    · rintro ⟨q, hq, hdist⟩
      have hq1 : q.1 ∈ unitInterval := hq.1
      let q' : ℝ × ℝ := (q.1, q.2 + c)
      have hq'_graph : q' ∈ functionGraph (f.translate c) := by
        simp only [q', functionGraph, Set.mem_setOf_eq, C2Function.translate_apply]
        exact ⟨hq1, by linarith [hq.2]⟩
      have h_dist' : dist p q' = dist (p.1, p.2 - c) q := by
        simp [q', Prod.dist_eq, Real.dist_eq] <;> rfl
      exact ⟨q', hq'_graph, by rw [h_dist']; exact hdist⟩
  have h_indic : g (f.translate c) =
      (graphNeighborhood f δ).indicator (fun _ => 1) (p.1, p.2 - c) := by
    have h_eq : g (f.translate c) =
        (graphNeighborhood (f.translate c) δ).indicator (fun _ => 1) p := by rfl
    rw [h_eq, Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> tauto
  exact h_indic

theorem integral_translate_strip (F : FiniteFunctionFamily) (δ c : ℝ) :
    ∫ p in (Set.Icc 0 1 ×ˢ Set.Icc c (c + 1)),
        Real.rpow (multiplicity F δ p) (3 / 2 : ℝ)
    = ∫ p in (Set.Icc 0 1 ×ˢ Set.Icc 0 1),
        Real.rpow (multiplicity (F.translate (-c)) δ p) (3 / 2 : ℝ) := by
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toFun := fun p => (p.1, p.2 + c),
      invFun := fun p => (p.1, p.2 - c),
      left_inv := by intro p; ext <;> simp <;> ring,
      right_inv := by intro p; ext <;> simp <;> ring,
      measurable_toFun := Measurable.prodMk measurable_fst (measurable_snd.add measurable_const),
      measurable_invFun := Measurable.prodMk measurable_fst (measurable_snd.sub measurable_const) }
  have hmp : MeasurePreserving e volume volume := by
    have h_id : MeasurePreserving (id : ℝ → ℝ) volume volume :=
      MeasurePreserving.id volume
    have h_add : MeasurePreserving (fun y : ℝ => y + c) volume volume :=
      MeasureTheory.measurePreserving_add_right volume c
    exact MeasurePreserving.prod h_id h_add
  let S := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  let T := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc c (c + 1)
  have h_image : e '' S = T := by
    ext z
    simp only [S, T, Set.mem_image, Set.mem_prod, Set.mem_Icc]
    constructor
    · rintro ⟨p, hp, hpeq⟩
      have hpeq' : (p.1, p.2 + c) = z := by simpa [e] using hpeq
      have hpeq'' : (p.1, p.2 + c) = (z.1, z.2) := hpeq'
      have hx : p.1 = z.1 := (Prod.ext_iff.mp hpeq'').1
      have hy : p.2 + c = z.2 := (Prod.ext_iff.mp hpeq'').2
      exact ⟨⟨by linarith [hp.1.1, hx], by linarith [hp.1.2, hx]⟩,
        ⟨by linarith [hp.2.1, hy], by linarith [hp.2.2, hy]⟩⟩
    · rintro ⟨hx, hy⟩
      refine' ⟨(z.1, z.2 - c), ⟨hx, _⟩, _⟩
      · exact ⟨by linarith, by linarith⟩
      · have h : e (z.1, z.2 - c) = z := by
          ext <;> simp [e] <;> ring
        exact h
  let g : ℝ × ℝ → ℝ := fun p => Real.rpow (multiplicity F δ p) (3 / 2 : ℝ)
  have h_eq1 : ∫ p in e '' S, g p = ∫ p in S, g (e p) :=
    hmp.setIntegral_image_emb (MeasurableEquiv.measurableEmbedding e) g S
  have h_eq2 : ∫ p in T, g p = ∫ p in S, g (e p) := by
    have h : ∫ p in e '' S, g p = ∫ p in T, g p := by
      congr with p <;> rw [h_image]
    exact h.symm.trans h_eq1
  have h3 : ∀ p : ℝ × ℝ, g (e p) =
      Real.rpow (multiplicity (F.translate (-c)) δ p) (3 / 2 : ℝ) := by
    intro p
    have h4 : multiplicity F δ (e p) = multiplicity (F.translate (-c)) δ p := by
      have h5 := multiplicity_translate_pointwise F δ (-c) p
      simpa [e] using Eq.symm h5
    dsimp only [g]
    rw [h4]
  rw [h_eq2]
  congr with p
  exact h3 p

/-! ### Boundary reflection -/

private lemma graphNeighborhood_left_reflect (f : C2Function) {δ x y : ℝ}
    (hδ : 0 < δ) (hx1 : -δ ≤ x) (hx2 : x ≤ 0) :
    (x, y) ∈ graphNeighborhood f δ → (-x, y) ∈ graphNeighborhood f δ := by
  intro hmem
  have h_ex : ∃ (q : ℝ × ℝ), q ∈ functionGraph f ∧ dist (x, y) q < δ :=
    Metric.mem_thickening_iff.mp hmem
  rcases h_ex with ⟨q, hq, hdist⟩
  have hq1 : q.1 ∈ Set.Icc (0 : ℝ) 1 := hq.1
  have h_xdist : |x - q.1| < δ := by
    have h : dist (x, y) q = max (|x - q.1|) (|y - q.2|) := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [h] at hdist
    exact lt_of_le_of_lt (le_max_left _ _) hdist
  have h_ydist : |y - q.2| < δ := by
    have h : dist (x, y) q = max (|x - q.1|) (|y - q.2|) := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [h] at hdist
    exact lt_of_le_of_lt (le_max_right _ _) hdist
  have h_q1_nonneg : 0 ≤ q.1 := hq1.1
  have h_lower : -δ < x + q.1 := by
    have h21 : -δ ≤ x + q.1 := by linarith
    have h22 : x + q.1 ≠ -δ := by
      intro h_eq
      have hx_eq : x = -δ := by linarith [hx1, h_q1_nonneg]
      have hq_eq : q.1 = 0 := by linarith [hx1, h_q1_nonneg]
      have h_contra : |x - q.1| = δ := by
        rw [hx_eq, hq_eq] <;> simp [abs_of_pos hδ]
      rw [h_contra] at h_xdist
      exact lt_irrefl δ h_xdist
    have h22' : -δ ≠ x + q.1 := by
      intro h
      exact h22 h.symm
    exact lt_of_le_of_ne h21 h22'
  have h_upper : x + q.1 < δ := by
    have h_abs : |x - q.1| = |q.1 - x| := by
      have h : x - q.1 = -(q.1 - x) := by ring
      rw [h, abs_neg]
    have h4 : q.1 - x ≤ |x - q.1| := by
      rw [h_abs]
      exact le_abs_self (q.1 - x)
    have h5 : q.1 - x < δ := lt_of_le_of_lt h4 h_xdist
    have h6 : x + q.1 ≤ q.1 - x := by linarith
    linarith
  have h_eq1 : (-x) - q.1 = -(x + q.1) := by ring
  have h_reflect : |(-x) - q.1| < δ := by
    rw [h_eq1, abs_neg]
    exact abs_lt.mpr ⟨h_lower, h_upper⟩
  have h_dist' : dist (-x, y) q < δ := by
    have h1 : dist (-x, y) q = max (dist (-x) q.1) (dist y q.2) := Prod.dist_eq
    have h2 : dist (-x) q.1 = |(-x) - q.1| := by rw [Real.dist_eq]
    have h3 : dist y q.2 = |y - q.2| := by rw [Real.dist_eq]
    rw [h1, h2, h3]
    exact max_lt h_reflect h_ydist
  exact Metric.mem_thickening_iff.mpr ⟨q, hq, h_dist'⟩

private lemma graphNeighborhood_right_reflect (f : C2Function) {δ x y : ℝ}
    (hδ : 0 < δ) (hx1 : 1 ≤ x) (hx2 : x ≤ 1 + δ) :
    (x, y) ∈ graphNeighborhood f δ → (2 - x, y) ∈ graphNeighborhood f δ := by
  intro hmem
  have h_ex : ∃ (q : ℝ × ℝ), q ∈ functionGraph f ∧ dist (x, y) q < δ :=
    Metric.mem_thickening_iff.mp hmem
  rcases h_ex with ⟨q, hq, hdist⟩
  have hq1 : q.1 ∈ Set.Icc (0 : ℝ) 1 := hq.1
  have h_xdist : |x - q.1| < δ := by
    have h : dist (x, y) q = max (|x - q.1|) (|y - q.2|) := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [h] at hdist
    exact lt_of_le_of_lt (le_max_left _ _) hdist
  have h_ydist : |y - q.2| < δ := by
    have h : dist (x, y) q = max (|x - q.1|) (|y - q.2|) := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [h] at hdist
    exact lt_of_le_of_lt (le_max_right _ _) hdist
  have h_q1_le_one : q.1 ≤ 1 := hq1.2
  have h_q1_gt : q.1 > 1 - δ := by
    have h4 : x - q.1 ≤ |x - q.1| := le_abs_self (x - q.1)
    have h5 : x - q.1 < δ := lt_of_le_of_lt h4 h_xdist
    linarith
  have h_lower : -δ < 2 - x - q.1 := by
    have h21 : -δ ≤ 2 - x - q.1 := by linarith
    have h22 : 2 - x - q.1 ≠ -δ := by
      intro h_eq
      have hx_eq : x = 1 + δ := by linarith [hx1, hx2, h_q1_le_one]
      have hq_eq : q.1 = 1 := by linarith [hx1, hx2, h_q1_le_one]
      have h_contra : |x - q.1| = δ := by
        rw [hx_eq, hq_eq] <;> simp [abs_of_pos hδ]
      rw [h_contra] at h_xdist
      exact lt_irrefl δ h_xdist
    have h22' : -δ ≠ 2 - x - q.1 := by
      intro h
      exact h22 h.symm
    exact lt_of_le_of_ne h21 h22'
  have h_upper : 2 - x - q.1 < δ := by linarith [h_q1_gt]
  have h_eq1 : (2 - x) - q.1 = 2 - x - q.1 := by ring
  have h_reflect : |(2 - x) - q.1| < δ := by
    rw [h_eq1]
    exact abs_lt.mpr ⟨h_lower, h_upper⟩
  have h_dist' : dist (2 - x, y) q < δ := by
    have h1 : dist (2 - x, y) q = max (dist (2 - x) q.1) (dist y q.2) := Prod.dist_eq
    have h2 : dist (2 - x) q.1 = |(2 - x) - q.1| := by rw [Real.dist_eq]
    have h3 : dist y q.2 = |y - q.2| := by rw [Real.dist_eq]
    rw [h1, h2, h3]
    exact max_lt h_reflect h_ydist
  exact Metric.mem_thickening_iff.mpr ⟨q, hq, h_dist'⟩

/-- Multiplicity at left boundary ≤ multiplicity at reflected interior point. -/
lemma multiplicity_left_reflect (F : FiniteFunctionFamily) {δ x y : ℝ}
    (hδ : 0 < δ) (hx1 : -δ ≤ x) (hx2 : x ≤ 0) :
    multiplicity F δ (x, y) ≤ multiplicity F δ (-x, y) := by
  classical
  dsimp only [multiplicity]
  apply Finset.sum_le_sum
  intro f _
  have h : (x, y) ∈ graphNeighborhood f δ → (-x, y) ∈ graphNeighborhood f δ :=
    graphNeighborhood_left_reflect f hδ hx1 hx2
  by_cases hcase : (x, y) ∈ graphNeighborhood f δ
  · have hcase' : (-x, y) ∈ graphNeighborhood f δ := h hcase
    rw [Set.indicator_apply, Set.indicator_apply, if_pos hcase, if_pos hcase']
  · rw [Set.indicator_apply, if_neg hcase]
    exact Set.indicator_nonneg (fun _ => by norm_num) _

/-- Multiplicity at right boundary ≤ multiplicity at reflected interior point. -/
lemma multiplicity_right_reflect (F : FiniteFunctionFamily) {δ x y : ℝ}
    (hδ : 0 < δ) (hx1 : 1 ≤ x) (hx2 : x ≤ 1 + δ) :
    multiplicity F δ (x, y) ≤ multiplicity F δ (2 - x, y) := by
  classical
  dsimp only [multiplicity]
  apply Finset.sum_le_sum
  intro f _
  have h : (x, y) ∈ graphNeighborhood f δ → (2 - x, y) ∈ graphNeighborhood f δ :=
    graphNeighborhood_right_reflect f hδ hx1 hx2
  by_cases hcase : (x, y) ∈ graphNeighborhood f δ
  · have hcase' : (2 - x, y) ∈ graphNeighborhood f δ := h hcase
    rw [Set.indicator_apply, Set.indicator_apply, if_pos hcase, if_pos hcase']
  · rw [Set.indicator_apply, if_neg hcase]
    exact Set.indicator_nonneg (fun _ => by norm_num) _

/-! ### Support of multiplicity -/

/-- Multiplicity is zero when x is outside (-δ, 1+δ). -/
lemma multiplicity_outside_x_range (F : FiniteFunctionFamily) (δ : ℝ) (hδ : 0 < δ)
    (x y : ℝ) (h : x < -δ ∨ x > 1 + δ) :
    multiplicity F δ (x, y) = 0 := by
  classical
  dsimp only [multiplicity]
  apply Finset.sum_eq_zero
  intro f _
  rw [Set.indicator_apply, if_neg]
  intro hmem
  have h_ex : ∃ (q : ℝ × ℝ), q ∈ functionGraph f ∧ dist (x, y) q < δ :=
    Metric.mem_thickening_iff.mp hmem
  rcases h_ex with ⟨q, hq, hdist⟩
  have hq1 : q.1 ∈ Set.Icc (0 : ℝ) 1 := hq.1
  have h_xdist : |x - q.1| < δ := by
    have h : dist (x, y) q = max (|x - q.1|) (|y - q.2|) := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [h] at hdist
    exact lt_of_le_of_lt (le_max_left _ _) hdist
  have h1 : -δ < x := by
    have h2 : -δ < x - q.1 := (abs_lt.mp h_xdist).1
    linarith [hq1.1]
  have h2 : x < 1 + δ := by
    have h3 : x - q.1 < δ := (abs_lt.mp h_xdist).2
    linarith [hq1.2]
  cases h with
  | inl h => linarith
  | inr h => linarith

/-- Multiplicity is zero when y is outside (-M-δ, M+δ). -/
lemma multiplicity_outside_y_range (F : FiniteFunctionFamily) (δ M_val : ℝ)
    (hδ : 0 < δ) (hM : ∀ f ∈ F.carrier, ∀ x : UnitPoint, |f x| ≤ M_val)
    (x y : ℝ) (hy : y < -M_val - δ ∨ y > M_val + δ) :
    multiplicity F δ (x, y) = 0 := by
  classical
  dsimp only [multiplicity]
  apply Finset.sum_eq_zero
  intro f hf
  rw [Set.indicator_apply, if_neg]
  intro hmem
  have h_ex : ∃ (q : ℝ × ℝ), q ∈ functionGraph f ∧ dist (x, y) q < δ :=
    Metric.mem_thickening_iff.mp hmem
  rcases h_ex with ⟨q, hq, hdist⟩
  have hq1 : q.1 ∈ Set.Icc (0 : ℝ) 1 := hq.1
  have hq2 : q.2 = f ⟨q.1, hq1⟩ := hq.2
  have hf_carrier : f ∈ F.carrier := by
    have h : f ∈ F.toFinset := hf
    simpa [FiniteFunctionFamily.toFinset, Set.Finite.mem_toFinset] using h
  have hM_f : |f ⟨q.1, hq1⟩| ≤ M_val := hM f hf_carrier ⟨q.1, hq1⟩
  have hq2_bdd : |q.2| ≤ M_val := by
    rw [hq2] <;> exact hM_f
  have h_ydist : |y - q.2| < δ := by
    have h : dist (x, y) q = max (|x - q.1|) (|y - q.2|) := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [h] at hdist
    exact lt_of_le_of_lt (le_max_right _ _) hdist
  have h1 : -M_val - δ < y := by
    have h2 : -δ < y - q.2 := (abs_lt.mp h_ydist).1
    have h3 : -M_val ≤ q.2 := (abs_le.mp hq2_bdd).1
    linarith
  have h2 : y < M_val + δ := by
    have h3 : y - q.2 < δ := (abs_lt.mp h_ydist).2
    have h4 : q.2 ≤ M_val := (abs_le.mp hq2_bdd).2
    linarith
  cases hy with
  | inl hy => linarith
  | inr hy => linarith


/-! ### Integral subadditivity -/

private lemma integral_union_le {f : ℝ × ℝ → ℝ} {s t : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h_int : Integrable f volume) (h_nonneg : ∀ x, 0 ≤ f x) :
    ∫ p in s ∪ t, f p ≤ (∫ p in s, f p) + (∫ p in t, f p) := by
  have h1 : s ∪ t = s ∪ (t \ s) := by
    ext x; simp [Set.mem_union] <;> tauto
  have h_disj : Disjoint s (t \ s) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact hx2.2 hx1
  have h_meas : MeasurableSet (t \ s) := ht.diff hs
  have h_ints : IntegrableOn f s volume := h_int.integrableOn
  have h_intt : IntegrableOn f (t \ s) volume := h_int.integrableOn
  have h_eq : ∫ p in s ∪ (t \ s), f p =
      (∫ p in s, f p) + (∫ p in (t \ s), f p) :=
    setIntegral_union h_disj h_meas h_ints h_intt
  rw [h1, h_eq]
  have h_sub : ∫ p in (t \ s), f p ≤ ∫ p in t, f p := by
    apply setIntegral_mono_set h_int.integrableOn
    · filter_upwards with x
      exact h_nonneg x
    · have hst : (t \ s) ≤ᵐ[volume] t := by
        filter_upwards with x hx
        exact hx.1
      exact hst
  linarith

private lemma setIntegral_finite_subadditivity {f : ℝ × ℝ → ℝ} {ι : Type*}
    (s : Finset ι) (t : ι → Set (ℝ × ℝ)) (ht : ∀ i, MeasurableSet (t i))
    (h_int : Integrable f volume) (h_nonneg : ∀ x, 0 ≤ f x) :
    ∫ p in (⋃ i ∈ s, t i), f p ≤ ∑ i ∈ s, ∫ p in t i, f p := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h : (⋃ i ∈ (∅ : Finset ι), t i) = (∅ : Set (ℝ × ℝ)) := by simp
    rw [h] <;> simp
  | @insert i s hi ih =>
    have h_union_set : (⋃ j ∈ (insert i s), t j) = (t i) ∪ (⋃ j ∈ s, t j) := by
      ext x; simp [Finset.mem_insert] <;> tauto
    have h_sum : (∑ j ∈ (insert i s), ∫ p in t j, f p) =
        (∫ p in t i, f p) + ∑ j ∈ s, ∫ p in t j, f p := by
      rw [Finset.sum_insert hi] <;> rfl
    rw [h_union_set, h_sum]
    have h_meas : MeasurableSet (⋃ j ∈ s, t j) :=
      Finset.measurableSet_biUnion s (fun j _ => ht j)
    have h_step : ∫ p in (t i) ∪ (⋃ j ∈ s, t j), f p ≤
        (∫ p in t i, f p) + (∫ p in (⋃ j ∈ s, t j), f p) :=
      integral_union_le (ht i) h_meas h_int h_nonneg
    have h_ih' : (∫ p in t i, f p) + (∫ p in (⋃ j ∈ s, t j), f p) ≤
        (∫ p in t i, f p) + ∑ j ∈ s, ∫ p in t j, f p :=
      add_le_add_right ih (∫ p in t i, f p)
    exact le_trans h_step h_ih'

/-! ### Strip covering bound -/

/-- If every unit vertical strip has multiplicity^(3/2) integral ≤ B_strip,
and all function values are bounded by M_val, then the global integral is
≤ 3 * (2 * M_val + 5) * B_strip. -/
lemma strip_covering_integral_bound (F : FiniteFunctionFamily) (δ M_val B_strip : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : ∀ f ∈ F.carrier, ∀ x : UnitPoint, |f x| ≤ M_val)
    (hM_nonneg : 0 ≤ M_val) (hB_nonneg : 0 ≤ B_strip)
    (h_strip_bound : ∀ (c : ℝ), ∫ p in (Set.Icc 0 1 ×ˢ Set.Icc c (c + 1)),
        Real.rpow (multiplicity F δ p) (3 / 2 : ℝ) ≤ B_strip)
    (h_int : Integrable (fun p => Real.rpow (multiplicity F δ p) (3 / 2 : ℝ)) volume) :
    ∫ p, Real.rpow (multiplicity F δ p) (3 / 2 : ℝ) ≤
    3 * (2 * M_val + 5) * B_strip := by
  let f : ℝ × ℝ → ℝ := fun p => Real.rpow (multiplicity F δ p) (3 / 2 : ℝ)
  have h_nonneg : ∀ p, 0 ≤ f p := by
    intro p
    have h1 : 0 ≤ multiplicity F δ p := by
      dsimp only [multiplicity]
      apply Finset.sum_nonneg
      intro f _
      exact Set.indicator_nonneg (fun _ => by norm_num) _
    exact Real.rpow_nonneg h1 _
  have h_mult_nonneg : ∀ p, 0 ≤ multiplicity F δ p := by
    intro p
    dsimp only [multiplicity]
    apply Finset.sum_nonneg
    intro f _
    exact Set.indicator_nonneg (fun _ => by norm_num) _
  let L := Set.Icc (-δ) 0 ×ˢ (Set.univ : Set ℝ)
  let I := Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)
  let R := Set.Icc (1 : ℝ) (1 + δ) ×ˢ (Set.univ : Set ℝ)
  let full := Set.Icc (-δ) (1 + δ) ×ˢ (Set.univ : Set ℝ)
  have hL_meas : MeasurableSet L := IsClosed.measurableSet isClosed_Icc |>.prod MeasurableSet.univ
  have hI_meas : MeasurableSet I := IsClosed.measurableSet isClosed_Icc |>.prod MeasurableSet.univ
  have hR_meas : MeasurableSet R := IsClosed.measurableSet isClosed_Icc |>.prod MeasurableSet.univ
  have hfull_meas : MeasurableSet full := IsClosed.measurableSet isClosed_Icc |>.prod MeasurableSet.univ
  -- Support in x
  have h_support : ∀ p, p ∉ full → f p = 0 := by
    intro p hp
    have h' : p.1 ∉ Set.Icc (-δ) (1 + δ) := by
      simpa [full, Set.mem_prod] using hp
    have h5 : ¬(-δ ≤ p.1 ∧ p.1 ≤ 1 + δ) := by simpa [Set.mem_Icc] using h'
    have h4 : p.1 < -δ ∨ p.1 > 1 + δ := by
      by_cases h6 : p.1 < -δ
      · exact Or.inl h6
      · have h7 : -δ ≤ p.1 := by linarith
        have h8 : ¬(p.1 ≤ 1 + δ) := by
          intro h9
          exact h5 ⟨h7, h9⟩
        have h9 : p.1 > 1 + δ := by linarith
        exact Or.inr h9
    have h6 : multiplicity F δ p = 0 := multiplicity_outside_x_range F δ hδ p.1 p.2 h4
    dsimp only [f]
    rw [h6] <;> simp
  have h_univ_eq : ∫ p, f p = ∫ p in full, f p := by
    have h_ae : f =ᵐ[volume] full.indicator f := by
      filter_upwards with p
      by_cases hp : p ∈ full
      · simp [hp, Set.indicator_apply]
      · have h_f : f p = 0 := h_support p hp
        simp [hp, h_f, Set.indicator_apply]
    have h1 : ∫ p, f p = ∫ p, full.indicator f p := integral_congr_ae h_ae
    rw [h1, integral_indicator hfull_meas]
  -- full = L ∪ I ∪ R via interval decomposition
  have h1_interval : Set.Icc (-δ) (1 + δ) =
      Set.Icc (-δ) 0 ∪ Set.Icc 0 1 ∪ Set.Icc 1 (1 + δ) := by
    ext x
    simp only [Set.mem_Icc, Set.mem_union]
    constructor
    · intro h
      have h1 : -δ ≤ x := h.1
      have h2 : x ≤ 1 + δ := h.2
      by_cases h3 : x ≤ 0
      · exact Or.inl (Or.inl ⟨h1, h3⟩)
      · have h4 : 0 ≤ x := by linarith
        by_cases h5 : x ≤ 1
        · exact Or.inl (Or.inr ⟨h4, h5⟩)
        · exact Or.inr ⟨by linarith, h2⟩
    · intro h
      rcases h with (h | h)
      · rcases h with (h | h)
        · exact ⟨h.1, by linarith⟩
        · exact ⟨by linarith [hδ], by linarith⟩
      · exact ⟨by linarith, h.2⟩
  have h_full_eq : full = L ∪ I ∪ R := by
    ext p
    simp only [full, L, I, R, Set.mem_prod, Set.mem_univ]
    rw [h1_interval]
    <;> simp [Set.prod_union]
    <;> tauto
  -- Subadditivity over L, I, R
  have h_sub : ∫ p in full, f p ≤
      (∫ p in L, f p) + (∫ p in I, f p) + (∫ p in R, f p) := by
    rw [h_full_eq]
    have h1 : ∫ p in (L ∪ I) ∪ R, f p ≤
        (∫ p in L ∪ I, f p) + (∫ p in R, f p) :=
      integral_union_le (hL_meas.union hI_meas) hR_meas h_int h_nonneg
    have h2 : ∫ p in L ∪ I, f p ≤ (∫ p in L, f p) + (∫ p in I, f p) :=
      integral_union_le hL_meas hI_meas h_int h_nonneg
    linarith
  -- Reflection maps
  let neg_equiv : ℝ ≃ₗᵢ[ℝ] ℝ := LinearIsometryEquiv.neg ℝ
  have hmp_neg : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    LinearIsometryEquiv.measurePreserving neg_equiv
  have hmp_id : MeasurePreserving (id : ℝ → ℝ) volume volume :=
    MeasurePreserving.id volume
  let e_left : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toFun := fun p => (-p.1, p.2),
      invFun := fun p => (-p.1, p.2),
      left_inv := by intro p; ext <;> simp,
      right_inv := by intro p; ext <;> simp,
      measurable_toFun := Measurable.prodMk measurable_fst.neg measurable_snd,
      measurable_invFun := Measurable.prodMk measurable_fst.neg measurable_snd }
  have hmp_left : MeasurePreserving e_left volume volume :=
    MeasurePreserving.prod hmp_neg hmp_id
  let e_right : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toFun := fun p => (2 - p.1, p.2),
      invFun := fun p => (2 - p.1, p.2),
      left_inv := by intro p; ext <;> simp <;> ring,
      right_inv := by intro p; ext <;> simp <;> ring,
      measurable_toFun := Measurable.prodMk (measurable_const.sub measurable_fst) measurable_snd,
      measurable_invFun := Measurable.prodMk (measurable_const.sub measurable_fst) measurable_snd }
  let translate2 : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toFun := fun p => (p.1 + 2, p.2),
      invFun := fun p => (p.1 - 2, p.2),
      left_inv := by intro p; ext <;> simp <;> ring,
      right_inv := by intro p; ext <;> simp <;> ring,
      measurable_toFun := Measurable.prodMk (measurable_fst.add measurable_const) measurable_snd,
      measurable_invFun := Measurable.prodMk (measurable_fst.sub measurable_const) measurable_snd }
  have hmp_trans2 : MeasurePreserving translate2 volume volume :=
    MeasurePreserving.prod (MeasureTheory.measurePreserving_add_right volume 2) hmp_id
  have hmp_right : MeasurePreserving e_right volume volume := by
    have h2 : MeasurePreserving (translate2 ∘ e_left) volume volume :=
      hmp_trans2.comp hmp_left
    have h_eq : (translate2 ∘ e_left) = e_right := by
      funext p; simp [e_right, translate2, e_left] <;> ring
    exact h_eq ▸ h2
  -- Pointwise bounds
  have h_pw_left : ∀ p ∈ L, f p ≤ f (e_left p) := by
    intro p hp
    have h_mult : multiplicity F δ p ≤ multiplicity F δ (e_left p) :=
      multiplicity_left_reflect F hδ hp.1.1 hp.1.2
    exact Real.rpow_le_rpow (h_mult_nonneg p) h_mult (by norm_num)
  have h_pw_right : ∀ p ∈ R, f p ≤ f (e_right p) := by
    intro p hp
    have h_mult : multiplicity F δ p ≤ multiplicity F δ (e_right p) :=
      multiplicity_right_reflect F hδ hp.1.1 hp.1.2
    exact Real.rpow_le_rpow (h_mult_nonneg p) h_mult (by norm_num)
  let g_left := f ∘ e_left
  let g_right := f ∘ e_right
  have h_int_left : Integrable g_left volume :=
    (hmp_left.integrable_comp_emb (MeasurableEquiv.measurableEmbedding e_left) (g := f)).mpr h_int
  have h_int_right : Integrable g_right volume :=
    (hmp_right.integrable_comp_emb (MeasurableEquiv.measurableEmbedding e_right) (g := f)).mpr h_int
  have h_ints_f_L : IntegrableOn f L volume := h_int.integrableOn
  have h_ints_g_L : IntegrableOn g_left L volume := h_int_left.integrableOn
  have h_ints_f_R : IntegrableOn f R volume := h_int.integrableOn
  have h_ints_g_R : IntegrableOn g_right R volume := h_int_right.integrableOn
  -- Image calculations
  have h_image_left : e_left '' L = Set.Icc (0 : ℝ) δ ×ˢ Set.univ := by
    ext ⟨x, y⟩
    simp only [Set.mem_image, Set.mem_prod, e_left, L, Set.mem_univ]
    constructor
    · rintro ⟨p, hp, hpeq⟩
      have hpx1 : -p.1 = x := congr_arg Prod.fst hpeq
      have hpx : p.1 ∈ Set.Icc (-δ) 0 := hp.1
      have h_x_eq : x = -p.1 := hpx1.symm
      have h1 : 0 ≤ x := by rw [h_x_eq]; exact neg_nonneg.mpr hpx.2
      have h2 : x ≤ δ := by rw [h_x_eq]; exact neg_le.mpr hpx.1
      exact ⟨⟨h1, h2⟩, trivial⟩
    · rintro ⟨hx, _⟩
      have hx1 : 0 ≤ x := hx.1
      have hx2 : x ≤ δ := hx.2
      have h1 : -δ ≤ -x := by linarith
      have h2 : -x ≤ 0 := by linarith
      refine' ⟨(-x, y), ⟨⟨h1, h2⟩, trivial⟩, _⟩
      <;> simp [e_left] <;> ring
  have h_image_right : e_right '' R = Set.Icc (1 - δ) 1 ×ˢ Set.univ := by
    ext ⟨x, y⟩
    simp only [Set.mem_image, Set.mem_prod, e_right, R, Set.mem_univ]
    constructor
    · rintro ⟨p, hp, hpeq⟩
      have hpx1 : 2 - p.1 = x := congr_arg Prod.fst hpeq
      have hpx : p.1 ∈ Set.Icc (1 : ℝ) (1 + δ) := hp.1
      have h_x_eq : x = 2 - p.1 := hpx1.symm
      have h1 : 1 - δ ≤ x := by rw [h_x_eq]; linarith [hpx.2]
      have h2 : x ≤ 1 := by rw [h_x_eq]; linarith [hpx.1]
      exact ⟨⟨h1, h2⟩, trivial⟩
    · rintro ⟨hx, _⟩
      have hx1 : 1 - δ ≤ x := hx.1
      have hx2 : x ≤ 1 := hx.2
      have h1 : 1 ≤ 2 - x := by linarith
      have h2 : 2 - x ≤ 1 + δ := by linarith
      refine' ⟨(2 - x, y), ⟨⟨h1, h2⟩, trivial⟩, _⟩
      <;> simp [e_right] <;> ring
  have h_sub_left : e_left '' L ⊆ I := by
    rw [h_image_left]
    intro p hp
    have hpx1 : 0 ≤ p.1 := hp.1.1
    have hpx2 : p.1 ≤ δ := hp.1.2
    have hpx3 : p.1 ≤ 1 := by linarith [hδ1]
    exact ⟨⟨hpx1, hpx3⟩, trivial⟩
  have h_sub_right : e_right '' R ⊆ I := by
    rw [h_image_right]
    intro p hp
    have hpx1 : 1 - δ ≤ p.1 := hp.1.1
    have hpx2 : p.1 ≤ 1 := hp.1.2
    have hpx3 : 0 ≤ p.1 := by linarith [hδ1]
    exact ⟨⟨hpx3, hpx2⟩, trivial⟩
  -- Left integral bound
  have hL_bound : ∫ p in L, f p ≤ ∫ p in I, f p := by
    have h1 : ∫ p in L, f p ≤ ∫ p in L, g_left p :=
      setIntegral_mono_on h_ints_f_L h_ints_g_L hL_meas h_pw_left
    have h2 : ∫ p in L, g_left p = ∫ p in e_left '' L, f p :=
      (hmp_left.setIntegral_image_emb (MeasurableEquiv.measurableEmbedding e_left) f L).symm
    rw [h2] at h1
    have h3 : ∫ p in e_left '' L, f p ≤ ∫ p in I, f p := by
      apply setIntegral_mono_set h_int.integrableOn
      · filter_upwards with x
        exact h_nonneg x
      · have hst : (e_left '' L) ≤ᵐ[volume] I := by
          filter_upwards with x hx
          exact h_sub_left hx
        exact hst
    exact le_trans h1 h3
  -- Right integral bound
  have hR_bound : ∫ p in R, f p ≤ ∫ p in I, f p := by
    have h1 : ∫ p in R, f p ≤ ∫ p in R, g_right p :=
      setIntegral_mono_on h_ints_f_R h_ints_g_R hR_meas h_pw_right
    have h2 : ∫ p in R, g_right p = ∫ p in e_right '' R, f p :=
      (hmp_right.setIntegral_image_emb (MeasurableEquiv.measurableEmbedding e_right) f R).symm
    rw [h2] at h1
    have h3 : ∫ p in e_right '' R, f p ≤ ∫ p in I, f p := by
      apply setIntegral_mono_set h_int.integrableOn
      · filter_upwards with x
        exact h_nonneg x
      · have hst : (e_right '' R) ≤ᵐ[volume] I := by
          filter_upwards with x hx
          exact h_sub_right hx
        exact hst
    exact le_trans h1 h3
  -- Total ≤ 3 * interior
  have h_total_interior : ∫ p, f p ≤ 3 * ∫ p in I, f p := by
    calc ∫ p, f p
      = ∫ p in full, f p := h_univ_eq
    _ ≤ (∫ p in L, f p) + (∫ p in I, f p) + (∫ p in R, f p) := h_sub
    _ ≤ 3 * (∫ p in I, f p) := by linarith
  -- Strip covering in y
  let a : ℝ := -M_val - δ
  let b : ℝ := M_val + δ
  let inner := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc a b
  have hinner_meas : MeasurableSet inner :=
    (IsClosed.measurableSet isClosed_Icc).prod (IsClosed.measurableSet isClosed_Icc)
  -- Support in y
  have h_support_y : ∀ p, p ∈ I → p ∉ inner → f p = 0 := by
    intro p hI hNin
    have hyn : p.2 ∉ Set.Icc a b := by
      by_contra h
      have hpin : p ∈ inner := ⟨hI.1, h⟩
      exact hNin hpin
    have h : p.2 < a ∨ p.2 > b := by
      have h5 : ¬(a ≤ p.2 ∧ p.2 ≤ b) := by simpa [Set.mem_Icc] using hyn
      by_cases h6 : p.2 < a
      · exact Or.inl h6
      · have h7 : a ≤ p.2 := by linarith
        have h8 : ¬(p.2 ≤ b) := by
          intro h9
          exact h5 ⟨h7, h9⟩
        have h9 : p.2 > b := by linarith
        exact Or.inr h9
    have h4 : multiplicity F δ p = 0 :=
      multiplicity_outside_y_range F δ M_val hδ hM p.1 p.2 h
    dsimp only [f]
    rw [h4] <;> simp
  have h_eq_inner : ∫ p in I, f p = ∫ p in inner, f p := by
    have h_ae : ∀ᵐ p ∂volume, I.indicator f p = inner.indicator f p := by
      filter_upwards with p
      by_cases hpI : p ∈ I
      · by_cases hpin : p ∈ inner
        · simp [hpI, hpin, Set.indicator_apply]
        · have h_f : f p = 0 := h_support_y p hpI hpin
          simp [hpI, hpin, h_f, Set.indicator_apply]
      · have hpin' : p ∉ inner := by
          intro h
          exact hpI ⟨h.1, trivial⟩
        simp [hpI, hpin', Set.indicator_apply]
    have h1 : ∫ p in I, f p = ∫ p, I.indicator f p := by rw [integral_indicator hI_meas]
    have h2 : ∫ p in inner, f p = ∫ p, inner.indicator f p := by rw [integral_indicator hinner_meas]
    have h3 : ∫ p, I.indicator f p = ∫ p, inner.indicator f p := integral_congr_ae h_ae
    rw [h1, h2, h3]
  -- Cover [a,b] with integer strips
  let m_min : ℤ := Int.floor a
  let m_max : ℤ := Int.ceil b
  let S : Finset ℤ := Finset.Icc m_min m_max
  let stripSet : ℤ → Set (ℝ × ℝ) := fun m =>
    Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (m : ℝ) ((m : ℝ) + 1)
  have h_strip_meas : ∀ m : ℤ, MeasurableSet (stripSet m) := by
    intro m
    dsimp only [stripSet]
    apply MeasurableSet.prod
    · exact IsClosed.measurableSet isClosed_Icc
    · exact IsClosed.measurableSet isClosed_Icc
  have h_cover : inner ⊆ ⋃ m ∈ S, stripSet m := by
    intro p hp
    have hx : p.1 ∈ Set.Icc (0 : ℝ) 1 := hp.1
    have hy : p.2 ∈ Set.Icc a b := hp.2
    let m : ℤ := Int.floor p.2
    have hm1 : m ∈ S := by
      simp only [S, Finset.mem_Icc]
      constructor
      · exact Int.floor_le_floor (show a ≤ p.2 from hy.1)
      · have h_fl : Int.floor p.2 ≤ Int.floor b := Int.floor_le_floor hy.2
        have h_fc : Int.floor b ≤ Int.ceil b := by
          have h3 : (Int.floor b : ℝ) ≤ b := Int.floor_le b
          have h4 : b ≤ (Int.ceil b : ℝ) := Int.le_ceil b
          have h5 : (Int.floor b : ℝ) ≤ (Int.ceil b : ℝ) := by linarith
          exact_mod_cast h5
        exact le_trans h_fl h_fc
    have hm2 : p.2 ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1) := by
      exact ⟨Int.floor_le p.2, Int.lt_floor_add_one p.2 |>.le⟩
    have h_goal : ∃ (k : ℤ), k ∈ S ∧ p ∈ stripSet k := ⟨Int.floor p.2, hm1, ⟨hx, hm2⟩⟩
    simpa [Set.mem_iUnion] using h_goal
  have h_card : (S.card : ℝ) ≤ 2 * M_val + 5 := by
    have h_ab : a ≤ b := by dsimp only [a, b]; linarith [hM_nonneg, hδ]
    have h_mm : m_min ≤ m_max := by
      have h1 : (m_min : ℝ) ≤ a := Int.floor_le a
      have h2 : b ≤ (m_max : ℝ) := Int.le_ceil b
      have h3 : (m_min : ℝ) ≤ (m_max : ℝ) := by linarith
      exact_mod_cast h3
    have h1 : (S.card : ℝ) ≤ (m_max : ℝ) - (m_min : ℝ) + 1 := by
      have h_card_int : S.card = (m_max + 1 - m_min).toNat := Int.card_Icc m_min m_max
      rw [h_card_int]
      have h_nonneg2 : 0 ≤ m_max + 1 - m_min := by omega
      let k : ℕ := (m_max + 1 - m_min).natAbs
      have hk : (m_max + 1 - m_min : ℤ) = (k : ℤ) := (Int.natAbs_of_nonneg h_nonneg2).symm
      have h_toNat : (m_max + 1 - m_min).toNat = k := by
        have h9 : (m_max + 1 - m_min) = (k : ℤ) := hk
        simp [h9, Int.toNat]
        <;> omega
      rw [h_toNat]
      have h10 : (k : ℝ) = ((m_max + 1 - m_min : ℤ) : ℝ) := by
        exact_mod_cast hk.symm
      rw [h10]
      <;> norm_cast <;> linarith
    have h2 : (m_max : ℝ) < b + 1 := Int.ceil_lt_add_one b
    have h2' : (m_max : ℝ) ≤ b + 1 := h2.le
    have h3 : (m_min : ℝ) ≥ a - 1 := by
      have h4 : a < (m_min : ℝ) + 1 := Int.lt_floor_add_one a
      linarith
    have h5 : (m_max : ℝ) - (m_min : ℝ) + 1 ≤ 2 * M_val + 5 := by
      have h6 : (m_max : ℝ) - (m_min : ℝ) + 1 ≤ (b + 1) - (a - 1) + 1 := by linarith
      have h7 : (b + 1) - (a - 1) + 1 = 2 * M_val + 2 * δ + 3 := by
        dsimp only [a, b] <;> ring
      rw [h7] at h6
      linarith [hδ1]
    exact le_trans h1 h5
  -- Integral over inner ≤ sum of strip integrals
  have h3 : ∫ p in inner, f p ≤ ∑ m ∈ S, ∫ p in stripSet m, f p := by
    have h4 : ∫ p in inner, f p ≤ ∫ p in (⋃ m ∈ S, stripSet m), f p := by
      apply setIntegral_mono_set h_int.integrableOn
      · filter_upwards with x
        exact h_nonneg x
      · have hst : inner ≤ᵐ[volume] (⋃ m ∈ S, stripSet m) := by
          filter_upwards with x hx
          exact h_cover hx
        exact hst
    have h5 : ∫ p in (⋃ m ∈ S, stripSet m), f p ≤ ∑ m ∈ S, ∫ p in stripSet m, f p :=
      setIntegral_finite_subadditivity S stripSet h_strip_meas h_int h_nonneg
    exact le_trans h4 h5
  -- Each strip ≤ B_strip
  have h6 : ∑ m ∈ S, ∫ p in stripSet m, f p ≤ (S.card : ℝ) * B_strip := by
    have h7 : ∀ m ∈ S, ∫ p in stripSet m, f p ≤ B_strip := by
      intro m _
      have h8 : ∫ p in stripSet m, f p =
          ∫ p in stripSet m, Real.rpow (multiplicity F δ p) (3 / 2 : ℝ) := by
        congr with p
        <;> rfl
      rw [h8]
      exact h_strip_bound (m : ℝ)
    calc ∑ m ∈ S, ∫ p in stripSet m, f p
      ≤ ∑ m ∈ S, B_strip := Finset.sum_le_sum h7
    _ = (S.card : ℝ) * B_strip := by simp [Finset.sum_const]
  -- Interior bound
  have h_interior : ∫ p in I, f p ≤ (2 * M_val + 5) * B_strip := by
    calc ∫ p in I, f p
      = ∫ p in inner, f p := h_eq_inner
    _ ≤ ∑ m ∈ S, ∫ p in stripSet m, f p := h3
    _ ≤ (S.card : ℝ) * B_strip := h6
    _ ≤ (2 * M_val + 5) * B_strip := by gcongr <;> linarith
  -- Final
  calc ∫ p, f p
    ≤ 3 * ∫ p in I, f p := h_total_interior
  _ ≤ 3 * ((2 * M_val + 5) * B_strip) := by gcongr
  _ = 3 * (2 * M_val + 5) * B_strip := by ring

end Kakeya.Cinematic
