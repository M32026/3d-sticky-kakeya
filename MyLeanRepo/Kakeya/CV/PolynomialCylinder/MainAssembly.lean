import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RotationReduction
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RotationTransfer
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.FiberMultiplicityBound
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.TubeProjectionArea
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.MeasurabilitySetup
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.ImplicitCover
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphAreaMain
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Main assembly of the polynomial cylinder estimate

This file assembles the proof of Guth's polynomial cylinder estimate
(Carbery--Valdimarsson Lemma 1) from its ingredients:

1. **Rotation reduction** — reduce an arbitrary unit direction `e` to `e₃`.
2. **Vanishing on non-z-graph parts** — where `∂p/∂z = 0`, the normal has
   zero `e₃`-component, so the integrand vanishes.
3. **Implicit function cover** — the part where `∂p/∂z ≠ 0` is covered by
   countably many `C¹` z-graph patches.
4. **Graph area formula** — on each z-graph patch, the weighted surface
   integral equals the Lebesgue measure of the projected base.
5. **Fiber multiplicity bound** — almost every fiber intersects the zero set
   in at most `k` points, controlling the overlap multiplicity of patches.
6. **Tube projection area** — the projection of the unit tube onto the
   perpendicular plane has area at most `π`.

Summing gives `directionalSurfaceArea e₃ p S ≤ π * k`.

## Whiteprint node: directional-estimate-assembly
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Real

namespace Kakeya.CV

/-! ### Measure theory helper lemmas (to be formalized) -/

/-- If `f x = 0` for all `x ∈ s`, then the set lintegral is zero. -/
lemma set_lintegral_eq_zero_of_forall {μ : Measure (Point 3)} {s : Set (Point 3)}
    {f : Point 3 → ENNReal} (h : ∀ x ∈ s, f x = 0) :
    (∫⁻ x in s, f x ∂μ) = 0 := by
  have h_le : ∀ x ∈ s, f x ≤ (0 : ENNReal) := by
    intro x hx
    rw [h x hx] <;> simp
  have h_mono : (∫⁻ x in s, f x ∂μ) ≤ (∫⁻ x in s, (0 : ENNReal) ∂μ) :=
    MeasureTheory.setLIntegral_mono (measurable_const) h_le
  have h_zero : (∫⁻ x in s, (0 : ENNReal) ∂μ) = 0 := by simp
  rw [h_zero] at h_mono
  exact le_antisymm h_mono (by positivity)

/-- Set lintegral is monotone in the set argument. -/
lemma set_lintegral_mono_set {μ : Measure (Point 3)} {s₁ s₂ : Set (Point 3)}
    {f : Point 3 → ENNReal} (h : s₁ ⊆ s₂) :
    (∫⁻ x in s₁, f x ∂μ) ≤ (∫⁻ x in s₂, f x ∂μ) :=
  MeasureTheory.lintegral_mono_set h

/-- Set lintegral is subadditive over union. -/
lemma set_lintegral_union_le {μ : Measure (Point 3)} {s₁ s₂ : Set (Point 3)}
    {f : Point 3 → ENNReal} :
    (∫⁻ x in (s₁ ∪ s₂), f x ∂μ) ≤
      (∫⁻ x in s₁, f x ∂μ) + (∫⁻ x in s₂, f x ∂μ) :=
  MeasureTheory.lintegral_union_le f s₁ s₂

/-- Set lintegral is countably subadditive. -/
lemma set_lintegral_iUnion_le {μ : Measure (Point 3)} {s : ℕ → Set (Point 3)}
    {f : Point 3 → ENNReal} :
    (∫⁻ x in (⋃ i, s i), f x ∂μ) ≤ ∑' i, (∫⁻ x in s i, f x ∂μ) :=
  MeasureTheory.lintegral_iUnion_le s f


/-! ### Graph patch definition -/

/-- **Graph area bound for z-graphs.** Given a z-graph lying in a polynomial
zero set with nonvanishing z-gradient, the directional surface area is bounded
by `12 * planeConstant` times the Lebesgue measure of the projection.

This is a thin wrapper around `graph_area_inequality_z`. -/
lemma graph_area_bound_z (U : Set (Point 2)) (f : Point 2 → ℝ)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (p : MvPolynomial (Fin 3) ℝ)
    (h_zero : zGraph U f ⊆ polynomialZeroSet p)
    (h_reg : ∀ x ∈ zGraph U f, (polynomialGradient p x) 2 ≠ 0)
    {A : Set (Point 3)} (hA : A ⊆ zGraph U f)
    (hB_meas : MeasurableSet (proj2 '' A)) :
    directionalSurfaceArea e3 p A ≤ 12 * planeConstant * volume (proj2 '' A) :=
  graph_area_inequality_z hU hf h_zero h_reg hA hB_meas

/-! **Implicit function cover.** The part of the zero set where `∂p/∂z ≠ 0`
can be covered by countably many `C¹` z-graph patches, each lying on the
zero set with nonvanishing `z`-gradient.

*Proof:* at each point apply the implicit function theorem to get a
local z-graph; use second countability of `ℝ³` to extract a countable
subcover. Formalized in `ImplicitCover.lean`. -/

/-- **Multiplicity-controlled sum.** If `U_i ⊆ B` are measurable and almost every
`y ∈ B` is contained in at most `k` of the `U_i`, then
`∑ i, volume U_i ≤ k * volume B`.

*Proof:* Beppo-Levi / monotone convergence: interchange sum and lintegral,
then bound the pointwise multiplicity by `k`. -/
lemma sum_volumes_with_multiplicity (B : Set (Point 2)) (U : ℕ → Set (Point 2))
    (k : ℕ) (h_sub : ∀ i, U i ⊆ B) (hmeas : ∀ i, MeasurableSet (U i))
    (hBmeas : MeasurableSet B)
    (h_mult : ∀ᵐ y ∂volume,
      ∑' i : ℕ, Set.indicator (U i) (fun (_ : Point 2) => (1 : ENNReal)) y ≤ (k : ENNReal)) :
    ∑' i : ℕ, volume (U i) ≤ (k : ℝ≥0∞) * volume B := by
  let g : ℕ → Point 2 → ENNReal := fun i => Set.indicator (U i) (fun (_ : Point 2) => (1 : ENNReal))
  let f_sum : Point 2 → ENNReal := fun y => ∑' i : ℕ, g i y
  have hg_meas : ∀ i, Measurable (g i) := by
    intro i
    exact (measurable_const : Measurable (fun (_ : Point 2) => (1 : ENNReal))).indicator (hmeas i)
  have h1 : ∀ i, volume (U i) = ∫⁻ y, g i y ∂volume := by
    intro i
    have h_indicator : ∫⁻ y, g i y ∂volume = ∫⁻ y in U i, (1 : ENNReal) ∂volume := by
      rw [lintegral_indicator (hmeas i)] <;> rfl
    rw [h_indicator]
    rw [MeasureTheory.setLIntegral_const (U i) (1 : ENNReal)]
    <;> simp
  have h2 : ∑' i : ℕ, volume (U i) = ∫⁻ y, f_sum y ∂volume := by
    have h_sum : ∑' i : ℕ, volume (U i) = ∑' i : ℕ, ∫⁻ y, g i y ∂volume := by
      congr with i
      exact h1 i
    rw [h_sum]
    have hg_ae : ∀ i, AEMeasurable (g i) volume := fun i => (hg_meas i).aemeasurable
    exact (MeasureTheory.lintegral_tsum hg_ae).symm
  have f_sum_zero : ∀ y ∉ B, f_sum y = 0 := by
    intro y hy
    have h6 : ∀ i, y ∉ U i := by
      intro i
      intro hxi
      exact hy (h_sub i hxi)
    have h8 : ∀ i, g i y = 0 := by
      intro i
      simp [g, h6 i]
    have h7 : f_sum y = 0 := by
      dsimp only [f_sum]
      rw [tsum_congr h8] <;> simp
    exact h7
  have f_sum_eq : f_sum = Set.indicator B f_sum := by
    funext y
    by_cases hy : y ∈ B
    · simp [hy, f_sum]
    · have h9 : f_sum y = 0 := f_sum_zero y hy
      rw [h9] <;> simp [hy]
  have h_bound_ae : ∀ᵐ y ∂volume, f_sum y ≤ Set.indicator B (fun (_ : Point 2) => (k : ENNReal)) y := by
    filter_upwards [h_mult] with y hy
    by_cases hyB : y ∈ B
    · have h9 : Set.indicator B (fun (_ : Point 2) => (k : ENNReal)) y = (k : ENNReal) := by
        simp [hyB, Set.indicator]
      rw [h9]
      exact hy
    · have h9 : f_sum y = 0 := f_sum_zero y hyB
      rw [h9]
      <;> simp [hyB, Set.indicator]
  have h_main1 : ∫⁻ y, f_sum y ∂volume ≤ ∫⁻ y, Set.indicator B (fun (_ : Point 2) => (k : ENNReal)) y ∂volume :=
    lintegral_mono_ae h_bound_ae
  have h_main2 : ∫⁻ y, Set.indicator B (fun (_ : Point 2) => (k : ENNReal)) y ∂volume = (k : ENNReal) * volume B :=
    MeasureTheory.lintegral_indicator_const hBmeas (k : ENNReal)
  have h_le : ∫⁻ y, f_sum y ∂volume ≤ (k : ENNReal) * volume B :=
    le_trans h_main1 (le_of_eq h_main2)
  have h_final : ∑' i : ℕ, volume (U i) ≤ (k : ENNReal) * volume B := by
    rw [h2]
    exact h_le
  exact h_final

/-! ### Disjointification and fiber multiplicity helpers -/

/-- The inverse of `proj2` on a z-graph: maps `y : Point 2` to `(y₀, y₁, f y)`. -/
def zGraphEmbed (f : Point 2 → ℝ) (y : Point 2) : Point 3 :=
  (y 0) • eBasis 0 + (y 1) • eBasis 1 + (f y) • eBasis 2

lemma zGraphEmbed_proj2 (f : Point 2 → ℝ) (y : Point 2) :
    proj2 (zGraphEmbed f y) = y := by
  ext i
  fin_cases i <;> simp [zGraphEmbed, proj2, eBasis] <;> decide

lemma zGraphEmbed_coord2 (f : Point 2 → ℝ) (y : Point 2) :
    (zGraphEmbed f y) 2 = f y := by
  simp [zGraphEmbed, eBasis] <;> decide

lemma mem_zGraph_iff (U : Set (Point 2)) (f : Point 2 → ℝ) (x : Point 3) :
    x ∈ zGraph U f ↔ proj2 x ∈ U ∧ x 2 = f (proj2 x) := by
  simp [zGraph]

lemma zGraphEmbed_eq (U : Set (Point 2)) (f : Point 2 → ℝ) {x : Point 3} (hx : x ∈ zGraph U f) :
    zGraphEmbed f (proj2 x) = x := by
  have h1 : x 2 = f (proj2 x) := (mem_zGraph_iff U f x).mp hx |>.2
  have h_coord0 : ∀ (y : Point 2), (zGraphEmbed f y) 0 = y 0 := by
    intro y; simp [zGraphEmbed, eBasis, PiLp.single_apply]
  have h_coord1 : ∀ (y : Point 2), (zGraphEmbed f y) 1 = y 1 := by
    intro y; simp [zGraphEmbed, eBasis, PiLp.single_apply]
  have h_proj0 : ∀ (z : Point 3), (proj2 z) 0 = z 0 := by
    intro z; simp [proj2, EuclideanSpace.equiv]
  have h_proj1 : ∀ (z : Point 3), (proj2 z) 1 = z 1 := by
    intro z; simp [proj2, EuclideanSpace.equiv]
  have h_eq0 : (zGraphEmbed f (proj2 x)) 0 = x 0 := by
    calc (zGraphEmbed f (proj2 x)) 0 = (proj2 x) 0 := h_coord0 (proj2 x)
      _ = x 0 := h_proj0 x
  have h_eq1 : (zGraphEmbed f (proj2 x)) 1 = x 1 := by
    calc (zGraphEmbed f (proj2 x)) 1 = (proj2 x) 1 := h_coord1 (proj2 x)
      _ = x 1 := h_proj1 x
  have h_eq2 : (zGraphEmbed f (proj2 x)) 2 = x 2 := by
    rw [zGraphEmbed_coord2 f (proj2 x), h1]
  ext i
  fin_cases i <;> tauto

/-- The projection of a measurable subset of a z-graph is measurable. -/
lemma proj2_image_measurable {U : Set (Point 2)} {f : Point 2 → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) {A : Set (Point 3)}
    (hA : MeasurableSet A) (h_sub : A ⊆ zGraph U f) :
    MeasurableSet (proj2 '' A) := by
  let φ := zGraphEmbed f
  have h_f_cont : ContinuousOn f U := hf.continuousOn
  have h_cont : ContinuousOn φ U := by
    have h1 : Continuous (fun y : Point 2 => (y 0) • eBasis 0) := by fun_prop
    have h2 : Continuous (fun y : Point 2 => (y 1) • eBasis 1) := by fun_prop
    have h3 : ContinuousOn (fun y : Point 2 => (f y) • eBasis 2) U :=
      h_f_cont.smul continuous_const.continuousOn
    exact (h1.continuousOn.add h2.continuousOn).add h3
  have h_eq : proj2 '' A = φ ⁻¹' A := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_xe : φ (proj2 x) = x := zGraphEmbed_eq U f (h_sub hx)
      rw [h_xe]; exact hx
    · intro hy
      refine' ⟨φ y, hy, _⟩
      exact zGraphEmbed_proj2 f y
  rw [h_eq]
  have h_sub2 : φ ⁻¹' A ⊆ U := by
    intro y hy
    have h2 : φ y ∈ zGraph U f := h_sub hy
    have h3 : proj2 (φ y) ∈ U := (mem_zGraph_iff U f (φ y)).mp h2 |>.1
    rw [zGraphEmbed_proj2 f y] at h3
    exact h3
  let i : U → Point 2 := Subtype.val
  have hU_meas : MeasurableSet U := hU.measurableSet
  have h_me : MeasurableEmbedding i := MeasurableEmbedding.subtype_coe hU_meas
  let φ_U : U → Point 3 := fun y => φ y
  have h_cont_U : Continuous φ_U := continuousOn_iff_continuous_restrict.mp h_cont
  have h_meas_U : Measurable φ_U := h_cont_U.measurable
  have h_preimage : MeasurableSet (φ_U ⁻¹' A) := h_meas_U hA
  have h_final : MeasurableSet (i '' (φ_U ⁻¹' A)) := h_me.measurableSet_image.mpr h_preimage
  have h_image_eq : i '' (φ_U ⁻¹' A) = φ ⁻¹' A := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact hy'
    · intro hy
      exact ⟨⟨y, h_sub2 hy⟩, hy, rfl⟩
  rw [←h_image_eq]
  exact h_final

/-- Disjointification of a countable family of sets. -/
def disjointify (s : ℕ → Set (Point 3)) : ℕ → Set (Point 3) :=
  fun i => Set.diff (s i) (⋃ j ∈ Finset.range i, s j)

lemma disjointify_sub (s : ℕ → Set (Point 3)) : ∀ i, disjointify s i ⊆ s i := by
  intro i
  intro x hx
  exact hx.1

lemma disjointify_disjoint (s : ℕ → Set (Point 3)) :
    ∀ i j, i ≠ j → Disjoint (disjointify s i) (disjointify s j) := by
  intro i j hne
  wlog h : i < j generalizing i j
  · exact (this j i hne.symm (hne.lt_or_gt.resolve_left h)).symm
  · have h1 : disjointify s i ⊆ s i := disjointify_sub s i
    have h2 : disjointify s j ⊆ Set.diff (s j) (s i) := by
      intro x hx
      have h3 : x ∈ s j := hx.1
      have h4 : x ∉ ⋃ k ∈ Finset.range j, s k := hx.2
      have h5 : i ∈ Finset.range j := Finset.mem_range.mpr h
      have h6 : x ∉ s i := by
        intro h7
        have h8 : x ∈ ⋃ k ∈ Finset.range j, s k := Set.mem_biUnion h5 h7
        exact h4 h8
      exact ⟨h3, h6⟩
    have h_disj : Disjoint (s i) (Set.diff (s j) (s i)) := by
      rw [Set.disjoint_left]
      intro x hxi hxdiff
      exact hxdiff.2 hxi
    exact Disjoint.mono h1 h2 h_disj

lemma disjointify_union (s : ℕ → Set (Point 3)) :
    (⋃ i, disjointify s i) = (⋃ i, s i) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    have h1 : disjointify s i ⊆ s i := disjointify_sub s i
    exact Set.mem_iUnion.mpr ⟨i, h1 hi⟩
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    have h_main : ∀ (n : ℕ), x ∈ s n → x ∈ ⋃ k, disjointify s k := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro hxn
        by_cases h : x ∈ ⋃ j ∈ Finset.range n, s j
        · have h_exists : ∃ j, j ∈ Finset.range n ∧ x ∈ s j := by
            simpa using h
          rcases h_exists with ⟨j, hj_range, hj_mem⟩
          have h_j_lt : j < n := Finset.mem_range.mp hj_range
          exact ih j h_j_lt hj_mem
        · have h' : x ∈ disjointify s n := ⟨hxn, h⟩
          exact Set.mem_iUnion.mpr ⟨n, h'⟩
    exact h_main i hi

/-- A z-graph of a function continuous on an open set is measurable. -/
lemma zGraph_measurable {U : Set (Point 2)} {f : Point 2 → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    MeasurableSet (zGraph U f) := by
  let V : Set (Point 3) := {x | proj2 x ∈ U}
  have h_equiv3 : Continuous (EuclideanSpace.equiv (Fin 3) ℝ) :=
    (EuclideanSpace.equiv (Fin 3) ℝ).continuous
  let f_middle : (Fin 3 → ℝ) → (Fin 2 → ℝ) := fun v => (fun i : Fin 2 => v (Fin.castSucc i))
  have h_middle : Continuous f_middle := by
    exact Pi.continuous_precomp Fin.castSucc
  have h_equiv2_symm : Continuous ((EuclideanSpace.equiv (Fin 2) ℝ).symm) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous
  have h_proj2_cont : Continuous proj2 := by
    have h4 : proj2 = ((EuclideanSpace.equiv (Fin 2) ℝ).symm) ∘ f_middle ∘ (EuclideanSpace.equiv (Fin 3) ℝ) := by
      funext x
      simp [proj2, f_middle]
      <;> rfl
    rw [h4]
    exact h_equiv2_symm.comp (h_middle.comp h_equiv3)
  have hV_open : IsOpen V := hU.preimage h_proj2_cont
  have hV_meas : MeasurableSet V := hV_open.measurableSet
  let i : V → Point 3 := Subtype.val
  have h_me : MeasurableEmbedding i := MeasurableEmbedding.subtype_coe hV_meas
  let h : V → ℝ × ℝ := fun x => ((x : Point 3) 2, f (proj2 (x : Point 3)))
  have h_f_cont : ContinuousOn f U := hf.continuousOn
  have h_cont : Continuous h := by
    have h1 : ContinuousOn (fun x : Point 3 => f (proj2 x)) V :=
      h_f_cont.comp h_proj2_cont.continuousOn (by intro x hx; simpa [V] using hx)
    have h2 : Continuous (fun x : V => f (proj2 (x : Point 3))) :=
      continuousOn_iff_continuous_restrict.mp h1
    have h3 : Continuous (fun x : V => (x : Point 3) 2) := by fun_prop
    have h4 : Continuous (fun x : V => ((x : Point 3) 2, f (proj2 (x : Point 3)))) := by
      exact Continuous.prodMk h3 h2
    exact h4
  let D : Set (ℝ × ℝ) := {p | p.1 = p.2}
  have hD_meas : MeasurableSet D := isClosed_diagonal.measurableSet
  have h_preimage : MeasurableSet (h ⁻¹' D) := h_cont.measurable hD_meas
  have h_final : MeasurableSet (i '' (h ⁻¹' D)) := h_me.measurableSet_image.mpr h_preimage
  have h_eq : i '' (h ⁻¹' D) = zGraph U f := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_setOf_eq, zGraph, V, D]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx1, hx2⟩
      refine' ⟨⟨x, hx1⟩, hx2, rfl⟩
  rw [←h_eq]
  exact h_final

/-! ### Directional estimate in the e₃ case -/

/-- The polynomial cylinder estimate in the special case `e = e₃`.

The constant is `π` (the area of the unit disk). -/
lemma directional_estimate_e3 (p : MvPolynomial (Fin 3) ℝ) (a : Point 3)
    (k : ℕ) (hp : p ≠ 0) (hk : p.totalDegree ≤ k) :
    directionalSurfaceArea e3 p (polynomialZeroSet p ∩ unitTube a e3) ≤
      12 * planeConstant * ENNReal.ofReal Real.pi * (k : ℝ≥0∞) := by
  classical
  let S := polynomialZeroSet p ∩ unitTube a e3

  -- Partition S into three parts:
  --   S_sing : gradient = 0  →  normal = 0  →  integrand = 0
  --   S_flat : gradient ≠ 0 but ∂p/∂z = 0  →  normal · e₃ = 0  →  integrand = 0
  --   S_zreg : ∂p/∂z ≠ 0  →  covered by z-graphs
  let S_sing := {x ∈ S | polynomialGradient p x = 0}
  let S_flat := {x ∈ S | polynomialGradient p x ≠ 0 ∧ (polynomialGradient p x) 2 = 0}
  let S_zreg := {x ∈ S | (polynomialGradient p x) 2 ≠ 0}

  have h_partition : S ⊆ S_sing ∪ S_flat ∪ S_zreg := by
    intro x hx
    simp only [Set.mem_union]
    by_cases h1 : polynomialGradient p x = 0
    · exact Or.inl (Or.inl ⟨hx, h1⟩)
    · by_cases h2 : (polynomialGradient p x) 2 = 0
      · exact Or.inl (Or.inr ⟨hx, h1, h2⟩)
      · exact Or.inr ⟨hx, h2⟩

  let μ : Measure (Point 3) := Measure.hausdorffMeasure 2
  let f : Point 3 → ENNReal := fun x => ENNReal.ofReal ‖inner ℝ e3 (polynomialUnitNormal p x)‖

  -- Step 1: Singular set contributes zero.
  have h_sing : directionalSurfaceArea e3 p S_sing = 0 := by
    have h1 : ∀ x ∈ S_sing, polynomialUnitNormal p x = 0 := by
      intro x hx
      have h2 : polynomialGradient p x = 0 := hx.2
      simp [polynomialUnitNormal, h2]
    have h_integrand : ∀ x ∈ S_sing, f x = 0 := by
      intro x hx
      have h_expand : f x = ENNReal.ofReal ‖inner ℝ e3 (polynomialUnitNormal p x)‖ := by rfl
      rw [h_expand, h1 x hx] <;> simp
    have h_main : (∫⁻ x in S_sing, f x ∂μ) = 0 :=
      set_lintegral_eq_zero_of_forall h_integrand
    exact h_main

  -- Step 2: Flat set (∂p/∂z = 0 but ∇p ≠ 0) contributes zero.
  have h_flat : directionalSurfaceArea e3 p S_flat = 0 := by
    have h_inner_e3 : ∀ (v : Point 3), inner ℝ e3 v = v 2 := by
      intro v
      simp [e3, EuclideanSpace.inner_single_left] <;> ring
    have h1 : ∀ x ∈ S_flat, (polynomialUnitNormal p x) 2 = 0 := by
      intro x hx
      have hgrad_ne : polynomialGradient p x ≠ 0 := hx.2.1
      have hgrad2 : (polynomialGradient p x) 2 = 0 := hx.2.2
      have hnorm : polynomialUnitNormal p x =
          ‖polynomialGradient p x‖⁻¹ • polynomialGradient p x := by
        simp [polynomialUnitNormal, hgrad_ne] <;> rfl
      rw [hnorm]
      simp [hgrad2] <;> ring
    have h_integrand : ∀ x ∈ S_flat, f x = 0 := by
      intro x hx
      have h4 : inner ℝ e3 (polynomialUnitNormal p x) = (polynomialUnitNormal p x) 2 := h_inner_e3 _
      have h5 : f x = ENNReal.ofReal ‖inner ℝ e3 (polynomialUnitNormal p x)‖ := by rfl
      rw [h5, h4, h1 x hx] <;> simp
    have h_main : (∫⁻ x in S_flat, f x ∂μ) = 0 :=
      set_lintegral_eq_zero_of_forall h_integrand
    exact h_main

  -- Step 3: Cover S_zreg by countably many z-graph patches.
  rcases regular_zero_set_zGraph_cover p with ⟨patches, hpatch_prop, hcover⟩
  let patchSets : ℕ → Set (Point 3) := fun i => patches i ∩ S

  -- Each patch intersected with S is a subset of the graph.
  have h_sub : ∀ i, patchSets i ⊆ patches i := by
    intro i
    intro x hx
    exact hx.1

  -- Step 4: Disjointify the patches.
  let A : ℕ → Set (Point 3) := disjointify patchSets
  have hA_sub : ∀ i, A i ⊆ patchSets i := disjointify_sub patchSets
  have hA_disj : ∀ i j, i ≠ j → Disjoint (A i) (A j) := disjointify_disjoint patchSets
  have hA_union : (⋃ i, A i) = (⋃ i, patchSets i) := disjointify_union patchSets

  have h_cover2 : S_zreg ⊆ ⋃ i : ℕ, patchSets i := by
    intro x hx
    have h_in_zero : x ∈ polynomialZeroSet p := hx.1.1
    have h_grad2 : (polynomialGradient p x) 2 ≠ 0 := hx.2
    have h5 : x ∈ {x ∈ polynomialZeroSet p | (polynomialGradient p x) 2 ≠ 0} := ⟨h_in_zero, h_grad2⟩
    have h6 : x ∈ ⋃ i : ℕ, patches i := hcover h5
    rcases Set.mem_iUnion.mp h6 with ⟨i, hi⟩
    have h7 : x ∈ patchSets i := ⟨hi, hx.1⟩
    exact Set.mem_iUnion.mpr ⟨i, h7⟩
  have h_coverA : S_zreg ⊆ ⋃ i, A i := by
    rw [hA_union] at *
    exact h_cover2

  -- Step 5: Measurability of patches and projections.
  have h_patch_meas : ∀ i, MeasurableSet (patchSets i) := by
    intro i
    rcases hpatch_prop i with ⟨U, f, hU, hf, h_eq, h_zero, h_reg⟩
    have h1 : MeasurableSet (patches i) := by
      rw [h_eq]
      exact zGraph_measurable hU hf
    have h2 : MeasurableSet S :=
      (measurableSet_polynomialZeroSet p).inter (measurableSet_unitTube a e3)
    exact h1.inter h2

  have hA_meas : ∀ i, MeasurableSet (A i) := by
    intro i
    have h1 : A i = Set.diff (patchSets i) (⋃ j ∈ Finset.range i, patchSets j) := by rfl
    rw [h1]
    have h_union_meas : MeasurableSet (⋃ j ∈ Finset.range i, patchSets j) := by
      exact Finset.measurableSet_biUnion (Finset.range i) fun b a => h_patch_meas b
    exact (h_patch_meas i).diff h_union_meas

  have h_proj_meas : ∀ i, MeasurableSet (proj2 '' A i) := by
    intro i
    rcases hpatch_prop i with ⟨U, f, hU, hf, h_eq, h_zero, h_reg⟩
    have hA_graph : A i ⊆ zGraph U f := by
      have h1 : A i ⊆ patchSets i := hA_sub i
      have h2 : patchSets i ⊆ patches i := by intro x hx; exact hx.1
      rw [h_eq] at h2
      exact h1.trans h2
    exact proj2_image_measurable hU hf (hA_meas i) hA_graph

  -- Apply graph area bound to each disjoint patch.
  have h_area : ∀ i, directionalSurfaceArea e3 p (A i) ≤
      12 * planeConstant * volume (proj2 '' A i) := by
    intro i
    rcases hpatch_prop i with ⟨U, f, hU, hf, h_eq, h_zero, h_reg⟩
    have hA_graph : A i ⊆ zGraph U f := by
      have h1 : A i ⊆ patchSets i := hA_sub i
      have h2 : patchSets i ⊆ patches i := by intro x hx; exact hx.1
      rw [h_eq] at h2
      exact h1.trans h2
    have h_zero' : zGraph U f ⊆ polynomialZeroSet p := by rw [←h_eq]; exact h_zero
    have h_reg' : ∀ x ∈ zGraph U f, (polynomialGradient p x) 2 ≠ 0 := by rw [←h_eq]; exact h_reg
    exact graph_area_bound_z U f hU hf p h_zero' h_reg' hA_graph (h_proj_meas i)

  -- Step 6: Projected disjoint patches lie in the tube projection.
  let B := proj2 '' unitTube a e3
  have hB : ∀ i, proj2 '' A i ⊆ B := by
    intro i
    have h1 : A i ⊆ S := by
      have h2 : A i ⊆ patchSets i := hA_sub i
      intro x hx
      exact (h2 hx).2
    have h3 : S ⊆ unitTube a e3 := by intro x hx; exact hx.2
    have h4 : A i ⊆ unitTube a e3 := h1.trans h3
    exact Set.image_mono h4

  -- Step 7: Multiplicity bound via fiber multiplicity.
  let e2 : Point 2 → (Fin 2 → ℝ) := WithLp.ofLp
  have h_mp2 : MeasurePreserving e2 volume volume :=
    PiLp.volume_preserving_ofLp (ι := Fin 2)
  let P : (Fin 2 → ℝ) → Prop := fun z =>
    let eqv := (EuclideanSpace.equiv (Fin 3) ℝ).symm
    let a : Point 3 := eqv (Fin.cases (z 0) (Fin.cases (z 1) (Fin.cases 0 Fin.elim0)))
    let e : Point 3 := eqv (Fin.cases 0 (Fin.cases 0 (Fin.cases 1 Fin.elim0)))
    let q := restrictToLine p a e
    q ≠ 0 ∧ Set.ncard (q.rootSet ℝ) ≤ k
  have h_fiber_orig : ∀ᵐ (z : Fin 2 → ℝ) ∂volume, P z := fiberMultiplicityBound_e3 p hp k hk
  have h_fiber : ∀ᵐ (y : Point 2) ∂volume, P (e2 y) := by
    let e2_homeo : Homeomorph (Point 2) (Fin 2 → ℝ) :=
      { toFun := e2
        invFun := @WithLp.toLp 2 (Fin 2 → ℝ)
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have h_emb : MeasurableEmbedding e2 := e2_homeo.measurableEmbedding
    rcases h_mp2 with ⟨_, h_map⟩
    have h1 : ∀ᵐ (z : Fin 2 → ℝ) ∂(Measure.map e2 volume), P z := by
      rw [h_map]
      exact h_fiber_orig
    exact (h_emb.ae_map_iff (p := P) (μ := volume)).mp h1

  have h_mult : ∀ᵐ (y : Point 2) ∂volume,
      ∑' i : ℕ, Set.indicator (proj2 '' A i) (fun (_ : Point 2) => (1 : ENNReal)) y ≤ (k : ENNReal) := by
    filter_upwards [h_fiber] with y hy
    let I : Set ℕ := {i | y ∈ proj2 '' A i}
    let z : Fin 2 → ℝ := e2 y
    let eqv := (EuclideanSpace.equiv (Fin 3) ℝ).symm
    let a_fib : Point 3 := eqv (Fin.cases (z 0) (Fin.cases (z 1) (Fin.cases 0 Fin.elim0)))
    let e_fib : Point 3 := eqv (Fin.cases 0 (Fin.cases 0 (Fin.cases 1 Fin.elim0)))
    let q := restrictToLine p a_fib e_fib
    have hq_ne : q ≠ 0 := hy.1
    have hq_card : Set.ncard (q.rootSet ℝ) ≤ k := hy.2
    have hz0 : z 0 = y 0 := by simp [z, e2] <;> rfl
    have hz1 : z 1 = y 1 := by simp [z, e2] <;> rfl
    have h_choice : ∀ (i : ℕ), i ∈ I → ∃ (x : Point 3), x ∈ A i ∧ proj2 x = y := by
      intro i hi
      simpa [I, Set.mem_setOf_eq] using hi
    let x : ℕ → Point 3 := fun i =>
      if h : i ∈ I then Classical.choose (h_choice i h) else 0
    have hx1 : ∀ i ∈ I, x i ∈ A i := by
      intro i hi
      have h_let : x i = Classical.choose (h_choice i hi) := by
        simp [x, hi]
      rw [h_let]
      exact (Classical.choose_spec (h_choice i hi)).1
    have hx2 : ∀ i ∈ I, proj2 (x i) = y := by
      intro i hi
      have h_let : x i = Classical.choose (h_choice i hi) := by
        simp [x, hi]
      rw [h_let]
      exact (Classical.choose_spec (h_choice i hi)).2
    have h_proj2_coord : ∀ (w : Point 3) (j : Fin 2), (e2 (proj2 w)) j = w (Fin.castSucc j) := by
      intro w j
      fin_cases j <;> rfl
    have h_coord : ∀ i ∈ I, (x i) 0 = y 0 ∧ (x i) 1 = y 1 := by
      intro i hi
      have h : e2 (proj2 (x i)) = e2 y := by rw [hx2 i hi]
      have h0 : (e2 (proj2 (x i))) 0 = (e2 y) 0 := by rw [h]
      have h1 : (e2 (proj2 (x i))) 1 = (e2 y) 1 := by rw [h]
      have h2 : (e2 (proj2 (x i))) 0 = (x i) 0 := h_proj2_coord (x i) 0
      have h3 : (e2 (proj2 (x i))) 1 = (x i) 1 := h_proj2_coord (x i) 1
      have h4 : (e2 y) 0 = y 0 := rfl
      have h5 : (e2 y) 1 = y 1 := rfl
      exact ⟨h2.symm.trans (h0.trans h4), h3.symm.trans (h1.trans h5)⟩
    have h_inj : Set.InjOn (fun i : ℕ => (x i) 2) I := by
      intro i hi j hj h_eq
      by_cases h : i = j
      · exact h
      · have h_disj : Disjoint (A i) (A j) := hA_disj i j h
        have h_xeq : x i = x j := by
          ext k
          fin_cases k
          · exact (h_coord i hi).1.trans (h_coord j hj).1.symm
          · exact (h_coord i hi).2.trans (h_coord j hj).2.symm
          · exact h_eq
        have h_false : False := by
          have h1 : x i ∈ A i := hx1 i hi
          have h2 : x i ∈ A j := by rw [h_xeq]; exact hx1 j hj
          exact Set.disjoint_left.mp h_disj h1 h2
        exact False.elim h_false
    have h_root_finite : Set.Finite (q.rootSet ℝ) := by
      have h1 : Set.Finite {x : ℝ | q.eval x = 0} := Polynomial.finite_setOf_isRoot hq_ne
      have h2 : q.rootSet ℝ = {x : ℝ | q.eval x = 0} := by
        ext x
        have h3 : x ∈ q.rootSet ℝ ↔ q.eval x = 0 := by
          simp [Polynomial.mem_rootSet, hq_ne]
        exact h3
      rw [h2]
      exact h1
    have h_root : ∀ i ∈ I, (x i) 2 ∈ q.rootSet ℝ := by
      intro i hi
      have h_xin_zero : x i ∈ polynomialZeroSet p := by
        have h : A i ⊆ S := by
          have h2 : A i ⊆ patchSets i := hA_sub i
          intro z hz
          exact (h2 hz).2
        exact (h (hx1 i hi)).1
      have h_eval : polynomialValue p (x i) = 0 := h_xin_zero
      have h_on_fib : x i = a_fib + (x i) 2 • e_fib := by
        have h_afib0 : a_fib 0 = z 0 := by
          dsimp only [a_fib]
          have h : ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Fin.cases (z 0) (Fin.cases (z 1) (Fin.cases 0 Fin.elim0)))) 0 = z 0 := by
            simp [EuclideanSpace.equiv] <;> rfl
          exact h
        have h_afib1 : a_fib 1 = z 1 := by
          dsimp only [a_fib]
          have h : ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Fin.cases (z 0) (Fin.cases (z 1) (Fin.cases 0 Fin.elim0)))) 1 = z 1 := by
            simp [EuclideanSpace.equiv] <;> rfl
          exact h
        have h_afib2 : a_fib 2 = 0 := by
          dsimp only [a_fib]
          have h : ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Fin.cases (z 0) (Fin.cases (z 1) (Fin.cases 0 Fin.elim0)))) 2 = 0 := by
            simp [EuclideanSpace.equiv] <;> rfl
          exact h
        have h_efib0 : e_fib 0 = 0 := by
          dsimp only [e_fib]
          have h : ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Fin.cases 0 (Fin.cases 0 (Fin.cases 1 Fin.elim0)))) 0 = 0 := by
            simp [EuclideanSpace.equiv] <;> rfl
          exact h
        have h_efib1 : e_fib 1 = 0 := by
          dsimp only [e_fib]
          have h : ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Fin.cases 0 (Fin.cases 0 (Fin.cases 1 Fin.elim0)))) 1 = 0 := by
            simp [EuclideanSpace.equiv] <;> rfl
          exact h
        have h_efib2 : e_fib 2 = 1 := by
          dsimp only [e_fib]
          have h : ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Fin.cases 0 (Fin.cases 0 (Fin.cases 1 Fin.elim0)))) 2 = 1 := by
            simp [EuclideanSpace.equiv] <;> rfl
          exact h
        ext k
        fin_cases k
        · simp [h_afib0, h_efib0, hz0, (h_coord i hi).1, Pi.add_apply, Pi.smul_apply] <;> ring
        · simp [h_afib1, h_efib1, hz1, (h_coord i hi).2, Pi.add_apply, Pi.smul_apply] <;> ring
        · simp [h_afib2, h_efib2, Pi.add_apply, Pi.smul_apply] <;> ring
      have h9 : q.eval ((x i) 2) = polynomialValue p (a_fib + (x i) 2 • e_fib) :=
        restrictToLine_eval p a_fib e_fib ((x i) 2)
      have h10 : q.eval ((x i) 2) = 0 := by
        rw [h9, ←h_on_fib, h_eval]
      simpa [Polynomial.mem_rootSet, hq_ne] using h10
    let g : ℕ → ℝ := fun i => (x i) 2
    have h_g_inj : Set.InjOn g I := h_inj
    have h_g_image : g '' I ⊆ q.rootSet ℝ := by
      intro r hr
      rcases hr with ⟨i, hi, rfl⟩
      exact h_root i hi
    have h_card_image : Set.ncard (g '' I) = Set.ncard I := Set.ncard_image_of_injOn h_g_inj
    have h_card_I : Set.ncard I ≤ Set.ncard (q.rootSet ℝ) := by
      have h1 : Set.ncard (g '' I) ≤ Set.ncard (q.rootSet ℝ) := Set.ncard_le_ncard h_g_image
      rw [h_card_image] at h1
      exact h1
    have h_final : Set.ncard I ≤ k := h_card_I.trans hq_card
    have hI_fin : Set.Finite I := by
      have h1 : Set.Finite (g '' I) := h_root_finite.subset h_g_image
      let F : Finset ℝ := h1.toFinset
      let choose_i : ℝ → ℕ := fun r =>
        if h : ∃ i, i ∈ I ∧ g i = r then Classical.choose h else 0
      let S : Finset ℕ := F.image choose_i
      have hI_sub : I ⊆ (S : Set ℕ) := by
        intro i hi
        have hgi : g i ∈ g '' I := ⟨i, hi, rfl⟩
        have hgr : g i ∈ F := by
          simpa [F, Set.Finite.mem_toFinset] using hgi
        have hex : ∃ j, j ∈ I ∧ g j = g i := ⟨i, hi, rfl⟩
        have h_choice : choose_i (g i) ∈ I ∧ g (choose_i (g i)) = g i := by
          dsimp only [choose_i]
          rw [dif_pos hex]
          exact Classical.choose_spec hex
        have h_eq : g (choose_i (g i)) = g i := h_choice.2
        have h_inj' : choose_i (g i) = i := h_g_inj h_choice.1 hi h_eq
        have h_in_S : choose_i (g i) ∈ S := Finset.mem_image.mpr ⟨g i, hgr, rfl⟩
        rw [h_inj'] at h_in_S
        exact h_in_S
      exact (Finset.finite_toSet S).subset hI_sub
    have h_tsum : ∑' i : ℕ, Set.indicator (proj2 '' A i) (fun (_ : Point 2) => (1 : ENNReal)) y = ↑(Set.ncard I) := by
      have h_eq : ∀ i : ℕ, Set.indicator (proj2 '' A i) (fun (_ : Point 2) => (1 : ENNReal)) y =
          Set.indicator I (fun (_ : ℕ) => (1 : ENNReal)) i := by
        intro i
        simp [I, Set.indicator]
        <;> aesop
      rw [tsum_congr h_eq]
      have h_zero_outside : ∀ i ∉ hI_fin.toFinset, Set.indicator I (fun (_ : ℕ) => (1 : ENNReal)) i = 0 := by
        intro i hi
        have h_i_notin_I : i ∉ I := by simpa [hI_fin.mem_toFinset] using hi
        simp [Set.indicator, h_i_notin_I]
      have h3 : ∑' i : ℕ, Set.indicator I (fun (_ : ℕ) => (1 : ENNReal)) i =
          ∑ i ∈ hI_fin.toFinset, Set.indicator I (fun (_ : ℕ) => (1 : ENNReal)) i :=
        tsum_eq_sum h_zero_outside
      rw [h3]
      have h4 : ∑ i ∈ hI_fin.toFinset, Set.indicator I (fun (_ : ℕ) => (1 : ENNReal)) i =
          ∑ i ∈ hI_fin.toFinset, (1 : ENNReal) := by
        apply Finset.sum_congr rfl
        intro i hi
        have h_i_in_I : i ∈ I := by simpa [hI_fin.mem_toFinset] using hi
        simp [Set.indicator, h_i_in_I]
      rw [h4]
      have h5 : ∑ i ∈ hI_fin.toFinset, (1 : ENNReal) = ↑(Finset.card hI_fin.toFinset) := by
        simp
      rw [h5]
      have h6 : Finset.card hI_fin.toFinset = Set.ncard I := by
        exact Eq.symm (ncard_eq_toFinset_card I hI_fin)
      rw [h6]
      <;> rfl
    rw [h_tsum]
    exact_mod_cast h_final

  -- Step 8: Sum over disjoint patches using multiplicity control.
  let μ : Measure (Point 3) := Measure.hausdorffMeasure 2
  let f_int : Point 3 → ENNReal := fun x => ENNReal.ofReal ‖inner ℝ e3 (polynomialUnitNormal p x)‖
  have h_sum : directionalSurfaceArea e3 p S_zreg ≤
      ∑' i : ℕ, directionalSurfaceArea e3 p (A i) := by
    simp only [directionalSurfaceArea]
    have h_mono : (∫⁻ x in S_zreg, f_int x ∂μ) ≤ (∫⁻ x in (⋃ i : ℕ, A i), f_int x ∂μ) :=
      set_lintegral_mono_set h_coverA
    have h_union : (∫⁻ x in (⋃ i : ℕ, A i), f_int x ∂μ) ≤
        ∑' i : ℕ, (∫⁻ x in (A i), f_int x ∂μ) :=
      set_lintegral_iUnion_le
    exact h_mono.trans h_union

  have h_sum_bound : ∑' i : ℕ, directionalSurfaceArea e3 p (A i) ≤
      12 * planeConstant * ∑' i : ℕ, volume (proj2 '' A i) := by
    have h : ∀ i, directionalSurfaceArea e3 p (A i) ≤ 12 * planeConstant * volume (proj2 '' A i) := h_area
    have h_tsum : ∑' i, directionalSurfaceArea e3 p (A i) ≤
        ∑' i, (12 * planeConstant * volume (proj2 '' A i)) :=
      ENNReal.tsum_le_tsum h
    have h_mul : ∑' i, (12 * planeConstant * volume (proj2 '' A i)) =
        12 * planeConstant * ∑' i, volume (proj2 '' A i) := by
      rw [ENNReal.tsum_mul_left]
    rw [h_mul] at h_tsum
    exact h_tsum
  have hB_eq : B = Metric.closedBall (proj2 a) 1 := by
    apply Set.Subset.antisymm (tube_projection_contained a)
    intro y hy
    let x : Point 3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm
        (Fin.cases (y 0) (Fin.cases (y 1) (Fin.cases (a 2) Fin.elim0)))
    have hx0 : x 0 = y 0 := by simp [x, EuclideanSpace.equiv] <;> rfl
    have hx1 : x 1 = y 1 := by simp [x, EuclideanSpace.equiv] <;> rfl
    have hx2 : x 2 = a 2 := by simp [x, EuclideanSpace.equiv] <;> rfl
    have hpx : proj2 x = y := by
      ext j
      fin_cases j <;> simp [proj2, hx0, hx1] <;> rfl
    have hdist : Metric.infDist x (affineLine a e3) ≤ 1 := by
      have h1 : Metric.infDist x (affineLine a e3) = dist (proj2 x) (proj2 a) := by
        rw [infDist_to_line_e3 a x, proj2_dist x a]
      rw [h1, hpx]
      exact hy
    exact ⟨x, hdist, hpx⟩
  have hBmeas : MeasurableSet B := by
    rw [hB_eq]
    have h_closed : IsClosed (Metric.closedBall (proj2 a) 1) := Metric.isClosed_closedBall
    exact h_closed.measurableSet
  have h_main : ∑' i : ℕ, volume (proj2 '' A i) ≤ (k : ℝ≥0∞) * volume B :=
    sum_volumes_with_multiplicity B (fun i => proj2 '' A i) k (fun i => hB i) h_proj_meas hBmeas h_mult
  have h_zreg_bound : directionalSurfaceArea e3 p S_zreg ≤
      12 * planeConstant * ENNReal.ofReal Real.pi * (k : ℝ≥0∞) := by
    calc
      directionalSurfaceArea e3 p S_zreg
        ≤ ∑' i : ℕ, directionalSurfaceArea e3 p (A i) := h_sum
      _ ≤ 12 * planeConstant * ∑' i : ℕ, volume (proj2 '' A i) := h_sum_bound
      _ ≤ 12 * planeConstant * ((k : ℝ≥0∞) * volume B) :=
          mul_le_mul_left' h_main (12 * planeConstant)
      _ ≤ 12 * planeConstant * ((k : ℝ≥0∞) * ENNReal.ofReal Real.pi) := by
          have h_vol : volume B ≤ ENNReal.ofReal Real.pi := tube_projection_measure_le a
          gcongr
      _ = 12 * planeConstant * ENNReal.ofReal Real.pi * (k : ℝ≥0∞) := by ring

  -- The singular and flat parts contribute zero, so the full set is bounded by S_zreg.
  have h_reduce : directionalSurfaceArea e3 p S ≤ directionalSurfaceArea e3 p S_zreg := by
    simp only [directionalSurfaceArea]
    have h1 : (∫⁻ x in S, f x ∂μ) ≤ (∫⁻ x in ((S_sing ∪ S_flat) ∪ S_zreg), f x ∂μ) :=
      set_lintegral_mono_set h_partition
    have h2 : (∫⁻ x in ((S_sing ∪ S_flat) ∪ S_zreg), f x ∂μ) ≤
        (∫⁻ x in (S_sing ∪ S_flat), f x ∂μ) + (∫⁻ x in S_zreg, f x ∂μ) :=
      set_lintegral_union_le (μ := μ) (s₁ := S_sing ∪ S_flat) (s₂ := S_zreg) (f := f)
    have h3 : (∫⁻ x in (S_sing ∪ S_flat), f x ∂μ) ≤
        (∫⁻ x in S_sing, f x ∂μ) + (∫⁻ x in S_flat, f x ∂μ) :=
      set_lintegral_union_le (μ := μ) (s₁ := S_sing) (s₂ := S_flat) (f := f)
    have h4 : (∫⁻ x in S_sing, f x ∂μ) = 0 := by exact_mod_cast h_sing
    have h5 : (∫⁻ x in S_flat, f x ∂μ) = 0 := by exact_mod_cast h_flat
    calc
      (∫⁻ x in S, f x ∂μ)
        ≤ (∫⁻ x in ((S_sing ∪ S_flat) ∪ S_zreg), f x ∂μ) := h1
      _ ≤ (∫⁻ x in (S_sing ∪ S_flat), f x ∂μ) + (∫⁻ x in S_zreg, f x ∂μ) := h2
      _ ≤ ((∫⁻ x in S_sing, f x ∂μ) + (∫⁻ x in S_flat, f x ∂μ)) + (∫⁻ x in S_zreg, f x ∂μ) := by
          gcongr
      _ = (∫⁻ x in S_zreg, f x ∂μ) := by rw [h4, h5] <;> ring
  exact h_reduce.trans h_zreg_bound

/-! ### Rotation reduction and main theorem -/

/-- The full polynomial cylinder estimate, obtained by rotating the given
direction `e` to `e₃`, applying `directional_estimate_e3`, and transferring
the result back via the linear isometry. -/
lemma polynomial_cylinder_estimate_main : PolynomialCylinderEstimateStatement := by
  have hpc_ne_top : planeConstant ≠ ⊤ := planeConstant_ne_top
  have hpc_pos : 0 < planeConstant := planeConstant_pos
  let bound : ENNReal := 12 * planeConstant * ENNReal.ofReal Real.pi
  have hbound_ne_top : bound ≠ ⊤ := by
    simp only [bound]
    have h1 : planeConstant ≠ ⊤ := hpc_ne_top
    have h2 : ENNReal.ofReal Real.pi ≠ ⊤ := by simp
    have h3 : (12 : ENNReal) ≠ ⊤ := by simp
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top h3 h1) h2
  let C : ℝ≥0 := bound.toNNReal
  have hC : (C : ℝ≥0∞) = bound :=
    ENNReal.coe_toNNReal hbound_ne_top
  have hC_pos : 0 < C := by
    have h3 : 0 < bound := by positivity
    have h4 : (C : ℝ≥0∞) = bound := hC
    have h5 : (C : ℝ≥0∞) ≠ 0 := by
      rw [h4]
      exact ne_of_gt h3
    have h6 : C ≠ 0 := by
      intro h7
      rw [h7] at h5
      simp at h5
    exact h6.bot_lt
  use C
  constructor
  · exact hC_pos
  · intro k p a e hp _hSingular hk he
    -- Step 1: Find a rotation R sending e to e₃.
    rcases exists_rotation_to_e3 e he with ⟨R, hR⟩

    -- Step 2: Define the rotated polynomial p' satisfying
    -- polynomialValue p' (R x) = polynomialValue p x.
    let p' : MvPolynomial (Fin 3) ℝ := rotatedPoly p R

    -- Step 3: Properties of p'.
    have hp'_ne : p' ≠ 0 := rotatedPoly_ne_zero p R hp
    have hp'_deg : p'.totalDegree ≤ k :=
      (rotatedPoly_totalDegree_le p R).trans hk

    -- Step 4: Geometric transfer under R.
    let S := polynomialZeroSet p ∩ unitTube a e
    let S' := polynomialZeroSet p' ∩ unitTube (R a) e3
    have hS1 : R '' polynomialZeroSet p = polynomialZeroSet p' :=
      rotated_zeroSet p R
    have hS2 : R '' unitTube a e = unitTube (R a) e3 :=
      rotated_unitTube R a e hR
    have hS' : R '' S = S' := by
      have h : R '' S = (R '' polynomialZeroSet p) ∩ (R '' unitTube a e) := by
        ext y
        simp only [Set.mem_image, Set.mem_inter_iff]
        constructor
        · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
          exact ⟨⟨x, hx1, rfl⟩, ⟨x, hx2, rfl⟩⟩
        · rintro ⟨⟨x1, hx1, rfl⟩, ⟨x2, hx2, h_eq⟩⟩
          have h_xeq : x2 = x1 := R.injective h_eq
          rw [h_xeq] at hx2
          exact ⟨x1, ⟨hx1, hx2⟩, rfl⟩
      rw [h, hS1, hS2]
      <;> rfl
    have h_transfer : directionalSurfaceArea e p S =
        directionalSurfaceArea e3 p' S' := by
      have h_tmp := directionalSurfaceArea_transfer p R e hR S
      rwa [hS'] at h_tmp

    -- Step 5: Apply the e₃ estimate.
    have h_e3 := directional_estimate_e3 p' (R a) k hp'_ne hp'_deg

    -- Step 6: Conclude.
    rw [h_transfer, hC]
    exact h_e3

end Kakeya.CV
