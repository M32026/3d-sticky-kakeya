/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionN.Volume
public import Kakeya.Mathlib.Topology.CoveringNumber
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Ball density at a scale

GWZ compress the geometric input of Lemma 5.8 into the single clause
`|A(W)| ≲ |Y_𝒲(W)|` "because `|W ∩ B| ≳ |B|` for every ball `B` of radius `w₁` with centre in
`W`".  This file isolates the shape hypothesis that clause presupposes, `Metric.IsBallDense`,
verifies it for rectangular prisms, and proves the covering/packing comparison that uses it:
for a `β`-ball dense compact set `W` at scale `r` and a measurable `A ⊆ W`,
`|N_{λ r}(A)| ≤ C(n, λ, β) · |W ∩ N_r(A)|`.

Ball density is *not* automatic for a convex body (a thin triangle in the plane fails it at
its own apex at the scale of its smallest affine thickness), which is why it has to be carried
as a hypothesis; see the blueprint note `note:ballDenseNotAutomatic`.
-/

@[expose] public section

open Metric MeasureTheory

/-! ### Boxes in an orthonormal frame -/

section Box

variable {n : ℕ} {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [PseudoMetricSpace S] [NormedAddTorsor E S]

/-- The axis-aligned box of common side length `h` in the orthonormal frame `b` centred at `c`:
the set of points whose `i`-th frame coordinate (relative to `c`) lies in `[a i, a i + h]`. -/
def orthonormalBox (b : OrthonormalBasis (Fin n) ℝ E) (c : S) (a : Fin n → ℝ) (h : ℝ) : Set S :=
  {z | ∀ i, b.repr (z -ᵥ c) i ∈ Set.Icc (a i) (a i + h)}

/-- Blueprint `lem:prismSubBoxAtPoint`: a sub-box of a prism anchored at a point.
If `x` lies in a rectangular prism `P` and `0 < h ≤ min_i (P.thicknesses i)`, then each frame
coordinate of `x` can be caught in a closed interval of length `h` inside `[-tᵢ, tᵢ]`; the
resulting box `Q` satisfies `x ∈ Q ⊆ P`. -/
theorem PrismNDim.exists_orthonormalBox_at_point (P : PrismNDim n E S) {x : S}
    (hx : x ∈ (P.carrier : Set S)) {h : ℝ} (hh : 0 < h)
    (hle : ∀ i, h ≤ (P.thicknesses i : ℝ)) :
    ∃ a : Fin n → ℝ,
      x ∈ orthonormalBox P.basis P.center a h ∧
        orthonormalBox P.basis P.center a h ⊆ (P.carrier : Set S) := by
  let y : Fin n → ℝ := fun i => P.basis.repr (x -ᵥ P.center) i
  have hy_le : ∀ i, |y i| ≤ (P.thicknesses i : ℝ) := by
    intro i
    exact (P.mem_carrier_iff x).1 hx i
  let a : Fin n → ℝ := fun i =>
    if y i + h ≤ (P.thicknesses i : ℝ) then y i else y i - h
  have hmem : ∀ i, y i ∈ Set.Icc (a i) (a i + h) := by
    intro i
    by_cases hcond : y i + h ≤ (P.thicknesses i : ℝ)
    · have hyin : y i ∈ Set.Icc (y i) (y i + h) := ⟨le_rfl, by linarith [hh]⟩
      simpa [a, hcond] using hyin
    · have hyin : y i ∈ Set.Icc (y i - h) (y i) := ⟨by linarith, le_rfl⟩
      simpa [a, hcond] using hyin
  have hsub : ∀ i, Set.Icc (a i) (a i + h) ⊆
      Set.Icc (-(P.thicknesses i : ℝ)) (P.thicknesses i : ℝ) := by
    intro i
    by_cases hcond : y i + h ≤ (P.thicknesses i : ℝ)
    · have hy1 : -(P.thicknesses i : ℝ) ≤ y i := (abs_le.mp (hy_le i)).1
      simpa [a, hcond] using (Set.Icc_subset_Icc hy1 hcond)
    · have hy2 : y i ≤ (P.thicknesses i : ℝ) := (abs_le.mp (hy_le i)).2
      have hcond' : (P.thicknesses i : ℝ) < y i + h := lt_of_not_ge hcond
      have hhl : -(P.thicknesses i : ℝ) ≤ y i - h := by linarith [hy2, hcond', hle i, hh]
      simpa [a, hcond] using (Set.Icc_subset_Icc hhl hy2)
  refine ⟨a, ?_, ?_⟩
  · intro i
    exact hmem i
  · intro z hz
    rw [P.mem_carrier_iff]
    intro i
    have hzi : P.basis.repr (z -ᵥ P.center) i ∈ Set.Icc (a i) (a i + h) := hz i
    have hzi' : P.basis.repr (z -ᵥ P.center) i ∈
        Set.Icc (-(P.thicknesses i : ℝ)) (P.thicknesses i : ℝ) := (hsub i) hzi
    rw [Set.mem_Icc] at hzi'
    exact abs_le.mpr hzi'

/-- Blueprint `lem:boxSideInBall`: a box of side `h` in an orthonormal frame is contained in the
closed ball of radius `√n · h` about any of its points. -/
theorem orthonormalBox_subset_closedBall (b : OrthonormalBasis (Fin n) ℝ E) (c : S)
    (a : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h) {x : S} (hx : x ∈ orthonormalBox b c a h) :
    orthonormalBox b c a h ⊆ Metric.closedBall x (Real.sqrt n * h) := by
  intro z hz
  let w : E := z -ᵥ x
  have hcoord : ∀ i, |b.repr (z -ᵥ x) i| ≤ h := by
    intro i
    have hzi : b.repr (z -ᵥ c) i ∈ Set.Icc (a i) (a i + h) := by
      simpa [orthonormalBox] using hz i
    have hxi : b.repr (x -ᵥ c) i ∈ Set.Icc (a i) (a i + h) := by
      simpa [orthonormalBox] using hx i
    have hv : z -ᵥ x = (z -ᵥ c) - (x -ᵥ c) := by
      rw [← vsub_add_vsub_cancel z c x]
      rw [← neg_vsub_eq_vsub_rev x c]
      rw [sub_eq_add_neg]
    calc
      |b.repr (z -ᵥ x) i| = |b.repr (z -ᵥ c) i - b.repr (x -ᵥ c) i| := by
        rw [hv]
        rw [map_sub]
        simp
      _ ≤ h := by
        rw [abs_le]
        constructor <;> nlinarith [Set.mem_Icc.mp hzi, Set.mem_Icc.mp hxi, hh]
  -- Parseval: ‖w‖² = ∑_i (b.repr w i)²
  have hpow : ‖w‖ ^ 2 = ∑ i, (b.repr w i) ^ 2 := by
    rw [← b.sum_sq_inner_left w]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm]
    rw [← b.repr_apply_apply]
  have hsq : ∑ i, (b.repr w i) ^ 2 ≤ n * h ^ 2 := by
    calc
      (∑ i, (b.repr w i) ^ 2) = ∑ i, (|b.repr w i|) ^ 2 := by simp [sq_abs]
      _ ≤ ∑ i, h ^ 2 := by
        exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2)
      _ = n * h ^ 2 := by simp
  have hnorm2 : ‖w‖ ^ 2 ≤ (Real.sqrt n * h) ^ 2 := by
    calc
      ‖w‖ ^ 2 ≤ n * h ^ 2 := by rw [hpow]; exact hsq
      _ = (Real.sqrt n * h) ^ 2 := by
        rw [mul_pow]
        rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
  have hzn : ‖w‖ ≤ Real.sqrt n * h := by
    rw [← abs_of_nonneg (norm_nonneg w),
      ← abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg n) hh)]
    exact sq_le_sq.mp hnorm2
  have hdx : dist z x ≤ Real.sqrt n * h := by
    simpa [w, dist_eq_norm_vsub] using hzn
  exact (Metric.mem_closedBall).mpr hdx

end Box

section BoxVolume

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Blueprint `lem:boxVolume`: the volume of a box of side `h` in an orthonormal frame is
`h ^ n`, since the frame coordinate map is a measure-preserving isometry onto `ℝⁿ`. -/
theorem volume_orthonormalBox (b : OrthonormalBasis (Fin n) ℝ E) (c : E) (a : Fin n → ℝ)
    {h : ℝ} (hh : 0 ≤ h) :
    volume (orthonormalBox b c a h) = ENNReal.ofReal (h ^ n) := by
  -- The frame coordinate map `g : z ↦ (⟨z - c, bᵢ⟩)ᵢ` is a measure-preserving isometry onto `ℝⁿ`.
  have htrans : MeasurePreserving (fun z : E => z - c) volume volume := by
    simpa [sub_eq_add_neg] using (measurePreserving_add_right (volume : Measure E) (-c))
  have hb : MeasurePreserving (fun z : E => b.repr (z - c)) volume volume :=
    b.measurePreserving_repr.comp htrans
  have hcoord : MeasurePreserving (fun w : EuclideanSpace ℝ (Fin n) => (fun i : Fin n => w i))
      volume volume := PiLp.volume_preserving_ofLp (Fin n)
  let g : E → Fin n → ℝ := fun z i => (b.repr (z - c)) i
  have hg : MeasurePreserving g volume volume := by
    exact hcoord.comp hb
  -- It carries `Q` onto the product of the intervals `∏ᵢ Jᵢ`.
  let G : Set (Fin n → ℝ) := Set.pi Set.univ (fun i : Fin n => Set.Icc (a i) (a i + h))
  have hset : orthonormalBox b c a h = g ⁻¹' G := by
    ext z
    simp [orthonormalBox, G, g]
    constructor
    · intro h
      exact ⟨fun i => (h i).1, fun i => by linarith [(h i).2]⟩
    · intro h i
      exact ⟨h.1 i, by linarith [h.2 i]⟩
  have hG : NullMeasurableSet G volume :=
    (by measurability : MeasurableSet G).nullMeasurableSet
  rw [hset, hg.measure_preimage hG]
  -- The product of the intervals has measure `∏ᵢ |Jᵢ| = h ^ n`.
  dsimp only [G]
  rw [volume_pi_pi]
  rw [show (fun i : Fin n => volume (Set.Icc (a i) (a i + h))) = fun _ => ENNReal.ofReal h by
    funext i
    rw [Real.volume_Icc]
    congr 1
    ring]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hh]

end BoxVolume

/-! ### Ball density -/

namespace Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

/-- Blueprint `def:ballDense`: `W` is **`β`-ball dense at scale `r`** if
`|W ∩ B̄(x, s)| ≥ β · sⁿ` for every `x ∈ W` and every `0 < s ≤ r`, where `n` is the dimension
of the ambient Euclidean space.

This is the precise content of GWZ's parenthetical "`W` has dimensions roughly
`w₁ × ⋯ × wₙ`": the body is not allowed to taper away at any of its own points on scales
below `r`.  The density constant is written `β`, not `κ`, because in GWZ Section 5 the letter
`κ` already denotes the dimensional volume-comparison constant between a convex body and its
outer prism. -/
def IsBallDense (W : Set E) (r : ℝ) (β : NNReal) : Prop :=
  ∀ ⦃x⦄, x ∈ W → ∀ ⦃s : ℝ⦄, 0 < s → s ≤ r →
    (β : ENNReal) * ENNReal.ofReal (s ^ Module.finrank ℝ E) ≤ volume (W ∩ Metric.closedBall x s)

/-- Ball density at a scale implies ball density, with the same constant, at every smaller
positive scale. -/
theorem IsBallDense.mono_scale {W : Set E} {r r' : ℝ} {β : NNReal} (h : IsBallDense W r β)
    (hr : r' ≤ r) : IsBallDense W r' β :=
  fun _ hx _ hs hsr => h hx hs (hsr.trans hr)

end Metric

/-! ### Rectangular prisms are ball dense -/

namespace PrismNDim

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Blueprint `def:prismBallDenseConstant`: the ball-density constant of a rectangular prism,
`c(n) = n ^ (-n / 2)`.  It is positive and depends only on the ambient dimension `n`. -/
noncomputable abbrev isBallDense_carrier.c (n : ℕ) : NNReal :=
  ⟨(Real.sqrt n)⁻¹ ^ n, by positivity⟩

theorem isBallDense_carrier.c_pos (n : ℕ) : 0 < isBallDense_carrier.c n := by
  rw [← NNReal.coe_lt_coe]
  change (0 : ℝ) < (Real.sqrt n)⁻¹ ^ n
  rcases n with _ | m
  · simp
  · positivity

/-- Blueprint `lem:prismBallDense`: a rectangular prism whose half-widths all exceed `ρ > 0` is
`c(n)`-ball dense at scale `ρ`.

Combined with `Metric.IsBallDense.mono_scale` and `PrismNDim.thickness_carrier_le` (which gives
`τ_{n-1}(P) ≤ ρ`), a prism is also `c(n)`-ball dense at scale `τ_{n-1}(P)`.  This is exactly
why GWZ may invoke the volume-comparison clause for blocks "of dimensions roughly
`w₁ × ⋯ × wₙ`". -/
theorem isBallDense_carrier (P : PrismNDim n E E) {ρ : ℝ} (hρ : 0 < ρ)
    (hle : ∀ i, ρ ≤ (P.thicknesses i : ℝ)) :
    Metric.IsBallDense (P.carrier : Set E) ρ (isBallDense_carrier.c n) := by
  have _ : 0 < ρ := hρ
  intro x hx s hs hsr
  by_cases hn : 0 < n
  · let h : ℝ := s / Real.sqrt (n : ℝ)
    have hs_nat : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hs_nat
    have hh : 0 < h := by
      dsimp [h]
      exact div_pos hs hsq_pos
    have hsq1 : 1 ≤ Real.sqrt (n : ℝ) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
      simpa [Real.sqrt_one] using (Real.sqrt_le_sqrt h1)
    have hle_s : h ≤ s := by
      dsimp [h]
      exact div_le_self (le_of_lt hs) hsq1
    have hfin : Module.finrank ℝ E = n := by
      simpa using (Module.finrank_eq_card_basis P.basis.toBasis)
    have hle' : ∀ i, h ≤ (P.thicknesses i : ℝ) := by
      intro i
      exact hle_s.trans (hsr.trans (hle i))
    rcases PrismNDim.exists_orthonormalBox_at_point P hx hh hle' with ⟨a, hxQ, hQP⟩
    have hvol0 : volume (orthonormalBox P.basis P.center a h) = ENNReal.ofReal (h ^ n) :=
      volume_orthonormalBox P.basis P.center a (le_of_lt hh)
    have hpow : (h ^ n : ℝ) = (s ^ n) * (Real.sqrt (n : ℝ))⁻¹ ^ n := by
      dsimp [h]
      rw [div_eq_mul_inv, mul_pow]
    have hvolQ : volume (orthonormalBox P.basis P.center a h) =
        (isBallDense_carrier.c n : ENNReal) * ENNReal.ofReal (s ^ Module.finrank ℝ E) := by
      rw [hvol0, hfin, hpow, ENNReal.ofReal_mul (pow_nonneg (le_of_lt hs) n)]
      rw [← ENNReal.ofReal_coe_nnreal]
      rw [show ((isBallDense_carrier.c n : NNReal) : ℝ) = (Real.sqrt (n : ℝ))⁻¹ ^ n by rfl]
      rw [mul_comm]
    have hQball : orthonormalBox P.basis P.center a h ⊆ Metric.closedBall x s := by
      have hb : orthonormalBox P.basis P.center a h ⊆
          Metric.closedBall x (Real.sqrt (n : ℝ) * h) :=
        orthonormalBox_subset_closedBall P.basis P.center a (le_of_lt hh) hxQ
      have hmain : Real.sqrt (n : ℝ) * h = s := by
        dsimp [h]
        exact mul_div_cancel₀ s (ne_of_gt hsq_pos)
      simpa [hmain] using hb
    rw [← hvolQ]
    exact measure_mono (Set.subset_inter hQP hQball)
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hfin0 : Module.finrank ℝ E = 0 := by
      simpa [hn0] using (Module.finrank_eq_card_basis P.basis.toBasis)
    have heq : ∀ x y : E, x = y := by
      intro x y
      let hx0 : x = 0 := by
        rcases Module.finrank_eq_zero_iff.mp hfin0 x with ⟨a, ha0, hax⟩
        exact (smul_eq_zero.mp hax).resolve_left ha0
      let hy0 : y = 0 := by
        rcases Module.finrank_eq_zero_iff.mp hfin0 y with ⟨a, ha0, hay⟩
        exact (smul_eq_zero.mp hay).resolve_left ha0
      exact hx0.trans hy0.symm
    have hball : Metric.closedBall x s = Set.univ := by
      ext z
      constructor
      · intro hz
        trivial
      · intro hz
        have hzx : z = x := heq z x
        simp [hzx, le_of_lt hs]
    haveI : IsEmpty (Fin n) := by
      rw [hn0]
      infer_instance
    have hvolP : volume (P.carrier : Set E) = (1 : ENNReal) := by
      rw [PrismNDim.volume_carrier P, hfin0]
      simp
    have hvoltarget : volume ((P.carrier : Set E) ∩ Metric.closedBall x s) = (1 : ENNReal) := by
      rw [hball, Set.inter_univ, hvolP]
    have hcl : (isBallDense_carrier.c n : ENNReal) *
        ENNReal.ofReal (s ^ Module.finrank ℝ E) = (1 : ENNReal) := by
      rw [hn0, hfin0, pow_zero]
      rw [← ENNReal.ofReal_coe_nnreal]
      have hc0 : (isBallDense_carrier.c 0 : ℝ) = 1 := by
        change (Real.sqrt (0 : ℝ))⁻¹ ^ 0 = 1
        rw [Real.sqrt_zero]
        norm_num
      rw [hc0]
      simp [ENNReal.ofReal_one]
    rw [hcl]
    simp [hvoltarget]

end PrismNDim

/-! ### Separated subsets, coverings, and the volume comparison -/

namespace Metric

/-- Blueprint `lem:maximalSeparatedSubset`: a nonempty bounded set in a proper metric space
admits a finite nonempty `r`-separated subset which is also an `r`-cover of it.

This is `Metric.maximalSeparatedSet` packaged as a `Finset`; finiteness comes from finiteness
of the packing number of a bounded set. -/
theorem exists_finset_separated_cover {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {A : Set X} (hAne : A.Nonempty) (hA : Bornology.IsBounded A) {r : ℝ} (hr : 0 < r) :
    ∃ T : Finset X, (T : Set X) ⊆ A ∧ T.Nonempty ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → r < dist x y) ∧
      A ⊆ ⋃ x ∈ T, Metric.closedBall x r := by
  let ε : NNReal := r.toNNReal
  have hεr : (ε : ℝ) = r := by
    dsimp [ε]
    exact Real.coe_toNNReal r (le_of_lt hr)
  have hε0 : (0 : NNReal) < ε := by
    dsimp [ε]
    exact Real.toNNReal_pos.mpr hr
  -- Step 1: the packing number is finite.
  have hpack : Metric.packingNumber ε A ≠ ⊤ := by
    have h2e : (2 : NNReal) * (ε / 2) = ε := by
      have h2ne : (2 : NNReal) ≠ 0 := by norm_num
      calc
        (2 : NNReal) * (ε / 2) = (2 : NNReal) * (ε * (2 : NNReal)⁻¹) := by rw [div_eq_mul_inv]
        _ = ε * ((2 : NNReal) * (2 : NNReal)⁻¹) := by ring
        _ = ε := by rw [mul_inv_cancel₀ h2ne, mul_one]
    have h1 : Metric.packingNumber ε A ≤ Metric.externalCoveringNumber (ε / 2) A := by
      have hstep := Metric.packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A
      rwa [h2e] at hstep
    have h2 : Metric.externalCoveringNumber (ε / 2) A ≤ Metric.coveringNumber (ε / 2) A :=
      Metric.externalCoveringNumber_le_coveringNumber (ε / 2) A
    have hle : Metric.packingNumber ε A ≤ Metric.coveringNumber (ε / 2) A := h1.trans h2
    have hεhalf : (0 : NNReal) < ε / 2 := by
      rw [← NNReal.coe_lt_coe]
      rw [NNReal.coe_div]
      rw [show ((2 : NNReal) : ℝ) = 2 by norm_num]
      exact half_pos (by simpa [hεr] using hr)
    have h3 : Metric.coveringNumber (ε / 2) A ≠ ⊤ := hA.coveringNumber_ne_top hεhalf
    exact ne_of_lt (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr h3))
  -- Steps 2-3: the maximal separated set is finite.
  have hfin : (Metric.maximalSeparatedSet ε A).Finite := by
    rw [← Set.encard_ne_top_iff]
    rw [Metric.encard_maximalSeparatedSet hpack]
    exact hpack
  lift Metric.maximalSeparatedSet ε A to Finset X using hfin with T hT
  -- Step 6: `T` is nonempty, since it covers the nonempty set `A`.
  have hcovM : A ⊆ ⋃ y ∈ Metric.maximalSeparatedSet ε A, Metric.closedBall y (ε : ℝ) := by
    exact (Metric.isCover_iff_subset_iUnion_closedBall).mp
      (Metric.isCover_maximalSeparatedSet hpack)
  have hneM : (Metric.maximalSeparatedSet ε A).Nonempty := by
    rcases hAne with ⟨a, ha⟩
    rcases Set.mem_iUnion.mp (hcovM ha) with ⟨y, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hyM, _⟩
    exact ⟨y, hyM⟩
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · rw [hT]
    exact Metric.maximalSeparatedSet_subset
  · change (T : Set X).Nonempty
    simpa [← hT] using hneM
  · intro x hx y hy hxy
    have hsepT : Metric.IsSeparated (ε : ENNReal) (T : Set X) := by
      simpa [hT] using
        (Metric.isSeparated_maximalSeparatedSet : Metric.IsSeparated (ε : ENNReal)
          (Metric.maximalSeparatedSet ε A))
    have he : (ε : ENNReal) < edist x y := hsepT hx hy hxy
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal (p := ε)] at he
    have hre : (ε : ℝ) < dist x y :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ε.prop).mp he
    simpa [hεr] using hre
  · simpa [← hT, hεr] using hcovM

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

/-- Blueprint `lem:thickeningCoverUpper`: covering upper bound for a dilated thickening.
If `A` is covered by the `N` closed balls of radius `r` about the points of `T` and `λ ≥ 1`,
then `N_{λ r}(A)` is covered by the balls of radius `(λ + 1) r` about the same points, whence
`|N_{λ r}(A)| ≤ N · ωₙ · ((λ + 1) r)ⁿ`. -/
theorem volume_cthickening_le_of_cover {A : Set E} {r lam : ℝ} (hr : 0 < r) (hlam : 1 ≤ lam)
    {T : Finset E} (hcov : A ⊆ ⋃ x ∈ T, Metric.closedBall x r) :
    Metric.cthickening (lam * r) A ⊆ ⋃ x ∈ T, Metric.closedBall x ((lam + 1) * r) ∧
      volume (Metric.cthickening (lam * r) A)
        ≤ (T.card : ENNReal) * volume (Metric.closedBall (0 : E) ((lam + 1) * r)) := by
  letI := Classical.decEq E
  have hlam0 : 0 ≤ lam := by nlinarith
  have hr_nn : 0 ≤ r := le_of_lt hr
  have hlamr_nn : 0 ≤ lam * r := by nlinarith
  have hset : Metric.cthickening (lam * r) A ⊆ ⋃ x ∈ T, Metric.closedBall x ((lam + 1) * r) := by
    have h1 : Metric.cthickening (lam * r) A ⊆
        Metric.cthickening (lam * r) (⋃ x ∈ T, Metric.closedBall x r) :=
      Metric.cthickening_subset_of_subset (lam * r) hcov
    have h2 : Metric.cthickening (lam * r) (⋃ x ∈ T, Metric.closedBall x r) =
        ⋃ x ∈ T, Metric.closedBall x ((lam + 1) * r) := by
      refine Finset.induction_on T ?h0 ?hstep
      · simp [Metric.cthickening_empty]
      · intro a s ha ih
        rw [Finset.set_biUnion_insert a s (fun x : E => Metric.closedBall x r)]
        rw [Metric.cthickening_union]
        rw [ih]
        rw [Finset.set_biUnion_insert a s (fun x : E => Metric.closedBall x ((lam + 1) * r))]
        congr 1
        · rw [cthickening_closedBall hlamr_nn hr_nn a]
          congr 1
          ring
    exact h1.trans (le_of_eq h2)
  refine ⟨hset, ?_⟩
  calc
    volume (Metric.cthickening (lam * r) A)
        ≤ volume (⋃ x ∈ T, Metric.closedBall x ((lam + 1) * r)) := measure_mono hset
    _ ≤ ∑ x ∈ T, volume (Metric.closedBall x ((lam + 1) * r)) :=
        MeasureTheory.measure_biUnion_finset_le T (fun x => Metric.closedBall x ((lam + 1) * r))
    _ = ∑ x ∈ T, volume (Metric.closedBall (0 : E) ((lam + 1) * r)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [MeasureTheory.Measure.addHaar_closedBall_center volume x ((lam + 1) * r)]
    _ = (T.card : ENNReal) * volume (Metric.closedBall (0 : E) ((lam + 1) * r)) := by
        simp [Finset.sum_const]

/-- Blueprint `lem:ballDensePackingLower`: packing lower bound from ball density.
If `W` is `β`-ball dense at scale `r`, `A ⊆ W`, and the points of `T ⊆ A` are pairwise at
distance more than `r`, then the disjoint balls `B̄(x, r/3)`, `x ∈ T`, give
`|W ∩ N_r(A)| ≥ |T| · β · (r/3)ⁿ`. -/
theorem IsBallDense.card_mul_le_volume_inter_cthickening {W A : Set E} {r : ℝ} {β : NNReal}
    (hβ : IsBallDense W r β) (hWm : MeasurableSet W) (hr : 0 < r) (hAW : A ⊆ W) {T : Finset E}
    (hTA : (T : Set E) ⊆ A) (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → r < dist x y) :
    (T.card : ENNReal) *
        ((β : ENNReal) * ENNReal.ofReal ((r / 3) ^ Module.finrank ℝ E))
      ≤ volume (W ∩ Metric.cthickening r A) := by
  let c : ENNReal := (β : ENNReal) * ENNReal.ofReal ((r / 3) ^ Module.finrank ℝ E)
  let B : Set E := W ∩ Metric.cthickening r A
  let S : E → Set E := fun x => W ∩ Metric.closedBall x (r / 3)
  have hTW : (T : Set E) ⊆ W := hTA.trans hAW
  have hlow : ∀ x ∈ T, c ≤ volume (S x) := by
    intro x hx
    dsimp [c, S]
    exact hβ (hTW hx) (by positivity) (by nlinarith [hr])
  have hsub : ∀ x, x ∈ T → S x ⊆ B := by
    intro x hx z hz
    dsimp [B, S] at hz ⊢
    exact
      ⟨hz.1, (Metric.closedBall_subset_cthickening (hTA hx) (r / 3)).trans
        (Metric.cthickening_mono (by nlinarith [hr]) A) hz.2⟩
  have hdisj : (T : Set E).PairwiseDisjoint S := by
    intro x hx y hy hxy
    change Disjoint (S x) (S y)
    rw [Set.disjoint_left]
    intro z hzx hzy
    have hdx : dist z x ≤ r / 3 := Metric.mem_closedBall.mp hzx.2
    have hdy : dist z y ≤ r / 3 := Metric.mem_closedBall.mp hzy.2
    have hxy' : dist x y ≤ 2 * (r / 3) := by
      calc
        dist x y ≤ dist x z + dist z y := dist_triangle x z y
        _ ≤ r / 3 + r / 3 := add_le_add (by simpa [dist_comm] using hdx) hdy
        _ = 2 * (r / 3) := by ring
    have h23 : 2 * (r / 3) < r := by nlinarith [hr]
    exact (lt_irrefl r (lt_trans (hsep x hx y hy hxy) (lt_of_le_of_lt hxy' h23))).elim
  have hsum_le : (∑ x ∈ T, volume (S x)) ≤ volume (⋃ x ∈ T, S x) := by
    exact (measure_biUnion_finset hdisj (fun b _ => by measurability)).symm.le
  calc
    (T.card : ENNReal) * c = ∑ x ∈ T, c := by
      simp [Finset.sum_const]
    _ ≤ ∑ x ∈ T, volume (S x) := Finset.sum_le_sum fun x hx => hlow x hx
    _ ≤ volume (⋃ x ∈ T, S x) := hsum_le
    _ ≤ volume (W ∩ Metric.cthickening r A) := by
      exact measure_mono (by
        intro z hz
        rcases (Set.mem_iUnion.mp hz) with ⟨x, hx⟩
        rcases (Set.mem_iUnion.mp hx) with ⟨hxT, hxz⟩
        exact hsub x hxT hxz)

/-- Blueprint `def:thickeningBallDenseComparisonConstant`: the constant in
`Metric.volume_cthickening_le_of_isBallDense`,
`C(n, λ, β) = β⁻¹ · ωₙ · 3ⁿ · (λ + 1)ⁿ`, where `ωₙ = √π ^ n / Γ(n / 2 + 1)` is the volume of
the closed unit ball of an `n`-dimensional Euclidean space.  It depends only on the ambient
dimension `n`, on the dilation factor `λ`, and on the ball-density constant `β`. -/
noncomputable abbrev volume_cthickening_le_of_isBallDense.C (n : ℕ) (lam β : NNReal) : NNReal :=
  β⁻¹ * ⟨Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1), by positivity⟩ * 3 ^ n * (lam + 1) ^ n

/-- Blueprint `lem:thickeningBallDenseComparison`: a dilated thickening is comparable to the
induced shade.  If `W` is compact and `β`-ball dense at scale `r > 0`, `A ⊆ W` is measurable
and `λ ≥ 1`, then
`|N_{λ r}(A)| ≤ C(n, λ, β) · |W ∩ N_r(A)|`.

Both bounds are obtained from a maximal `r`-separated subset `T ⊆ A`: covering gives
`|N_{λ r}(A)| ≤ |T| ωₙ (λ+1)ⁿ rⁿ`, packing gives `|W ∩ N_r(A)| ≥ |T| β 3⁻ⁿ rⁿ`, and `|T| rⁿ`
is eliminated between them. -/
theorem volume_cthickening_le_of_isBallDense [Nontrivial E] {W A : Set E} {r : ℝ} {β lam : NNReal}
    (hW : IsCompact W) (hβ : IsBallDense W r β) (hr : 0 < r) (hβ0 : 0 < β)
    (hA : MeasurableSet A) (hAW : A ⊆ W) (hlam : 1 ≤ lam) :
    volume (Metric.cthickening ((lam : ℝ) * r) A)
      ≤ (volume_cthickening_le_of_isBallDense.C (Module.finrank ℝ E) lam β : ENNReal) *
        volume (W ∩ Metric.cthickening r A) := by
  by_cases hAe : A.Nonempty
  · set n : ℕ := Module.finrank ℝ E with hn
    let ω : NNReal := ⟨Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1), by positivity⟩
    have hCdef : volume_cthickening_le_of_isBallDense.C n lam β =
        β⁻¹ * ω * (3 : NNReal) ^ n * (lam + 1 : NNReal) ^ n := rfl
    have hAb : Bornology.IsBounded A := (IsCompact.isBounded hW).subset hAW
    rcases exists_finset_separated_cover hAe hAb hr with ⟨T, hTA, hTne, hsep, hcov⟩
    -- Covering upper bound.
    have hU : volume (Metric.cthickening ((lam : ℝ) * r) A)
        ≤ (T.card : ENNReal) *
          volume (Metric.closedBall (0 : E) (((lam : ℝ) + 1) * r)) := by
      exact (volume_cthickening_le_of_cover (r := r) (lam := (lam : ℝ))
        hr (NNReal.coe_le_coe.mpr hlam) hcov).2
    -- Packing lower bound.
    have hV : (T.card : ENNReal) * ((β : ENNReal) * ENNReal.ofReal ((r / 3) ^ n))
        ≤ volume (W ∩ Metric.cthickening r A) := by
      simpa [n] using
        (IsBallDense.card_mul_le_volume_inter_cthickening hβ
          hW.isClosed.measurableSet hr hAW hTA hsep)
    have hrpos : (0 : ℝ) ≤ r := le_of_lt hr
    -- `|B̄(0, (λ+1)r)| = ((λ+1)r)ⁿ · ω`.
    have hball : volume (Metric.closedBall (0 : E) (((lam : ℝ) + 1) * r))
        = ENNReal.ofReal (((lam : ℝ) + 1) * r) ^ n * (ω : ENNReal) := by
      rw [InnerProductSpace.volume_closedBall (0 : E) (((lam : ℝ) + 1) * r)]
      rw [← ENNReal.ofReal_coe_nnreal (p := ω)]
      congr 1
    -- `3ⁿ · (r/3)ⁿ = rⁿ`.
    have h3c : ((3 : NNReal) : ENNReal) = ENNReal.ofReal (3 : ℝ) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := (3 : NNReal))]
      norm_num
    have h3red : ((3 : NNReal) : ENNReal) ^ n * ENNReal.ofReal ((r / 3) ^ n)
        = (ENNReal.ofReal r) ^ n := by
      have h3pos : (0 : ℝ) ≤ (3 : ℝ) := by norm_num
      have h3m : (3 : ℝ) ^ n * (r / 3) ^ n = r ^ n := by
        rw [← mul_pow]
        congr 1
        ring
      rw [h3c, ← ENNReal.ofReal_pow h3pos,
        ← ENNReal.ofReal_mul (p := 3 ^ n) (q := (r / 3) ^ n)
          (by positivity : 0 ≤ (3 : ℝ) ^ n),
        ← ENNReal.ofReal_pow hrpos, h3m]
    -- `(λ+1)ⁿ · rⁿ = ((λ+1)r)ⁿ`.
    have hlco : ((lam + 1 : NNReal) : ENNReal) = ENNReal.ofReal ((lam : ℝ) + 1) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := (lam + 1 : NNReal))]
      congr 1
    have hlamred : ((lam + 1 : NNReal) : ENNReal) ^ n * (ENNReal.ofReal r) ^ n
        = ENNReal.ofReal (((lam : ℝ) + 1) * r) ^ n := by
      rw [hlco, ← mul_pow]
      congr 1
      exact (ENNReal.ofReal_mul (p := (lam : ℝ) + 1) (q := r)
        (by positivity : 0 ≤ (lam : ℝ) + 1)).symm
    -- `C · β = ω · 3ⁿ · (λ+1)ⁿ` in `NNReal`.
    have hb : (β⁻¹ * β : NNReal) = 1 := by
      apply Subtype.ext
      simp only [NNReal.val_eq_coe, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_one]
      exact inv_mul_cancel₀ (by exact_mod_cast (ne_of_gt hβ0))
    have hCβ : (volume_cthickening_le_of_isBallDense.C n lam β : NNReal) * β
        = ω * (3 : NNReal) ^ n * (lam + 1 : NNReal) ^ n := by
      rw [hCdef]
      rw [show (β⁻¹ * ω * (3 : NNReal) ^ n * (lam + 1 : NNReal) ^ n) * β =
            β⁻¹ * β * ω * (3 : NNReal) ^ n * (lam + 1 : NNReal) ^ n by ring]
      rw [hb]
      simp
    have hCβco : (volume_cthickening_le_of_isBallDense.C n lam β : ENNReal) *
        (β : ENNReal)
        = (((ω * (3 : NNReal) ^ n * (lam + 1 : NNReal) ^ n) : NNReal) : ENNReal) := by
      rw [← congrArg (fun x : NNReal => (x : ENNReal)) hCβ]
      exact ENNReal.coe_mul (volume_cthickening_le_of_isBallDense.C n lam β) β
    have hco4 : (((ω * (3 : NNReal) ^ n * (lam + 1 : NNReal) ^ n) : NNReal) : ENNReal)
        = (ω : ENNReal) * ((3 : NNReal) : ENNReal) ^ n *
            ((lam + 1 : NNReal) : ENNReal) ^ n := by
      simp [ENNReal.coe_mul, ENNReal.coe_pow]
    -- The constant identity: `|B̄(0,(λ+1)r)| = C(n,λ,β) · β · (r/3)ⁿ`.
    have hAeq : volume (Metric.closedBall (0 : E) (((lam : ℝ) + 1) * r))
        = (volume_cthickening_le_of_isBallDense.C n lam β : ENNReal) *
            ((β : ENNReal) * ENNReal.ofReal ((r / 3) ^ n)) := by
      calc
        volume (Metric.closedBall (0 : E) (((lam : ℝ) + 1) * r))
            = (ENNReal.ofReal (((lam : ℝ) + 1) * r)) ^ n * (ω : ENNReal) := hball
        _ = (ω : ENNReal) * ENNReal.ofReal (((lam : ℝ) + 1) * r) ^ n := by ring
        _ = (ω : ENNReal) * ((lam + 1 : NNReal) : ENNReal) ^ n *
            (ENNReal.ofReal r) ^ n := by
          rw [← hlamred]
          ring
        _ = (ω : ENNReal) * ((3 : NNReal) : ENNReal) ^ n *
            ((lam + 1 : NNReal) : ENNReal) ^ n * ENNReal.ofReal ((r / 3) ^ n) := by
          rw [← h3red]
          ring
        _ = (volume_cthickening_le_of_isBallDense.C n lam β : ENNReal) *
            ((β : ENNReal) * ENNReal.ofReal ((r / 3) ^ n)) := by
          rw [← hco4, ← hCβco]
          ring
    calc
      volume (Metric.cthickening ((lam : ℝ) * r) A)
          ≤ (T.card : ENNReal) *
            volume (Metric.closedBall (0 : E) (((lam : ℝ) + 1) * r)) := hU
      _ = (volume_cthickening_le_of_isBallDense.C n lam β : ENNReal) *
            ((T.card : ENNReal) *
              ((β : ENNReal) * ENNReal.ofReal ((r / 3) ^ n))) := by
            rw [hAeq]
            ring
      _ ≤ (volume_cthickening_le_of_isBallDense.C n lam β : ENNReal) *
            volume (W ∩ Metric.cthickening r A) := by
            gcongr
  · have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hAe
    subst A
    simp

end Metric
