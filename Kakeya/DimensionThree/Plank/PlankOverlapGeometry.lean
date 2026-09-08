/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank
public import Kakeya.DimensionThree.Volume
public import Kakeya.DimensionThree.Plank.ThickenedReprVolume

/-!
# Overlap geometry of congruent planks

The ED conflict-degree bound of `Kakeya/DimensionThree/Plank/EDExtraction.lean` needs the
implication

`volume (P ∩ Q) > (1/2) · volume P  →  Q ⊆ 11 • P`

for two congruent `a × b × 1` planks.  Every dilation lemma already in the repository
(`Plank.plank_subset_dilation_of_angle_le`, `Plank.slab_subset_dilation_of_angle_lt`,
`PrismNDim.perturbation_subset_dilation`) takes an *angle bound as a hypothesis*.  The content of
this file is to **derive** the frame bounds from the volume overlap, and then to assemble them into
an *anisotropic* containment.

## The three frame coefficients

Write `eᵢ := P.basis i` and `fⱼ := Q.basis j`.  A point of `Q` sits at frame displacement
`(s₀, s₁, s₂)` from a common point `p ∈ P ∩ Q`, with `|s₀| ≤ 2a`, `|s₁| ≤ 2b`, `|s₂| ≤ 2`.  To place
it inside a bounded dilation of `P` one needs, for each of `P`'s two thin normals, that the frame
coefficients pair with those displacements at the right scale:

* `|⟪e₀, f₁⟫| ≲ a / b` and `|⟪e₀, f₂⟫| ≲ a` — otherwise `Q` escapes `P`'s thin slab;
* `|⟪e₁, f₂⟫| ≲ b` — the in-plane rotation about the thin axis, which is *not* controlled at scale
  `a`.  This is why `PrismNDim.perturbation_subset_dilation`, which asks every frame vector to move
  by at most the smallest half-width, is the wrong tool: two planks with large overlap may genuinely
  differ by a rotation of size `b` about the thin axis.

## Where the estimates come from

All three are read off the anisotropic slab-traversal estimates already proved in
`Kakeya/DimensionThree/Volume.lean`, applied with the roles of the two planks exchanged:

* `ThickenedReprPrism3D.volume_inter_le_weighted` confines the intersection to `P`'s *thin*
  slab and gives
  `|P ∩ Q| ≤ 8 a² b / max (|⟪f₁, e₀⟫| · b) (|⟪f₂, e₀⟫|)`;
* `ThickenedReprPrism3D.volume_inter_le_weighted_mid` confines it to `P`'s *middle* slab and gives
  `|P ∩ Q| ≤ 8 a b² / max (|⟪f₀, e₁⟫| · a) (|⟪f₂, e₁⟫|)`.

Against the overlap lower bound `|P ∩ Q| > (1/2) · 8ab = 4ab` coming from failure of essential
distinctness, each denominator is forced below `2a` respectively `2b`.  No Fubini computation is
performed here; the shear step below is the Fubini-free device those estimates are built on, and is
retained as the standalone analytic lemma.

## The resulting constant

Summing the three contributions against `|s₀| ≤ 2a`, `|s₁| ≤ 2b`, `|s₂| ≤ 2` and the displacement of
`p` from `P.center` gives `11` in every coordinate, so `Q ⊆ P.dilation 11`.  The factor is absolute:
it depends neither on `a`, `b` nor on the planks.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

noncomputable section

namespace Kakeya

/-- The shear used by the slab-traversal estimate: it keeps the first two coordinates and replaces
the third by the linear form `α₀ x₀ + α₁ x₁ + α₂ x₂`.

Its matrix is lower triangular with diagonal `(1, 1, α₂)`, so its determinant is `α₂` — which is
exactly the sine of the angle the estimate controls. -/
def shearMap (α₀ α₁ α₂ : ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  Matrix.toLin' !![1, 0, 0; 0, 1, 0; α₀, α₁, α₂]

theorem shearMap_apply (α₀ α₁ α₂ : ℝ) (x : Fin 3 → ℝ) :
    shearMap α₀ α₁ α₂ x = ![x 0, x 1, α₀ * x 0 + α₁ * x 1 + α₂ * x 2] := by
  funext i
  fin_cases i <;> simp [shearMap, Matrix.toLin'_apply, Matrix.mulVec, Matrix.vecHead,
    Matrix.vecTail]
  ring

/-- The determinant of the shear is the coefficient it shears by. -/
theorem det_shearMap (α₀ α₁ α₂ : ℝ) :
    LinearMap.det (shearMap α₀ α₁ α₂) = α₂ := by
  rw [shearMap, LinearMap.det_toLin']
  simp [Matrix.det_fin_three]

/-- **The shear volume bound: the Fubini-free step of the slab-traversal estimate.**

A set of `ℝ³` whose points obey two coordinate bounds and one bound on a linear form whose third
coefficient is nonzero has volume at most `8 w₀ w₁ h / |α₂|`.

This is the whole analytic content of the slab-traversal estimate.  Geometrically `w₀, w₁` are two
half-widths of `Q`, `h` is the thin half-width of `P`, and `α₂ = ⟪f₂, e₀⟫` is the sine of the angle
between `Q`'s long axis and `P`'s long plane; the conclusion is `|P ∩ Q| ≤ 8 a² b / sin θ`.

No measurability hypothesis is needed: the set is contained in the preimage of a box under an
invertible linear map, and `volume` is monotone. -/
theorem volume_le_of_shear_bounds
    {α₀ α₁ α₂ : ℝ} (hα₂ : α₂ ≠ 0) {w₀ w₁ h : ℝ}
    (hw₀ : 0 ≤ w₀) (hw₁ : 0 ≤ w₁) (hh : 0 ≤ h)
    {A : Set (Fin 3 → ℝ)}
    (hbd : ∀ x ∈ A, |x 0| ≤ w₀ ∧ |x 1| ≤ w₁ ∧
      |α₀ * x 0 + α₁ * x 1 + α₂ * x 2| ≤ h) :
    volume A ≤ ENNReal.ofReal (8 * w₀ * w₁ * h / |α₂|) := by
  let T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := shearMap α₀ α₁ α₂
  let B : Set (Fin 3 → ℝ) := Set.Icc (-(![w₀, w₁, h])) (![w₀, w₁, h])
  have hdet : LinearMap.det T ≠ 0 := by
    simpa [T, det_shearMap] using hα₂
  have hAB : A ⊆ T ⁻¹' B := by
    intro x hx
    obtain ⟨h0, h1, h2⟩ := hbd x hx
    change shearMap α₀ α₁ α₂ x ∈ Set.Icc (-![w₀, w₁, h]) (![w₀, w₁, h])
    rw [shearMap_apply]
    constructor
    · intro i
      fin_cases i
      · simpa using (abs_le.mp h0).1
      · simpa using (abs_le.mp h1).1
      · simpa using (abs_le.mp h2).1
    · intro i
      fin_cases i
      · simpa using (abs_le.mp h0).2
      · simpa using (abs_le.mp h1).2
      · simpa using (abs_le.mp h2).2
  have hprod :
      (∏ i : Fin 3, ENNReal.ofReal (![w₀, w₁, h] i - (-(![w₀, w₁, h])) i)) =
        ENNReal.ofReal (8 * w₀ * w₁ * h) := by
    rw [Fin.prod_univ_three]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, Pi.neg_apply,
      sub_neg_eq_add, Matrix.cons_val_one, Matrix.cons_val]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ w₀ + w₀)]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (w₀ + w₀) * (w₁ + w₁))]
    congr 1
    ring
  have hBvol : volume B = ENNReal.ofReal (8 * w₀ * w₁ * h) := by
    dsimp [B]
    rw [Real.volume_Icc_pi]
    exact hprod
  calc
    volume A ≤ volume (T ⁻¹' B) := measure_mono hAB
    _ = ENNReal.ofReal |(LinearMap.det T)⁻¹| * volume B := by
      rw [Measure.addHaar_preimage_linearMap volume hdet]
    _ = ENNReal.ofReal |α₂⁻¹| * volume B := by
      simp [T, det_shearMap]
    _ = ENNReal.ofReal (8 * w₀ * w₁ * h / |α₂|) := by
      rw [hBvol]
      rw [mul_comm]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * w₀ * w₁ * h)]
      congr 1
      rw [abs_inv]
      ring

/-! ### Frame coordinates of a displacement inside a prism -/

/-- Two points of a prism differ by at most twice each half-width in every frame coordinate. -/
theorem abs_repr_vsub_le_two_mul_thicknesses {n : ℕ} {E S : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [PseudoMetricSpace S] [NormedAddTorsor E S]
    (R : PrismNDim n E S) {x p : S} (hx : x ∈ R.carrier) (hp : p ∈ R.carrier) (j : Fin n) :
    |R.basis.repr (x -ᵥ p) j| ≤ 2 * (R.thicknesses j : ℝ) := by
  rw [R.basis.repr_apply_apply, real_inner_comm]
  exact PrismNDim.abs_inner_vsub_basis_le R hp hx j

/-- Re-expansion of one orthonormal frame coordinate in another orthonormal frame. -/
theorem repr_eq_sum_inner_mul_repr {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c d : OrthonormalBasis (Fin n) ℝ E) (v : E) (i : Fin n) :
    c.repr v i = ∑ j, inner ℝ (c i) (d j) * d.repr v j := by
  rw [c.repr_apply_apply]
  conv_lhs => rw [← d.sum_repr v]
  rw [inner_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [real_inner_smul_right]
  ring

/-- Distinct unit frame vectors pair to at most one in absolute value. -/
theorem abs_inner_basis_le_one {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c d : OrthonormalBasis (Fin n) ℝ E) (i j : Fin n) :
    |inner ℝ (c i) (d j)| ≤ 1 := by
  calc
    |inner ℝ (c i) (d j)| ≤ ‖c i‖ * ‖d j‖ := abs_real_inner_le_norm (c i) (d j)
    _ = 1 := by simp

/-- Coordinatewise triangle inequality for a change of orthonormal frame in dimension three. -/
theorem abs_repr_le_sum_abs_inner_mul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c d : OrthonormalBasis (Fin 3) ℝ E) (v : E) (i : Fin 3) :
    |c.repr v i| ≤
      |inner ℝ (c i) (d 0)| * |d.repr v 0| + |inner ℝ (c i) (d 1)| * |d.repr v 1| +
        |inner ℝ (c i) (d 2)| * |d.repr v 2| := by
  rw [repr_eq_sum_inner_mul_repr c d v i, Fin.sum_univ_three]
  calc
    |inner ℝ (c i) (d 0) * d.repr v 0 + inner ℝ (c i) (d 1) * d.repr v 1 +
        inner ℝ (c i) (d 2) * d.repr v 2|
        ≤ |inner ℝ (c i) (d 0) * d.repr v 0| + |inner ℝ (c i) (d 1) * d.repr v 1| +
            |inner ℝ (c i) (d 2) * d.repr v 2| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |inner ℝ (c i) (d 0)| * |d.repr v 0| + |inner ℝ (c i) (d 1)| * |d.repr v 1| +
        |inner ℝ (c i) (d 2)| * |d.repr v 2| := by
      rw [abs_mul, abs_mul, abs_mul]

/-! ### Frame bounds from a large overlap -/

variable {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}

/-- The three half-widths of an `a × b × 1` plank, as real numbers. -/
theorem plank_thicknesses (P : Plank a b hab hb1) :
    ((P.thicknesses 0 : NNReal) : ℝ) = (a : ℝ) ∧ ((P.thicknesses 1 : NNReal) : ℝ) = (b : ℝ) ∧
      ((P.thicknesses 2 : NNReal) : ℝ) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [P.thicknesses_eq]

/-- **The overlap lower bound.**  Failure of essential distinctness for two congruent planks means
their intersection has volume more than `4ab`, half the volume of either. -/
theorem lt_volume_inter_of_not_isEssentiallyDistinct (P Q : Plank a b hab hb1)
    (hnd : ¬ _root_.IsEssentiallyDistinct (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    ENNReal.ofReal (4 * (a : ℝ) * (b : ℝ)) <
      volume ((P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
  have hnd' : (1 / 2) * max (volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      (volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) <
      volume ((P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
    rw [IsEssentiallyDistinct] at hnd
    exact not_le.mp hnd
  have hP : volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) =
      8 * (a : ENNReal) * (b : ENNReal) := by
    simpa using (Prism3D.volume_carrier P)
  have hQ : volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) =
      8 * (a : ENNReal) * (b : ENNReal) := by
    simpa using (Prism3D.volume_carrier Q)
  have hmax : max (volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      (volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) =
      8 * (a : ENNReal) * (b : ENNReal) := by
    rw [hP, hQ, max_self]
  have hvol : (1 / 2) * max (volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      (volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) =
      ENNReal.ofReal (4 * (a : ℝ) * (b : ℝ)) := by
    rw [hmax]
    have h8 : 8 * (a : ENNReal) * (b : ENNReal) =
        ENNReal.ofReal (8 * (a : ℝ) * (b : ℝ)) := by
      rw [← ENNReal.ofReal_ofNat (n := 8)]
      rw [← ENNReal.ofReal_coe_nnreal (p := a)]
      rw [← ENNReal.ofReal_coe_nnreal (p := b)]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * (a : ℝ))]
    have hhalf : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_ofNat (n := 2)]
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [hhalf, h8]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / 2 : ℝ))]
    congr 1
    ring
  rw [hvol] at hnd'
  exact hnd'

/-- Planks with a large overlap are nondegenerate: a plank of zero thickness is essentially
distinct from every other plank. -/
theorem pos_of_not_isEssentiallyDistinct (P Q : Plank a b hab hb1)
    (hnd : ¬ _root_.IsEssentiallyDistinct (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    0 < (a : ℝ) := by
  rw [NNReal.coe_pos, pos_iff_ne_zero]
  intro ha0
  have hlt : (0 : ENNReal) < volume (P.carrier ∩ Q.carrier) := by
    have h := lt_volume_inter_of_not_isEssentiallyDistinct P Q hnd
    simpa [ha0] using h
  have hvol0 : volume (P.carrier ∩ Q.carrier) ≤ 0 := by
    have hle : volume (P.carrier ∩ Q.carrier) ≤
        volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
      measure_mono Set.inter_subset_left
    have hvolP : volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) = 0 := by
      rw [Prism3D.volume_carrier P]
      simp [ha0]
    exact hle.trans_eq hvolP
  exact (not_lt_of_ge hvol0) hlt

/-- **Thin-normal frame bound from a large overlap.**  Both frame coefficients of `P`'s thin normal
against `Q`'s two other axes are controlled, each at its own scale: the middle one at scale `a / b`
and the long one at scale `a`.

This is `ThickenedReprPrism3D.volume_inter_le_weighted` applied with the two planks exchanged,
against the
overlap lower bound. -/
theorem abs_inner_thin_le_of_not_isEssentiallyDistinct (P Q : Plank a b hab hb1)
    (hnd : ¬ _root_.IsEssentiallyDistinct (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    (b : ℝ) * |inner ℝ (P.basis 0) (Q.basis 1)| ≤ 2 * (a : ℝ) ∧
      |inner ℝ (P.basis 0) (Q.basis 2)| ≤ 2 * (a : ℝ) := by
  set A₁ : ℝ := |inner ℝ (Q.basis 1) (P.basis 0)| with hA₁
  set A₂ : ℝ := |inner ℝ (Q.basis 2) (P.basis 0)| with hA₂
  set M : ℝ := max (A₁ * (b : ℝ)) (A₂ * 1) with hM_def
  have ha_pos : 0 < (a : ℝ) := pos_of_not_isEssentiallyDistinct P Q hnd
  have hb_pos : 0 < (b : ℝ) := lt_of_lt_of_le ha_pos (by exact_mod_cast hab)
  have hb_nn : 0 < b := by exact_mod_cast hb_pos
  have hA1_nonneg : 0 ≤ A₁ := by simp [hA₁]
  have hA2_nonneg : 0 ≤ A₂ := by simp [hA₂]
  have hM_nonneg : 0 ≤ M := by
    rw [hM_def]
    exact le_trans (mul_nonneg hA1_nonneg (le_of_lt hb_pos)) (le_max_left _ _)
  by_cases hM : 0 < M
  · have hvol : volume ((Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ P.carrier) ≤
        ENNReal.ofReal (8 * (a : ℝ) ^ 2 * (b : ℝ) / M) := by
      simpa [hM_def, hA₁, hA₂] using
        (ThickenedReprPrism3D.volume_inter_le_weighted (P₁ := Q) (P₂ := P) (c := 1)
          (hb := hb_nn) (hc := zero_lt_one)
          (hpos := by simpa [hM_def, hA₁, hA₂] using hM))
    have hlt : ENNReal.ofReal (4 * (a : ℝ) * (b : ℝ)) <
        ENNReal.ofReal (8 * (a : ℝ) ^ 2 * (b : ℝ) / M) := by
      have hlt0' : ENNReal.ofReal (4 * (a : ℝ) * (b : ℝ)) <
          volume ((Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ P.carrier) := by
        simpa [Set.inter_comm] using lt_volume_inter_of_not_isEssentiallyDistinct P Q hnd
      exact lt_of_lt_of_le hlt0' hvol
    have hprod_pos : 0 < 4 * (a : ℝ) * (b : ℝ) := by positivity
    have hden_pos : 0 < 8 * (a : ℝ) ^ 2 * (b : ℝ) / M := by
      have hright_enn : 0 < ENNReal.ofReal (8 * (a : ℝ) ^ 2 * (b : ℝ) / M) :=
        lt_trans (ENNReal.ofReal_pos.mpr hprod_pos) hlt
      exact ENNReal.ofReal_pos.mp hright_enn
    have hreal : 4 * (a : ℝ) * (b : ℝ) < 8 * (a : ℝ) ^ 2 * (b : ℝ) / M :=
      (ENNReal.ofReal_lt_ofReal_iff hden_pos).mp hlt
    have hM_lt : M < 2 * (a : ℝ) := by
      have hmul : 4 * (a : ℝ) * (b : ℝ) * M < 8 * (a : ℝ) ^ 2 * (b : ℝ) :=
        (lt_div_iff₀ hM).mp hreal
      nlinarith
    constructor
    · rw [real_inner_comm, ← hA₁, mul_comm]
      calc
        A₁ * (b : ℝ) ≤ M := by simp [hM_def]
        _ ≤ 2 * (a : ℝ) := le_of_lt hM_lt
    · rw [real_inner_comm, ← hA₂]
      calc
        A₂ = A₂ * 1 := by rw [mul_one]
        _ ≤ M := by simp [hM_def]
        _ ≤ 2 * (a : ℝ) := le_of_lt hM_lt
  · have hM_zero : M = 0 := le_antisymm (le_of_not_gt hM) hM_nonneg
    have hA1b_zero : A₁ * (b : ℝ) = 0 := by
      have hle : A₁ * (b : ℝ) ≤ 0 := by
        calc
          A₁ * (b : ℝ) ≤ M := by simp [hM_def]
          _ = 0 := hM_zero
      have hge : 0 ≤ A₁ * (b : ℝ) := mul_nonneg hA1_nonneg (le_of_lt hb_pos)
      exact le_antisymm hle hge
    have hA1_zero : A₁ = 0 :=
      (mul_eq_zero.mp hA1b_zero).resolve_right (ne_of_gt hb_pos)
    have hA2_zero : A₂ = 0 := by
      have hle : A₂ ≤ 0 := by
        calc
          A₂ = A₂ * 1 := by rw [mul_one]
          _ ≤ max (A₁ * (b : ℝ)) (A₂ * 1) := le_max_right _ _
          _ = M := by rw [hM_def]
          _ = 0 := hM_zero
      exact le_antisymm hle hA2_nonneg
    constructor
    · rw [real_inner_comm, ← hA₁, hA1_zero, mul_zero]
      positivity
    · rw [real_inner_comm, ← hA₂, hA2_zero]
      positivity

/-- **Middle-normal frame bound from a large overlap.**  The coefficient measuring how far `Q`'s
long axis tilts out of `P`'s middle direction is controlled at scale `b`, not at scale `a`.

This is `ThickenedReprPrism3D.volume_inter_le_weighted_mid` applied with the two planks
exchanged, against the
overlap lower bound.  It is exactly the in-plane rotation control that a generic perturbation lemma
cannot provide. -/
theorem abs_inner_mid_le_of_not_isEssentiallyDistinct (P Q : Plank a b hab hb1)
    (hnd : ¬ _root_.IsEssentiallyDistinct (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    |inner ℝ (P.basis 1) (Q.basis 2)| ≤ 2 * (b : ℝ) := by
  classical
  let m₀ : ℝ := |inner ℝ (Q.basis 0) (P.basis 1)|
  let m₂ : ℝ := |inner ℝ (Q.basis 2) (P.basis 1)|
  let M : ℝ := max (m₀ * (a : ℝ)) (m₂ * (1 : ℝ))
  have ha_pos : 0 < (a : ℝ) := pos_of_not_isEssentiallyDistinct P Q hnd
  have ha_pos_nn : 0 < a := by exact_mod_cast ha_pos
  have hb_pos : 0 < (b : ℝ) := lt_of_lt_of_le ha_pos (by exact_mod_cast hab)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M, m₀, m₂]
    positivity
  have hm₂_le_M : m₂ ≤ M := by
    dsimp [M]
    simpa using (le_max_right : m₂ * (1 : ℝ) ≤ max (m₀ * (a : ℝ)) (m₂ * (1 : ℝ)))
  have hM_le_2b : M ≤ 2 * (b : ℝ) := by
    by_cases hMpos : 0 < M
    · have hvol := ThickenedReprPrism3D.volume_inter_le_weighted_mid (P₁ := Q) (P₂ := P) ha_pos_nn
        (by norm_num : 0 < (1 : NNReal)) hMpos
      have hvol' : volume ((Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ P.carrier) ≤
          ENNReal.ofReal (8 * (b : ℝ) ^ 2 * (a : ℝ) * (1 : ℝ) / M) := by
        simpa [M, m₀, m₂] using hvol
      have hvol_lb : ENNReal.ofReal (4 * (a : ℝ) * (b : ℝ)) <
          volume ((P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
            (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :=
        lt_volume_inter_of_not_isEssentiallyDistinct P Q hnd
      have hlt : ENNReal.ofReal (4 * (a : ℝ) * (b : ℝ)) <
          ENNReal.ofReal (8 * (b : ℝ) ^ 2 * (a : ℝ) * (1 : ℝ) / M) := by
        exact lt_of_lt_of_le hvol_lb (by simpa [Set.inter_comm] using hvol')
      have hlt_real : 4 * (a : ℝ) * (b : ℝ) <
          8 * (b : ℝ) ^ 2 * (a : ℝ) * (1 : ℝ) / M := by
        have hstrict : 0 < 8 * (b : ℝ) ^ 2 * (a : ℝ) * (1 : ℝ) / M := by
          positivity
        exact (ENNReal.ofReal_lt_ofReal_iff hstrict).mp hlt
      have hMult : 4 * (a : ℝ) * (b : ℝ) * M < 8 * (a : ℝ) * (b : ℝ) ^ 2 := by
        nlinarith [(lt_div_iff₀ hMpos).mp hlt_real]
      have hM_lt : M < 2 * (b : ℝ) := by
        by_contra h
        have hbge : 2 * (b : ℝ) ≤ M := le_of_not_gt h
        have hmul : 4 * (a : ℝ) * (b : ℝ) * (2 * (b : ℝ)) ≤
            4 * (a : ℝ) * (b : ℝ) * M := by
          exact mul_le_mul_of_nonneg_left hbge (by positivity)
        nlinarith [hMult, hmul, ha_pos, hb_pos]
      exact le_of_lt hM_lt
    · have hM_eq : M = 0 := le_antisymm (le_of_not_gt hMpos) hM_nonneg
      rw [hM_eq]
      positivity
  have hm₂_le_2b : m₂ ≤ 2 * (b : ℝ) := le_trans hm₂_le_M hM_le_2b
  simpa [m₂, real_inner_comm] using hm₂_le_2b

/-! ### The anisotropic dilation -/

/-- **The displacement bound.**  For two planks with a large overlap, the displacement between any
two points of `Q` has, in *`P`*'s frame, every coordinate bounded by ten times `P`'s corresponding
half-width.

This is where the three frame bounds are spent.  Each of `Q`'s half-widths `2a`, `2b`, `2` is paired
with the frame coefficient that matches it, so the anisotropy is preserved: the long displacement
`2` meets the coefficient bounded by `a` (resp. `b`), not by `1`. -/
theorem abs_repr_vsub_le_of_not_isEssentiallyDistinct (P Q : Plank a b hab hb1)
    (hnd : ¬ _root_.IsEssentiallyDistinct (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    {x p : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hp : p ∈ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) (i : Fin 3) :
    |P.basis.repr (x -ᵥ p) i| ≤ 10 * (P.thicknesses i : ℝ) := by
  obtain ⟨hPt0, hPt1, hPt2⟩ := plank_thicknesses P
  obtain ⟨hQt0, hQt1, hQt2⟩ := plank_thicknesses Q
  obtain ⟨hthin1, hthin2⟩ := abs_inner_thin_le_of_not_isEssentiallyDistinct P Q hnd
  have hmid := abs_inner_mid_le_of_not_isEssentiallyDistinct P Q hnd
  have ha0 : (0:ℝ) ≤ (a:ℝ) := (a : NNReal).coe_nonneg
  have hb0 : (0:ℝ) ≤ (b:ℝ) := (b : NNReal).coe_nonneg
  have hab' : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
  have hb1' : (b:ℝ) ≤ 1 := by exact_mod_cast hb1
  -- displacement bounds inside Q
  have hs0 : |Q.basis.repr (x -ᵥ p) 0| ≤ 2 * (a:ℝ) := by
    simpa [hQt0] using abs_repr_vsub_le_two_mul_thicknesses Q.toPrismNDim hx hp 0
  have hs1 : |Q.basis.repr (x -ᵥ p) 1| ≤ 2 * (b:ℝ) := by
    simpa [hQt1] using abs_repr_vsub_le_two_mul_thicknesses Q.toPrismNDim hx hp 1
  have hs2 : |Q.basis.repr (x -ᵥ p) 2| ≤ 2 := by
    simpa [hQt2] using abs_repr_vsub_le_two_mul_thicknesses Q.toPrismNDim hx hp 2
  have hexp := abs_repr_le_sum_abs_inner_mul P.basis Q.basis (x -ᵥ p) i
  have hs0' : (0:ℝ) ≤ |Q.basis.repr (x -ᵥ p) 0| := abs_nonneg _
  have hs1' : (0:ℝ) ≤ |Q.basis.repr (x -ᵥ p) 1| := abs_nonneg _
  have hs2' : (0:ℝ) ≤ |Q.basis.repr (x -ᵥ p) 2| := abs_nonneg _
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by
    fin_cases i <;> simp
  rcases hcases with rfl | rfl | rfl
  · -- thickness a; bound 10a
    rw [hPt0]
    nlinarith [abs_inner_basis_le_one P.basis Q.basis 0 0,
      abs_nonneg (inner ℝ (P.basis 0) (Q.basis 0)),
      abs_nonneg (inner ℝ (P.basis 0) (Q.basis 1)),
      abs_nonneg (inner ℝ (P.basis 0) (Q.basis 2)),
      hexp, hs0, hs1, hs2, hthin1, hthin2, hs0', hs1', hs2']
  · -- thickness b; bound 10b
    rw [hPt1]
    nlinarith [abs_inner_basis_le_one P.basis Q.basis 1 0,
      abs_inner_basis_le_one P.basis Q.basis 1 1,
      abs_nonneg (inner ℝ (P.basis 1) (Q.basis 2)),
      hexp, hs0, hs1, hs2, hmid, hs0', hs1', hs2']
  · -- thickness 1; bound 10
    rw [hPt2]
    nlinarith [abs_inner_basis_le_one P.basis Q.basis 2 0,
      abs_inner_basis_le_one P.basis Q.basis 2 1,
      abs_inner_basis_le_one P.basis Q.basis 2 2,
      hexp, hs0, hs1, hs2, hs0', hs1', hs2']

/-- **Large overlap forces bounded anisotropic dilation.**

If two congruent `a × b × 1` planks fail to be essentially distinct — that is, if their intersection
has more than half the volume of either — then one is contained in the `11`-fold dilation of the
other.  The factor `11` is absolute: it depends neither on `a`, `b` nor on the planks.

No angle bound, frame alignment or centre proximity is assumed; all three are derived from the
volume overlap by `Kakeya.abs_inner_thin_le_of_not_isEssentiallyDistinct` and
`Kakeya.abs_inner_mid_le_of_not_isEssentiallyDistinct`.  The dilation is anisotropic, each axis of
`P` being stretched by `11` times *its own* half-width; an isotropic statement would be false, since
two planks with large overlap may differ by a rotation of size `b` about the thin axis. -/
theorem large_overlap_plank_subset_dilation (P Q : Plank a b hab hb1)
    (hnd : ¬ _root_.IsEssentiallyDistinct (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      ((P.toPrismNDim.dilation 11).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  have hvol : volume ((P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
      (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) ≠ 0 := by
    exact ne_of_gt (lt_of_le_of_lt
      (by positivity : (0 : ENNReal) ≤ ENNReal.ofReal (4 * (a : ℝ) * (b : ℝ)))
      (lt_volume_inter_of_not_isEssentiallyDistinct P Q hnd))
  have hne : ((P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
      (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))).Nonempty :=
    nonempty_of_measure_ne_zero hvol
  rcases hne with ⟨p, hpP, hpQ⟩
  intro x hx
  rw [(P.toPrismNDim.dilation 11).mem_carrier_iff]
  intro i
  rw [PrismNDim.dilation_center, PrismNDim.dilation_basis, PrismNDim.dilation_thicknesses]
  push_cast
  change |P.basis.repr (x -ᵥ P.center) i| ≤ (11 : ℝ) * (P.thicknesses i : ℝ)
  have hmain : |P.basis.repr (x -ᵥ p) i| ≤ 10 * (P.thicknesses i : ℝ) :=
    abs_repr_vsub_le_of_not_isEssentiallyDistinct P Q hnd hx hpQ i
  calc
    |P.basis.repr (x -ᵥ P.center) i| = |P.basis.repr ((x -ᵥ p) + (p -ᵥ P.center)) i| := by
      rw [← vsub_add_vsub_cancel x p P.center]
    _ = |P.basis.repr (x -ᵥ p) i + P.basis.repr (p -ᵥ P.center) i| := by
      simp
    _ ≤ |P.basis.repr (x -ᵥ p) i| + |P.basis.repr (p -ᵥ P.center) i| := abs_add_le _ _
    _ ≤ |P.basis.repr (x -ᵥ p) i| + (P.thicknesses i : ℝ) := by
      gcongr
      exact ((P.mem_carrier_iff p).1 hpP) i
    _ ≤ 10 * (P.thicknesses i : ℝ) + (P.thicknesses i : ℝ) := by
      nlinarith [add_le_add_right hmain (P.thicknesses i : ℝ)]
    _ = 11 * (P.thicknesses i : ℝ) := by ring

end Kakeya

end

end
