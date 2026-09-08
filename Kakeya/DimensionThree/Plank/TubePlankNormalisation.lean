/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.FrostmanPlankGeometry
public import Kakeya.DimensionThree.AffineTransport
public import Kakeya.DimensionThree.Volume

/-!
# Normalising the fine tubes inside a factor plank (Part (B) inner geometry)

The geometric core of `Plank.normaliseTubesInsidePlank`: under the affine normalisation `f` of an
`a × b × 1` plank `W` (`Plank.IsPlankNormalisation`), a fine `δ`-tube `T ⊆ W` acquires an outer
plank model of dimensions `(δ/b) × (δ/a) × 1` whose thin normal is orthogonal to `g 0`.

The construction is explicit.  Write `D` for the linear part of `f`, so that
`⟪f x - f y, g i⟫ = (κ / w i) ⟪x - y, W.basis i⟫` with `w = (a, b, 1)`
(`Plank.inner_image_sub_basis`).  Let `T` have endpoints `T.x`, `T.y` at distance `1` and put
`d = f T.y - f T.x`, which is nonzero.  The model plank is

* centred at `f T.center`;
* with long axis `ŵ = d / ‖d‖`;
* with thin normal `n` a unit vector orthogonal to **both** `ŵ` and `g 0`
  (`Plank.exists_unit_orthogonal_pair`, using `dim = 3`);
* with middle axis completing `n, ŵ` to an orthonormal frame
  (`Plank.exists_orthonormalBasis_fst_thd_eq`).

The three containment estimates are then independent of each other.

* Thin direction: the axis contributes nothing (`n ⊥ ŵ`), and since `n ⊥ g 0` the transverse
  ball of radius `δ` contributes at most `√2 · κ · δ / b ≤ δ / b`, because `3κ² ≤ 1`
  (`Plank.three_mul_sq_le_one_of_image_subset_closedBall`).
* Middle direction: again no axis contribution, and the ball contributes at most
  `√3 · κ · δ / a ≤ δ / a`.
* Long direction: no estimate on the linear part is needed.  A `δ`-tube is symmetric about its
  centre, so for `x ∈ T` the reflected point `2 • T.center - x` also lies in `T`; both images lie
  in the unit ball, and `f T.center` is their midpoint, whence `‖f x - f T.center‖ ≤ 1`.

The remaining two facts the consumer needs are the tangency bound
(`Plank.abs_inner_slabNormal_le_of_angle`: a slab meeting the model plank at angle `≤ θ` has its own
normal within `θ` of the model's long plane, hence nearly orthogonal to `g 0`) and the maximal
density transfer (`Plank.maxDensity_le_of_image_subset`), which uses that `f` is an affine
*equivalence* (`Plank.exists_affineEquiv_of_isPlankNormalisation`) with Jacobian `κ³ / (a b)`
(`Plank.jacobian_eq`), together with the two-sided tube volume bounds of `Tube.le_volume`.
-/

@[expose] public section

open MeasureTheory Kakeya
open scoped NNReal Real

noncomputable section

namespace Plank

/-! ### Linear algebra in dimension three -/

/-- **A unit vector orthogonal to two prescribed vectors** in `EuclideanSpace ℝ (Fin 3)`.
The span of two vectors has rank at most `2 < 3`, so its orthogonal complement is nonzero;
normalising a nonzero element gives the claim. -/
theorem exists_unit_orthogonal_pair (u v : EuclideanSpace ℝ (Fin 3)) :
    ∃ n : EuclideanSpace ℝ (Fin 3), ‖n‖ = 1 ∧ inner ℝ n u = 0 ∧ inner ℝ n v = 0 := by
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
    Submodule.span ℝ ({u, v} : Set (EuclideanSpace ℝ (Fin 3)))
  have hfin : Module.finrank ℝ K ≤ 2 := by
    dsimp [K]
    calc
      Module.finrank ℝ (Submodule.span ℝ ({u, v} : Set (EuclideanSpace ℝ (Fin 3))))
          ≤ ({u, v} : Set (EuclideanSpace ℝ (Fin 3))).toFinset.card :=
            finrank_span_le_card (R := ℝ) ({u, v} : Set (EuclideanSpace ℝ (Fin 3)))
      _ ≤ 2 := by
        rw [show ({u, v} : Set (EuclideanSpace ℝ (Fin 3))).toFinset
            = ({u, v} : Finset (EuclideanSpace ℝ (Fin 3))) by simp]
        calc
          ({u, v} : Finset (EuclideanSpace ℝ (Fin 3))).card
              ≤ ({v} : Finset (EuclideanSpace ℝ (Fin 3))).card + 1 :=
                Finset.card_insert_le (s := ({v} : Finset (EuclideanSpace ℝ (Fin 3)))) (a := u)
          _ ≤ 2 := by simp
  have horth : Module.finrank ℝ K + Module.finrank ℝ Kᗮ = 3 := by
    simpa [finrank_euclideanSpace_fin] using
      (Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) K)
  have hpo : 0 < Module.finrank ℝ Kᗮ := by
    omega
  have hne : Kᗮ ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff (R := ℝ) (S := Kᗮ)]
    exact Nat.succ_le_of_lt hpo
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hne with ⟨w, hw_mem, hw_ne⟩
  have hwKo : ∀ z : EuclideanSpace ℝ (Fin 3), z ∈ K → inner ℝ z w = 0 := by
    exact (Submodule.mem_orthogonal (K := K) (v := w)).mp hw_mem
  have hu_mem : u ∈ K := by
    dsimp [K]
    exact Submodule.subset_span (R := ℝ) (s := ({u, v} : Set (EuclideanSpace ℝ (Fin 3))))
      (show u ∈ ({u, v} : Set (EuclideanSpace ℝ (Fin 3))) by simp)
  have hv_mem : v ∈ K := by
    dsimp [K]
    exact Submodule.subset_span (R := ℝ) (s := ({u, v} : Set (EuclideanSpace ℝ (Fin 3))))
      (show v ∈ ({u, v} : Set (EuclideanSpace ℝ (Fin 3))) by simp)
  have hwu : inner ℝ u w = 0 := hwKo u hu_mem
  have hwv : inner ℝ v w = 0 := hwKo v hv_mem
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
  refine ⟨(‖w‖⁻¹ : ℝ) • w, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (ne_of_gt hw_pos)]
  · rw [real_inner_smul_left, real_inner_comm, hwu]
    norm_num
  · rw [real_inner_smul_left, real_inner_comm, hwv]
    norm_num

/-- **An orthonormal frame with prescribed first and last vector.**  Two orthonormal vectors of
`EuclideanSpace ℝ (Fin 3)` extend to an orthonormal basis placing them in positions `0` and `2`;
this is `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` applied to the partial family
`![u, 0, v]` on the set `{0, 2}`. -/
theorem exists_orthonormalBasis_fst_thd_eq {u v : EuclideanSpace ℝ (Fin 3)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) :
    ∃ B : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)), B 0 = u ∧ B 2 = v := by
  let w : Fin 3 → EuclideanSpace ℝ (Fin 3) := ![u, 0, v]
  let s : Set (Fin 3) := ({0, 2} : Set (Fin 3))
  have hw0 : w 0 = u := rfl
  have hw2 : w 2 = v := rfl
  have hw : Orthonormal ℝ (s.restrict w) := by
    constructor
    · intro i
      change ‖w i.1‖ = 1
      rcases i with ⟨i₀, hi⟩
      fin_cases i₀
      · simp [hw0, hu]
      · simp [s] at hi
      · simp [hw2, hv]
    · intro i j hij
      change inner ℝ (w i.1) (w j.1) = 0
      rcases i with ⟨i₀, hi⟩
      rcases j with ⟨j₀, hj⟩
      have hij₀ : i₀ ≠ j₀ := by
        intro h
        apply hij
        exact Subtype.ext h
      fin_cases i₀ <;> fin_cases j₀ <;> first
        | exfalso; exact (hij₀ rfl)
        | simp [w, real_inner_comm, huv]
  rcases (Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin 3)) (ι := Fin 3)
      (card_ι := by simp) (v := w) (s := s) (hv := hw)) with ⟨B, hB⟩
  exact ⟨B, by simpa [hw0] using hB 0 (by simp [s]), by simpa [hw2] using hB 2 (by simp [s])⟩

/-! ### The linear part of a plank normalisation -/

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}

/-- **Coordinates of a normalisation displacement.**  For a plank normalisation `f` of `W`, the
`g i`-coordinate of `f x - f y` is the `W.basis i`-coordinate of `x - y`, scaled by
`κ / W.thicknesses i`.  Immediate from `Plank.IsPlankNormalisation` at `x` and at `y`. -/
theorem inner_image_sub_basis (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g) (x y : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    inner ℝ (f x - f y) (g i)
      = κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - y) (W.basis i) := by
  have hx := hnorm x
  have hy := hnorm y
  let col (j : Fin 3) (u : EuclideanSpace ℝ (Fin 3)) :
      EuclideanSpace ℝ (Fin 3) :=
    (κ * ((W.thicknesses j : ℝ))⁻¹ * inner ℝ (u - W.center) (W.basis j)) • g j
  have hxcol : f x = f W.center + ∑ j : Fin 3, col j x := by
    simpa [col] using hx
  have hycol : f y = f W.center + ∑ j : Fin 3, col j y := by
    simpa [col] using hy
  have hdiff : f x - f y
      = ∑ j : Fin 3, (κ * ((W.thicknesses j : ℝ))⁻¹
          * (inner ℝ (x - W.center) (W.basis j) - inner ℝ (y - W.center) (W.basis j))) • g j := by
    rw [hxcol, hycol]
    rw [show (f W.center + ∑ j : Fin 3, col j x) -
            (f W.center + ∑ j : Fin 3, col j y)
          = (∑ j : Fin 3, col j x) - (∑ j : Fin 3, col j y) by abel]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp [col]
    rw [← sub_smul]
    apply congr_arg (fun z : ℝ => z • g j)
    ring
  calc
    inner ℝ (f x - f y) (g i)
        = inner ℝ (∑ j : Fin 3, (κ * ((W.thicknesses j : ℝ))⁻¹
            * (inner ℝ (x - W.center) (W.basis j) - inner ℝ (y - W.center) (W.basis j))) • g j)
            (g i) := by
          rw [hdiff]
    _ = ∑ j : Fin 3, (κ * ((W.thicknesses j : ℝ))⁻¹
          * (inner ℝ (x - W.center) (W.basis j) - inner ℝ (y - W.center) (W.basis j)))
          * inner ℝ (g j) (g i) := by
          rw [sum_inner]
          simp_rw [real_inner_smul_left]
    _ = κ * ((W.thicknesses i : ℝ))⁻¹
        * (inner ℝ (x - W.center) (W.basis i) - inner ℝ (y - W.center) (W.basis i)) := by
          simp_rw [g.inner_eq_ite]
          simp
    _ = κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - y) (W.basis i) := by
          rw [show inner ℝ (x - W.center) (W.basis i) - inner ℝ (y - W.center) (W.basis i)
                = inner ℝ (x - y) (W.basis i) by
              rw [← inner_sub_left]
              congr 1
              abel]

/-- **The image of the plank is a cube.**  A plank normalisation maps `W` onto the `κ × κ × κ`
box centred at `f W.center` with frame `g`: the `g i`-coordinate of `f x - f W.center` is
`(κ / W.thicknesses i) ⟪x - W.center, W.basis i⟫`, which ranges over `[-κ, κ]` exactly as `x`
ranges over `W`.  Surjectivity uses the explicit preimage
`W.center + ∑ i, (W.thicknesses i / κ) ⟪y - f W.center, g i⟫ • W.basis i`. -/
theorem image_carrier_eq_cube (ha : 0 < a) (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ} (hκ : 0 < κ)
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g) :
    f '' (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((PrismNDim.mk' (f W.center) g (fun _ => Real.toNNReal κ)).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) := by
  let Q : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
    PrismNDim.mk' (f W.center) g (fun _ => Real.toNNReal κ)
  change f '' (W.carrier : Set _) = (Q.carrier : Set _)
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast (lt_of_lt_of_le ha hab)
  have htpos : ∀ i : Fin 3, (0 : ℝ) < (W.thicknesses i : ℝ) := by
    intro i
    rw [W.thicknesses_eq]
    fin_cases i
    · exact_mod_cast ha
    · exact_mod_cast hbpos
    · norm_num
  have hκR : ((Real.toNNReal κ : ℝ≥0) : ℝ) = κ := Real.coe_toNNReal κ hκ.le
  have hQc : Q.center = f W.center := by
    simpa [Q] using PrismNDim.center_mk' (f W.center) g (fun _ => Real.toNNReal κ)
  have hQb : Q.basis = g := by
    simpa [Q] using PrismNDim.basis_mk' (f W.center) g (fun _ => Real.toNNReal κ)
  have hQt : Q.thicknesses = (fun _ => Real.toNNReal κ) := by
    simpa [Q] using PrismNDim.thicknesses_mk' (f W.center) g (fun _ => Real.toNNReal κ)
  have hvF : ∀ u : EuclideanSpace ℝ (Fin 3),
      (u -ᵥ f W.center : EuclideanSpace ℝ (Fin 3)) = u - f W.center := by
    intro u
    exact vsub_eq_sub u (f W.center)
  have hvW : ∀ u : EuclideanSpace ℝ (Fin 3),
      (u -ᵥ W.center : EuclideanSpace ℝ (Fin 3)) = u - W.center := by
    intro u
    exact vsub_eq_sub u W.center
  have hRepW : ∀ (v : EuclideanSpace ℝ (Fin 3)) (i : Fin 3),
      (W.basis.repr v) i = inner ℝ v (W.basis i) := by
    intro v i
    rw [W.basis.repr_apply_apply]
    rw [real_inner_comm]
  have hRepG : ∀ (v : EuclideanSpace ℝ (Fin 3)) (i : Fin 3),
      (g.repr v) i = inner ℝ v (g i) := by
    intro v i
    rw [g.repr_apply_apply]
    rw [real_inner_comm]
  apply Set.Subset.antisymm
  · rintro x ⟨w, hw, rfl⟩
    rw [Q.mem_carrier_iff]
    intro i
    rw [hQb, hQc, hQt]
    rw [hvF (f w)]
    rw [hRepG (f w - f W.center) i]
    rw [hκR]
    have hbnd : |inner ℝ (w - W.center) (W.basis i)| ≤ (W.thicknesses i : ℝ) := by
      have hmem := (W.mem_carrier_iff w).mp hw i
      rw [hRepW (w -ᵥ W.center) i] at hmem
      rw [hvW w] at hmem
      exact hmem
    calc
      |inner ℝ (f w - f W.center) (g i)|
          = |κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (w - W.center) (W.basis i)| := by
            congr 1
            exact inner_image_sub_basis W hnorm w W.center i
      _ = κ * ((W.thicknesses i : ℝ))⁻¹ * |inner ℝ (w - W.center) (W.basis i)| := by
            rw [abs_mul, abs_mul]
            rw [abs_of_pos hκ, abs_of_pos (inv_pos.mpr (htpos i))]
      _ ≤ κ * ((W.thicknesses i : ℝ))⁻¹ * (W.thicknesses i : ℝ) := by
            exact mul_le_mul_of_nonneg_left hbnd
              (mul_nonneg hκ.le (le_of_lt (inv_pos.mpr (htpos i))))
      _ = κ := by
            rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt (htpos i)), mul_one]
  · intro y hy
    rw [Q.mem_carrier_iff] at hy
    rw [hQb, hQc, hQt] at hy
    have hhy : ∀ i : Fin 3, |inner ℝ (y - f W.center) (g i)| ≤ κ := by
      intro i
      have hi := hy i
      rw [hvF y] at hi
      rw [hRepG (y - f W.center) i] at hi
      rw [hκR] at hi
      exact hi
    let c (j : Fin 3) : ℝ :=
      (W.thicknesses j : ℝ) * κ⁻¹ * inner ℝ (y - f W.center) (g j)
    let z : EuclideanSpace ℝ (Fin 3) := W.center + ∑ j : Fin 3, (c j) • W.basis j
    refine ⟨z, ?_, ?_⟩
    · rw [W.mem_carrier_iff]
      intro i
      rw [hRepW (z -ᵥ W.center) i]
      rw [hvW z]
      have hzc : z - W.center = ∑ j : Fin 3, (c j) • W.basis j := by
        dsimp [z]
        abel
      have hcval : inner ℝ (z - W.center) (W.basis i) = c i := by
        rw [hzc]
        rw [sum_inner]
        simp_rw [real_inner_smul_left]
        rw [Finset.sum_eq_single i]
        · rw [real_inner_self_eq_norm_sq, W.basis.norm_eq_one]
          ring
        · intro j hjm j_ne_i
          rw [W.basis.inner_eq_zero j_ne_i, mul_zero]
        · intro hj
          exact absurd (Finset.mem_univ i) hj
      rw [hcval]
      calc
        |c i| = |(W.thicknesses i : ℝ) * κ⁻¹ * inner ℝ (y - f W.center) (g i)| := by
            dsimp [c]
        _ = (W.thicknesses i : ℝ) * κ⁻¹ * |inner ℝ (y - f W.center) (g i)| := by
            rw [abs_mul, abs_mul]
            rw [abs_of_pos (htpos i), abs_of_pos (inv_pos.mpr hκ)]
        _ ≤ (W.thicknesses i : ℝ) * κ⁻¹ * κ := by
            exact mul_le_mul_of_nonneg_left (hhy i)
              (mul_nonneg (le_of_lt (htpos i)) (le_of_lt (inv_pos.mpr hκ)))
        _ = (W.thicknesses i : ℝ) := by
            rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hκ), mul_one]
    · have hzc : z - W.center = ∑ j : Fin 3, (c j) • W.basis j := by
        dsimp [z]
        abel
      have hci : ∀ j : Fin 3, inner ℝ (z - W.center) (W.basis j) = c j := by
        intro j
        rw [hzc]
        rw [sum_inner]
        simp_rw [real_inner_smul_left]
        rw [Finset.sum_eq_single j]
        · rw [real_inner_self_eq_norm_sq, W.basis.norm_eq_one]
          ring
        · intro k hkm kj_ne
          rw [W.basis.inner_eq_zero kj_ne, mul_zero]
        · intro hkm
          exact absurd (Finset.mem_univ j) hkm
      have hsy : ∑ i : Fin 3, inner ℝ (y - f W.center) (g i) • g i = y - f W.center := by
        simpa [real_inner_comm] using (g.sum_repr' (y - f W.center))
      calc
        f z = f W.center
            + ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (z - W.center) (W.basis i)) •
                g i := hnorm z
        _ = f W.center + ∑ i, (κ * ((W.thicknesses i : ℝ))⁻¹ * c i) • g i := by
            congr 1
            refine Finset.sum_congr rfl (fun i _ => ?_)
            congr 1
            rw [hci i]
        _ = f W.center + ∑ i, inner ℝ (y - f W.center) (g i) • g i := by
            congr 1
            refine Finset.sum_congr rfl (fun i _ => ?_)
            congr 1
            dsimp [c]
            field_simp [ne_of_gt (htpos i), ne_of_gt hκ]
        _ = y := by
            rw [hsy]
            abel

/-- **The contraction of a windowed normalisation obeys `3κ² ≤ 1`.**  The two opposite corners
`W.center ± (a • W.basis 0 + b • W.basis 1 + W.basis 2)` of `W` have images at distance
`2κ√3`; both lie in the unit ball, so `2κ√3 ≤ 2`.

This is the only place where the window hypothesis enters the transverse estimates, and it is what
makes the *exact* inner scales `δ/b`, `δ/a` (rather than `κ`-dependent ones) admissible. -/
theorem three_mul_sq_le_one_of_image_subset_closedBall (ha : 0 < a) (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ} (hκ : 0 < κ)
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g)
    (himg : f '' (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 1) :
    3 * κ ^ 2 ≤ 1 := by
  let t : Fin 3 → ℝ := fun i => (W.thicknesses i : ℝ)
  let dx : EuclideanSpace ℝ (Fin 3) := ∑ i : Fin 3, t i • W.basis i
  let xp : EuclideanSpace ℝ (Fin 3) := W.center + dx
  let xm : EuclideanSpace ℝ (Fin 3) := W.center - dx
  let v : EuclideanSpace ℝ (Fin 3) := f xp - f xm
  have hrepr_dx : ∀ i : Fin 3, W.basis.repr dx i = t i := by
    intro i
    calc
      W.basis.repr dx i = inner ℝ (W.basis i) dx := by rw [W.basis.repr_apply_apply]
      _ = (∑ j : Fin 3, t j * inner ℝ (W.basis i) (W.basis j)) := by
        simp [dx, inner_sum, real_inner_smul_right]
      _ = t i := by
        rw [Finset.sum_eq_single i]
        · rw [real_inner_self_eq_norm_sq, W.basis.norm_eq_one]; ring
        · intro j _ hji
          rw [W.basis.inner_eq_zero (Ne.symm hji)]; ring
        · intro h
          exact absurd (Finset.mem_univ i) h
  have hxpW : xp ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [W.mem_carrier_iff]
    intro j
    rw [show W.basis.repr (xp -ᵥ W.center) j = t j by
      rw [show xp -ᵥ W.center = dx by simp [xp]]
      exact hrepr_dx j]
    simp [t, abs_of_nonneg (NNReal.coe_nonneg (W.thicknesses j))]
  have hxmW : xm ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [W.mem_carrier_iff]
    intro j
    rw [show W.basis.repr (xm -ᵥ W.center) j = -t j by
      calc
        W.basis.repr (xm -ᵥ W.center) j = inner ℝ (W.basis j) (xm -ᵥ W.center) := by
          rw [W.basis.repr_apply_apply]
        _ = inner ℝ (W.basis j) (-dx) := by
          rw [show xm -ᵥ W.center = -dx by simp [xm]]
        _ = - inner ℝ (W.basis j) dx := by rw [inner_neg_right]
        _ = -t j := by
          rw [← W.basis.repr_apply_apply, hrepr_dx j]]
    simp [t, abs_of_nonneg (NNReal.coe_nonneg (W.thicknesses j))]
  have hxpi : ∀ i : Fin 3, inner ℝ (xp - W.center) (W.basis i) = t i := by
    intro i
    calc
      inner ℝ (xp - W.center) (W.basis i) = W.basis.repr (xp - W.center) i := by
        rw [real_inner_comm, ← W.basis.repr_apply_apply]
      _ = W.basis.repr dx i := by
        rw [show xp - W.center = dx by simp [xp]]
      _ = t i := hrepr_dx i
  have hxmi : ∀ i : Fin 3, inner ℝ (xm - W.center) (W.basis i) = -t i := by
    intro i
    calc
      inner ℝ (xm - W.center) (W.basis i) = inner ℝ (W.basis i) (xm - W.center) := by
        rw [real_inner_comm]
      _ = inner ℝ (W.basis i) (-dx) := by
        rw [show xm - W.center = -dx by simp [xm]]
      _ = - inner ℝ (W.basis i) dx := by rw [inner_neg_right]
      _ = -t i := by
        rw [← W.basis.repr_apply_apply, hrepr_dx i]
  have hv : ∀ i : Fin 3, inner ℝ v (g i) = 2 * κ := by
    intro i
    change inner ℝ (f xp - f xm) (g i) = 2 * κ
    calc
      inner ℝ (f xp - f xm) (g i)
          = κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (xp - xm) (W.basis i) := by
              exact inner_image_sub_basis W hnorm xp xm i
      _ = κ * ((W.thicknesses i : ℝ))⁻¹ * (2 * t i) := by
        congr 1
        calc
          inner ℝ (xp - xm) (W.basis i)
              = inner ℝ ((xp - W.center) - (xm - W.center)) (W.basis i) := by
                  rw [show xp - xm = (xp - W.center) - (xm - W.center) by abel]
          _ = inner ℝ (xp - W.center) (W.basis i) - inner ℝ (xm - W.center) (W.basis i) := by
              rw [inner_sub_left]
          _ = t i - (-t i) := by rw [hxpi i, hxmi i]
          _ = 2 * t i := by ring
      _ = 2 * κ := by
        dsimp [t]
        have htpos : 0 < (W.thicknesses i : ℝ) := by
          rw [W.thicknesses_eq]
          fin_cases i
          · simpa using (show (0 : ℝ) < (a : ℝ) by exact_mod_cast ha)
          · simpa using (show (0 : ℝ) < (b : ℝ) by
              exact_mod_cast (lt_of_lt_of_le ha hab))
          · norm_num
        field_simp [ne_of_gt htpos]
  have hnorm_sq : ‖v‖ ^ 2 = (∑ i : Fin 3, (inner ℝ v (g i)) ^ 2) := by
    rw [← OrthonormalBasis.sum_sq_inner_right g v]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm]
  have hnorm2 : ‖v‖ ^ 2 = 12 * κ ^ 2 := by
    rw [hnorm_sq]
    calc
      (∑ i : Fin 3, (inner ℝ v (g i)) ^ 2) = ∑ i : Fin 3, (2 * κ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hv i]
      _ = 3 * (2 * κ) ^ 2 := by
        rw [Fin.sum_univ_three]
        ring
      _ = 12 * κ ^ 2 := by ring
  have hfp : f xp ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    himg ⟨xp, hxpW, rfl⟩
  have hfm : f xm ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    himg ⟨xm, hxmW, rfl⟩
  have hfp1 : ‖f xp‖ ≤ 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hfp
    exact hfp
  have hfm1 : ‖f xm‖ ≤ 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hfm
    exact hfm
  have hnorm_le : ‖v‖ ≤ 2 := by
    calc
      ‖v‖ ≤ ‖f xp‖ + ‖f xm‖ := by simpa [v] using (norm_sub_le (f xp) (f xm))
      _ ≤ 1 + 1 := add_le_add hfp1 hfm1
      _ ≤ 2 := by norm_num
  have hsq : ‖v‖ ^ 2 ≤ 4 := by nlinarith [hnorm_le, norm_nonneg v]
  have hκsq : 12 * κ ^ 2 ≤ 4 := by
    rw [← hnorm2]
    exact hsq
  nlinarith

/-- **The Jacobian of a plank normalisation is `κ³ / (a b)`.**  Apply the volume identity to
`W.carrier`: by `Plank.image_carrier_eq_cube` the image is a `κ`-cube, of volume `8κ³`, while
`volume W.carrier = 8ab`. -/
theorem jacobian_eq (ha : 0 < a) (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ} (hκ : 0 < κ)
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g) {J : ℝ≥0}
    (hvolf : ∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E) :
    J * (a * b) = Real.toNNReal κ ^ 3 := by
  let c : ENNReal := (Real.toNNReal κ : ENNReal)
  let Q : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
    PrismNDim.mk' (f W.center) g (fun _ => Real.toNNReal κ)
  have himg : f '' (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    simpa [Q] using image_carrier_eq_cube ha W hκ hnorm
  have hvolQ : volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) = 8 * c ^ 3 := by
    rw [PrismNDim.volume_carrier, finrank_euclideanSpace_fin]
    simp [Q, PrismNDim.thicknesses_mk', c]
    ring
  have hvolW : volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = 8 * (a : ENNReal) * (b : ENNReal) := by
    simpa using Prism3D.volume_carrier W
  have hEqE : 8 * c ^ 3 = (J : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
    calc
      8 * c ^ 3 = volume (f '' (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
        rw [himg]
        exact hvolQ.symm
      _ = (J : ENNReal) * volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
        hvolf (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      _ = (J : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by rw [hvolW]
  have hEq8 : c ^ 3 * 8 = (J : ENNReal) * (a : ENNReal) * (b : ENNReal) * 8 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hEqE
  have hcancel : c ^ 3 = (J : ENNReal) * (a : ENNReal) * (b : ENNReal) := by
    have h8top : (8 : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    exact (ENNReal.mul_left_inj (by norm_num : (8 : ENNReal) ≠ 0) h8top).mp hEq8
  apply ENNReal.coe_inj.mp
  simpa [c, ENNReal.coe_mul, ENNReal.coe_pow, mul_assoc] using hcancel.symm

/-- **A plank normalisation is an affine equivalence.**  Its linear part sends the orthonormal
frame `W.basis` to the frame `g` scaled by the nonzero factors `κ / W.thicknesses i`, hence is
bijective; the affine map is that linear map composed with translations. -/
theorem exists_affineEquiv_of_isPlankNormalisation (ha : 0 < a) (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ} (hκ : 0 < κ)
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g) :
    ∃ F : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3), ∀ x, F x = f x := by
  let r : Fin 3 → ℝ := fun i => κ * ((W.thicknesses i : ℝ))⁻¹
  have hbpos : 0 < (b : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le ha hab)
  have hthick_pos : ∀ i : Fin 3, (0 : ℝ) < (W.thicknesses i : ℝ) := by
    intro i
    rw [W.thicknesses_eq]
    fin_cases i
    · exact_mod_cast ha
    · exact_mod_cast hbpos
    · norm_num
  have hr : ∀ i : Fin 3, r i ≠ 0 := by
    intro i
    dsimp [r]
    exact mul_ne_zero (ne_of_gt hκ) (inv_ne_zero (ne_of_gt (hthick_pos i)))
  -- The linear part of `f`: it rotates `W.basis` onto `g` and rescales the `i`-th
  -- coordinate by `r i = κ / W.thicknesses i`.  It is constructed as a `LinearEquiv`
  -- pairing an explicit inverse, hence bijective.
  let Lf : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (W.basis.toBasis).constr ℝ (fun i => (r i) • g i)
  let Linv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (g.toBasis).constr ℝ (fun i => (r i)⁻¹ • W.basis i)
  have h_Lf_basis : ∀ i : Fin 3, Lf (W.basis i) = (r i) • g i := by
    intro i
    simp [Lf]
  have h_Linv_basis : ∀ i : Fin 3, Linv (g i) = (r i)⁻¹ • W.basis i := by
    intro i
    simp [Linv]
  have h_sumW : ∀ v : EuclideanSpace ℝ (Fin 3),
      v = ∑ i : Fin 3, inner ℝ (W.basis i) v • W.basis i := by
    intro v
    exact (W.basis.sum_repr' v).symm
  have h_sumG : ∀ v : EuclideanSpace ℝ (Fin 3),
      v = ∑ i : Fin 3, inner ℝ (g i) v • g i := by
    intro v
    exact (g.sum_repr' v).symm
  have h_linv_lf : Linv.comp (Lf : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
      = LinearMap.id := by
    apply LinearMap.ext
    intro v
    calc
      Linv (Lf v) = Linv (Lf (∑ i : Fin 3, inner ℝ (W.basis i) v • W.basis i)) := by
        congr 2
        exact h_sumW v
      _ = ∑ i : Fin 3, inner ℝ (W.basis i) v • Linv (Lf (W.basis i)) := by
        simp [map_sum]
      _ = ∑ i : Fin 3, inner ℝ (W.basis i) v • W.basis i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hc : Linv (Lf (W.basis i)) = W.basis i := by
          simp [h_Lf_basis i, h_Linv_basis i, smul_smul, mul_inv_cancel₀ (hr i)]
        rw [hc]
      _ = v := by
        exact (W.basis.sum_repr' v)
  have h_lf_lnv : Lf.comp (Linv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
      = LinearMap.id := by
    apply LinearMap.ext
    intro v
    calc
      Lf (Linv v) = Lf (Linv (∑ i : Fin 3, inner ℝ (g i) v • g i)) := by
        congr 2
        exact h_sumG v
      _ = ∑ i : Fin 3, inner ℝ (g i) v • Lf (Linv (g i)) := by
        simp [map_sum]
      _ = ∑ i : Fin 3, inner ℝ (g i) v • g i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hc : Lf (Linv (g i)) = g i := by
          simp [h_Linv_basis i, h_Lf_basis i, smul_smul, inv_mul_cancel₀ (hr i)]
        rw [hc]
      _ = v := by
        exact (g.sum_repr' v)
  let L : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    LinearEquiv.ofLinear Lf Linv h_lf_lnv h_linv_lf
  have h_Lf_formula : ∀ v,
      Lf v = ∑ i : Fin 3, (r i * inner ℝ v (W.basis i)) • g i := by
    intro v
    calc
      Lf v = Lf (∑ i : Fin 3, inner ℝ v (W.basis i) • W.basis i) := by
        refine congrArg Lf ?_
        calc
          v = ∑ i : Fin 3, inner ℝ (W.basis i) v • W.basis i := h_sumW v
          _ = ∑ i : Fin 3, inner ℝ v (W.basis i) • W.basis i := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [real_inner_comm]
      _ = ∑ i : Fin 3, inner ℝ v (W.basis i) • Lf (W.basis i) := by
        simp [map_sum]
      _ = ∑ i : Fin 3, inner ℝ v (W.basis i) • ((r i) • g i) := by
        simp [h_Lf_basis]
      _ = ∑ i : Fin 3, (r i * inner ℝ v (W.basis i)) • g i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [smul_smul, mul_comm]
  let F : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ((AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 3)) (-W.center)).trans L.toAffineEquiv).trans
      (AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 3)) (f W.center))
  have h_F_app : ∀ z, F z = f W.center + L (z - W.center) := by
    intro z
    simp only [F, AffineEquiv.trans_apply, AffineEquiv.constVAdd_apply]
    change f W.center + L ((-W.center) + z) = f W.center + L (z - W.center)
    congr 1
    congr 1
    abel
  refine ⟨F, ?_⟩
  intro x
  calc
    F x = f W.center + L (x - W.center) := h_F_app x
    _ = f W.center + ∑ i : Fin 3, (r i * inner ℝ (x - W.center) (W.basis i)) • g i := by
      congr 1
      simpa [L] using (h_Lf_formula (x - W.center))
    _ = f x := by
      rw [hnorm x]

/-! ### The inner plank model of a normalised tube -/

/-- **A `δ`-tube is symmetric about its centre.** -/
theorem Tube.reflect_mem_carrier {δ : ℝ≥0} (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (T.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    (2 : ℝ) • T.center - x ∈ (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  rw [T.carrier_eq] at hx
  rw [T.carrier_eq]
  obtain ⟨z₀, hz₀_mem, hxz₀⟩ := Set.mem_iUnion₂.mp hx
  rw [Metric.mem_closedBall] at hxz₀
  rw [dist_eq_norm] at hxz₀
  let w : EuclideanSpace ℝ (Fin 3) := (2 : ℝ) • T.center - z₀
  have harg :
      (2 : ℝ) • T.center - x - ((2 : ℝ) • T.center - z₀) = z₀ - x := by
    abel
  have hseg : w ∈ segment ℝ T.x T.y := by
    obtain ⟨u, v, hu0, hv0, huv, hz₀_eq⟩ := hz₀_mem
    have hcenter : (2 : ℝ) • T.center = T.x + T.y := by
      change (2 : ℝ) • midpoint ℝ T.x T.y = T.x + T.y
      rw [two_smul]
      rw [midpoint_add_self]
    refine ⟨v, u, hv0, hu0, by linarith, ?_⟩
    calc
      v • T.x + u • T.y = (1 - u) • T.x + (1 - v) • T.y := by
        have h₁ : 1 - u = v := by linarith
        have h₂ : 1 - v = u := by linarith
        rw [h₁, h₂]
      _ = (T.x + T.y) - (u • T.x + v • T.y) := by
        module
      _ = (T.x + T.y) - z₀ := by rw [hz₀_eq]
      _ = (2 : ℝ) • T.center - z₀ := by rw [← hcenter]
      _ = w := rfl
  have hball : (2 : ℝ) • T.center - x ∈ Metric.closedBall w (δ : ℝ) := by
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm]
    have hnorm : ‖((2 : ℝ) • T.center - x) - w‖ = ‖x - z₀‖ := by
      dsimp [w]
      rw [harg]
      rw [norm_sub_rev]
    calc
      ‖((2 : ℝ) • T.center - x) - w‖ = ‖x - z₀‖ := hnorm
      _ ≤ (δ : ℝ) := hxz₀
  exact Set.mem_iUnion₂.mpr ⟨w, hseg, hball⟩

/-- **Coordinates of a normalisation displacement against an arbitrary direction.**  Expanding
`f x - f y` in the orthonormal frame `g` and using `Plank.inner_image_sub_basis` termwise. -/
theorem inner_image_sub_expand (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g) (x y m : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (f x - f y) m
      = ∑ i, inner ℝ m (g i)
          * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - y) (W.basis i)) := by
  calc
    inner ℝ (f x - f y) m
        = inner ℝ (∑ i : Fin 3, inner ℝ (g i) (f x - f y) • g i) m := by
          congr 1
          exact (g.sum_repr' (f x - f y)).symm
    _ = ∑ i : Fin 3, inner ℝ (g i) (f x - f y) * inner ℝ (g i) m := by
          rw [sum_inner]
          simp_rw [real_inner_smul_left]
    _ = ∑ i : Fin 3, inner ℝ (f x - f y) (g i) * inner ℝ (g i) m := by
          apply Finset.sum_congr rfl
          intro i hi
          have heq : inner ℝ (g i) (f x - f y) = inner ℝ (f x - f y) (g i) := by
            rw [real_inner_comm]
          rw [heq]
    _ = ∑ i : Fin 3,
          (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - y) (W.basis i)) * inner ℝ (g i) m := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [inner_image_sub_basis W hnorm]
    _ = ∑ i : Fin 3, inner ℝ m (g i)
          * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - y) (W.basis i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have heq : inner ℝ (g i) m = inner ℝ m (g i) := by
            rw [real_inner_comm]
          calc
            (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - y) (W.basis i)) * inner ℝ (g i) m
                = (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - y) (W.basis i))
                    * inner ℝ m (g i) := by
                  rw [heq]
            _ = inner ℝ m (g i)
                  * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - y) (W.basis i)) := by
                  ring

/-- **The thin transverse estimate.**  A direction `m` orthogonal to `g 0` sees the image of a
`δ`-ball only through the two coordinates scaled by `κ/b` and `κ`; since `b ≤ 1` and `2κ² ≤ 1`,
the total is at most `δ/b`. -/
theorem abs_inner_le_thin (ha : 0 < a) {κ : ℝ} (hκ : 0 < κ) (hκ3 : 3 * κ ^ 2 ≤ 1)
    (W : Plank a b hab hb1) {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    {m : EuclideanSpace ℝ (Fin 3)} (hm : ‖m‖ = 1) (hm0 : inner ℝ m (g 0) = 0)
    {δ : ℝ≥0} {e : EuclideanSpace ℝ (Fin 3)} (he : ‖e‖ ≤ (δ : ℝ)) :
    |∑ i, inner ℝ m (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i))|
      ≤ ((δ / b : ℝ≥0) : ℝ) := by
  let m1 : ℝ := inner ℝ m (g 1)
  let m2 : ℝ := inner ℝ m (g 2)
  let u1 : ℝ := inner ℝ e (W.basis 1)
  let u2 : ℝ := inner ℝ e (W.basis 2)
  let t1 : ℝ := m1 * (κ * ((b : ℝ)⁻¹) * u1)
  let t2 : ℝ := m2 * (κ * u2)
  have hb : 0 < (b : ℝ) := by exact_mod_cast (lt_of_lt_of_le ha hab)
  have hb1ℝ : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have hbpos : 0 ≤ (b : ℝ) := le_of_lt hb
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hb
  have hbuf : (1 : ℝ) ≤ (b : ℝ)⁻¹ := by
    rw [← mul_inv_cancel₀ hbne]
    simpa using (mul_le_mul_of_nonneg_right hb1ℝ (inv_nonneg.mpr hbpos))
  have hbInvNonneg : 0 ≤ (b : ℝ)⁻¹ := inv_nonneg.mpr hbpos
  have hδ : 0 ≤ (δ : ℝ) := δ.prop
  have hκpos : 0 ≤ κ := le_of_lt hκ
  have hie (i : Fin 3) : |inner ℝ e (W.basis i)| ≤ (δ : ℝ) := by
    calc
      |inner ℝ e (W.basis i)| ≤ ‖e‖ * ‖W.basis i‖ := abs_real_inner_le_norm e (W.basis i)
      _ = ‖e‖ := by simp
      _ ≤ (δ : ℝ) := he
  have hu1 : |u1| ≤ (δ : ℝ) := by simpa [u1] using hie 1
  have hu2 : |u2| ≤ (δ : ℝ) := by simpa [u2] using hie 2
  have hparseval : (∑ i : Fin 3, (inner ℝ m (g i)) ^ 2) = 1 := by
    have h := g.sum_sq_norm_inner_right m
    rw [hm] at h
    simpa [pow_two, sq_abs, real_inner_comm] using h
  have hmm : m1 ^ 2 + m2 ^ 2 = 1 := by
    rw [Fin.sum_univ_three] at hparseval
    simpa [m1, m2, hm0, pow_two] using hparseval
  have hs_le : (|m1| + |m2|) ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg (|m1| - |m2|), sq_abs m1, sq_abs m2, hmm, abs_nonneg m1, abs_nonneg m2]
  have h2κsq : 2 * κ ^ 2 ≤ 1 := by nlinarith [hκ3]
  have hkSsq : (κ * (|m1| + |m2|)) ^ 2 ≤ 1 := by
    nlinarith [hs_le, h2κsq]
  have hkS : κ * (|m1| + |m2|) ≤ 1 := by
    simpa [Real.sqrt_one] using (Real.le_sqrt_of_sq_le hkSsq)
  have hsum_expr : (∑ i, inner ℝ m (g i)
        * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i))) = t1 + t2 := by
    rw [Fin.sum_univ_three]
    rw [W.thicknesses_eq]
    simp [t1, t2, m1, m2, u1, u2, hm0]
  have hscale1 : |κ * ((b : ℝ)⁻¹) * u1| ≤ κ * ((b : ℝ)⁻¹) * (δ : ℝ) := by
    calc
      |κ * ((b : ℝ)⁻¹) * u1| = (κ * ((b : ℝ)⁻¹)) * |u1| := by
        rw [abs_mul, abs_mul]
        rw [abs_of_pos hκ, abs_of_pos (inv_pos.mpr hb)]
      _ ≤ (κ * ((b : ℝ)⁻¹)) * (δ : ℝ) := by
        exact mul_le_mul_of_nonneg_left hu1 (mul_nonneg hκpos hbInvNonneg)
  have hbnd1 : |m1 * (κ * ((b : ℝ)⁻¹) * u1)| ≤ |m1| * (κ * ((b : ℝ)⁻¹) * (δ : ℝ)) := by
    simpa [abs_mul] using (mul_le_mul_of_nonneg_left hscale1 (abs_nonneg m1))
  have hle1 : |t1| ≤ κ * |m1| * ((b : ℝ)⁻¹) * (δ : ℝ) := by
    calc
      |t1| = |m1 * (κ * ((b : ℝ)⁻¹) * u1)| := by rfl
      _ ≤ |m1| * (κ * ((b : ℝ)⁻¹) * (δ : ℝ)) := hbnd1
      _ = κ * |m1| * ((b : ℝ)⁻¹) * (δ : ℝ) := by ring
  have hscale2 : |κ * u2| ≤ κ * (δ : ℝ) := by
    calc
      |κ * u2| = κ * |u2| := by rw [abs_mul, abs_of_pos hκ]
      _ ≤ κ * (δ : ℝ) := mul_le_mul_of_nonneg_left hu2 hκpos
  have hbnd2 : |m2 * (κ * u2)| ≤ |m2| * (κ * (δ : ℝ)) := by
    calc
      |m2 * (κ * u2)| ≤ |m2| * |κ * u2| := by rw [abs_mul]
      _ ≤ |m2| * (κ * (δ : ℝ)) := mul_le_mul_of_nonneg_left hscale2 (abs_nonneg m2)
  have hle2 : |t2| ≤ κ * |m2| * (δ : ℝ) := by
    calc
      |t2| = |m2 * (κ * u2)| := by rfl
      _ ≤ |m2| * (κ * (δ : ℝ)) := hbnd2
      _ = κ * |m2| * (δ : ℝ) := by ring
  have hleAdd : |t1 + t2| ≤ κ * |m1| * ((b : ℝ)⁻¹) * (δ : ℝ) + κ * |m2| * (δ : ℝ) := by
    calc
      |t1 + t2| ≤ |t1| + |t2| := by
        rw [abs_le]
        constructor
        · have hn1 : -|t1| ≤ t1 := by
            have h : -(t1) ≤ |t1| := by simpa using (le_abs_self (-t1))
            simpa using (neg_le_neg h)
          have hn2 : -|t2| ≤ t2 := by
            have h : -(t2) ≤ |t2| := by simpa using (le_abs_self (-t2))
            simpa using (neg_le_neg h)
          linarith
        · nlinarith [le_abs_self t1, le_abs_self t2]
      _ ≤ κ * |m1| * ((b : ℝ)⁻¹) * (δ : ℝ) + κ * |m2| * (δ : ℝ) := add_le_add hle1 hle2
  have hbb : (b : ℝ) * (b : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hbne
  have hm2b : κ * |m2| * (b : ℝ) ≤ κ * |m2| := by
    have hx : 0 ≤ κ * |m2| := mul_nonneg hκpos (abs_nonneg m2)
    simpa using (mul_le_mul_of_nonneg_left hb1ℝ hx)
  have hbell : κ * |m1| + κ * |m2| * (b : ℝ) ≤ 1 := by
    nlinarith [hkS, hm2b]
  have hfac : (δ : ℝ) * (b : ℝ)⁻¹ * (κ * |m1| + κ * |m2| * (b : ℝ))
      = κ * |m1| * (b : ℝ)⁻¹ * (δ : ℝ) + κ * |m2| * (δ : ℝ) := by
    field_simp [hbne]
  have hR : κ * |m1| * ((b : ℝ)⁻¹) * (δ : ℝ) + κ * |m2| * (δ : ℝ) ≤ (δ : ℝ) * (b : ℝ)⁻¹ := by
    calc
      κ * |m1| * ((b : ℝ)⁻¹) * (δ : ℝ) + κ * |m2| * (δ : ℝ)
          = (δ : ℝ) * (b : ℝ)⁻¹ * (κ * |m1| + κ * |m2| * (b : ℝ)) := hfac.symm
      _ ≤ (δ : ℝ) * (b : ℝ)⁻¹ := by
          simpa using (mul_le_mul_of_nonneg_left hbell (mul_nonneg hδ hbInvNonneg))
  rw [hsum_expr, NNReal.coe_div, div_eq_mul_inv]
  exact le_trans hleAdd hR

/-- **The middle transverse estimate.**  For an arbitrary unit direction the largest scaling `κ/a`
dominates all three coordinates, and `3κ² ≤ 1` turns the resulting `√3 κ δ / a` into `δ/a`. -/
theorem abs_inner_le_mid (ha : 0 < a) {κ : ℝ} (hκ : 0 < κ) (hκ3 : 3 * κ ^ 2 ≤ 1)
    (W : Plank a b hab hb1) {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    {m : EuclideanSpace ℝ (Fin 3)} (hm : ‖m‖ = 1)
    {δ : ℝ≥0} {e : EuclideanSpace ℝ (Fin 3)} (he : ‖e‖ ≤ (δ : ℝ)) :
    |∑ i, inner ℝ m (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i))|
      ≤ ((δ / a : ℝ≥0) : ℝ) := by
  rw [NNReal.coe_div]
  -- scalar facts
  have hap : (a : ℝ) > 0 := by exact_mod_cast ha
  have hap' : 0 ≤ (a : ℝ) := le_of_lt hap
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hb1' : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have ha1 : (a : ℝ) ≤ 1 := le_trans hab' hb1'
  have hδ0 : 0 ≤ (δ : ℝ) := (δ : ℝ≥0).coe_nonneg
  -- the coordinates of m in frame g
  let m0 : ℝ := inner ℝ m (g 0)
  let m1 : ℝ := inner ℝ m (g 1)
  let m2 : ℝ := inner ℝ m (g 2)
  let S : ℝ := |m0| + |m1| + |m2|
  have hS0 : 0 ≤ S := by
    dsimp [S]
    positivity
  -- thicknesses are positive (for the inv sign)
  have hthick_pos : ∀ i : Fin 3, (0 : ℝ) < (W.thicknesses i : ℝ) := by
    intro i
    rw [W.thicknesses_eq]
    fin_cases i
    · exact_mod_cast ha
    · exact_mod_cast (lt_of_lt_of_le ha hab)
    · norm_num
  -- for every i, |⟪e, W.basis i⟫| ≤ δ
  have hge : ∀ i : Fin 3, |inner ℝ e (W.basis i)| ≤ (δ : ℝ) := by
    intro i
    calc
      |inner ℝ e (W.basis i)| ≤ ‖e‖ * ‖W.basis i‖ := abs_real_inner_le_norm _ _
      _ = ‖e‖ := by rw [W.basis.norm_eq_one i, mul_one]
      _ ≤ (δ : ℝ) := he
  -- every thickness⁻¹ is at most a⁻¹  (a ≤ b ≤ 1)
  have hge_thick : ∀ i : Fin 3, (a : ℝ) ≤ (W.thicknesses i : ℝ) := by
    intro i
    rw [W.thicknesses_eq]
    fin_cases i
    · simp
    · simpa using hab'
    · simpa using ha1
  have hinv : ∀ i : Fin 3, ((W.thicknesses i : ℝ))⁻¹ ≤ (a : ℝ)⁻¹ := by
    intro i
    exact (inv_le_inv₀ (hthick_pos i) hap).mpr (hge_thick i)
  -- termwise bound: a term ≤ κ · |mᵢ| · thickness⁻¹ · δ
  have hterm : ∀ i : Fin 3,
      |inner ℝ m (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i))|
        ≤ κ * |inner ℝ m (g i)| * ((W.thicknesses i : ℝ))⁻¹ * (δ : ℝ) := by
    intro i
    calc
      |inner ℝ m (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i))|
          = |inner ℝ m (g i)| * |κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i)| := by
            rw [abs_mul]
      _ ≤ |inner ℝ m (g i)| * (κ * ((W.thicknesses i : ℝ))⁻¹ * (δ : ℝ)) := by
            have hsub :
                |κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i)|
                  ≤ κ * ((W.thicknesses i : ℝ))⁻¹ * (δ : ℝ) := by
              calc
                |κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i)|
                    = κ * ((W.thicknesses i : ℝ))⁻¹ * |inner ℝ e (W.basis i)| := by
                      rw [abs_mul, abs_mul, abs_of_pos hκ,
                        abs_of_pos (inv_pos.mpr (hthick_pos i))]
                _ ≤ κ * ((W.thicknesses i : ℝ))⁻¹ * (δ : ℝ) := by
                      gcongr
                      exact hge i
            exact mul_le_mul_of_nonneg_left hsub (abs_nonneg _)
      _ = κ * |inner ℝ m (g i)| * ((W.thicknesses i : ℝ))⁻¹ * (δ : ℝ) := by ring
  -- the sum is at most κ · a⁻¹ · δ · (|m₀| + |m₁| + |m₂|)
  have hsum : |∑ i, inner ℝ m (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i))|
      ≤ κ * (a : ℝ)⁻¹ * (δ : ℝ) * S := by
    calc
      |∑ i, inner ℝ m (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i))|
          ≤ ∑ i, κ * |inner ℝ m (g i)| * ((W.thicknesses i : ℝ))⁻¹ * (δ : ℝ) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
            intro i _
            exact hterm i
      _ ≤ ∑ i, κ * |inner ℝ m (g i)| * (a : ℝ)⁻¹ * (δ : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro i _
            have hmc : 0 ≤ κ * |inner ℝ m (g i)| := mul_nonneg (le_of_lt hκ) (abs_nonneg _)
            simpa [mul_assoc] using (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (hinv i) hδ0) hmc)
      _ = κ * (a : ℝ)⁻¹ * (δ : ℝ) * S := by
            rw [Fin.sum_univ_three]
            dsimp [S, m0, m1, m2]
            ring
  -- the sum-of-squares identity: m₀² + m₁² + m₂² = ‖m‖² = 1
  have hsumsq : m0 ^ 2 + m1 ^ 2 + m2 ^ 2 = 1 := by
    have hiso : ‖g.repr m‖ = 1 := by
      rw [LinearIsometryEquiv.norm_map, hm]
    have hcoord : ∀ i : Fin 3, inner ℝ m (g i) = (g.repr m : EuclideanSpace ℝ (Fin 3)) i := by
      intro i
      rw [real_inner_comm]
      rw [g.repr_apply_apply]
    calc
      m0 ^ 2 + m1 ^ 2 + m2 ^ 2
          = ∑ i : Fin 3, (inner ℝ m (g i)) ^ 2 := by
            dsimp [m0, m1, m2]
            rw [Fin.sum_univ_three]
      _ = ∑ i : Fin 3, ((g.repr m : EuclideanSpace ℝ (Fin 3)) i) ^ 2 := by
            simp_rw [hcoord]
      _ = ‖g.repr m‖ ^ 2 := by
            simpa using (EuclideanSpace.real_norm_sq_eq (g.repr m)).symm
      _ = 1 := by
            rw [hiso]
            norm_num
  -- S² ≤ 3
  have hSsq : S ^ 2 ≤ 3 := by
    have hle : S ^ 2 ≤ 3 * (m0 ^ 2 + m1 ^ 2 + m2 ^ 2) := by
      dsimp [S]
      nlinarith [sq_nonneg (|m0| - |m1|), sq_nonneg (|m1| - |m2|), sq_nonneg (|m2| - |m0|),
        (sq_abs m0).symm, (sq_abs m1).symm, (sq_abs m2).symm]
    nlinarith [hle, hsumsq]
  -- κ · S ≤ 1  (via squaring)
  have hκS : κ * S ≤ 1 := by
    have h0 : (κ * S) ^ 2 ≤ 1 := by
      rw [mul_pow]
      have h1 : κ ^ 2 * S ^ 2 ≤ κ ^ 2 * 3 := mul_le_mul_of_nonneg_left hSsq (sq_nonneg κ)
      nlinarith
    have hbig : (κ * S) ^ 2 ≤ (1 : ℝ) ^ 2 := by simpa using h0
    exact (sq_le_sq₀ (mul_nonneg (le_of_lt hκ) hS0) (by norm_num : (0 : ℝ) ≤ 1)).mp hbig
  -- finish
  calc
    |∑ i, inner ℝ m (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i))|
        ≤ κ * (a : ℝ)⁻¹ * (δ : ℝ) * S := hsum
    _ = (κ * S) * ((a : ℝ)⁻¹ * (δ : ℝ)) := by ring
    _ ≤ (δ : ℝ) * (a : ℝ)⁻¹ := by
          have hM : 0 ≤ (a : ℝ)⁻¹ * (δ : ℝ) := mul_nonneg (inv_nonneg.mpr hap') hδ0
          calc
            (κ * S) * ((a : ℝ)⁻¹ * (δ : ℝ)) ≤ 1 * ((a : ℝ)⁻¹ * (δ : ℝ)) :=
              mul_le_mul_of_nonneg_right hκS hM
            _ = (δ : ℝ) * (a : ℝ)⁻¹ := by ring
    _ = (δ : ℝ) / (a : ℝ) := by rw [div_eq_mul_inv]

/-- **The longitudinal estimate, from symmetry alone.**  A `δ`-tube is symmetric about its centre,
so the image of a tube inside a windowed plank stays within distance `1` of the image of the tube
centre — no bound on the linear part of the normalisation is needed. -/
theorem norm_image_sub_tubeCenter_le (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)}
    (himg : f '' (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 1)
    {δ : ℝ≥0} (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hT : (T.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (T.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    ‖f x - f T.center‖ ≤ 1 := by
  let x' : EuclideanSpace ℝ (Fin 3) := (2 : ℝ) • T.center - x
  have hxT' : x' ∈ (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    simpa [x'] using (Tube.reflect_mem_carrier T hx)
  have hxW : x ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := hT hx
  have hxW' : x' ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := hT hxT'
  have hfx : f x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := himg ⟨x, hxW, rfl⟩
  have hfx' : f x' ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := himg ⟨x', hxW', rfl⟩
  have hnormx : ‖f x‖ ≤ 1 := by
    have hd := (Metric.mem_closedBall).mp hfx
    simpa [dist_eq_norm] using hd
  have hnormx' : ‖f x'‖ ≤ 1 := by
    have hd := (Metric.mem_closedBall).mp hfx'
    simpa [dist_eq_norm] using hd
  have hxx : x + x' = (2 : ℝ) • T.center := by
    dsimp [x']
    abel
  have hmm : midpoint ℝ x x' = T.center := by
    rw [midpoint_eq_smul_add, hxx, smul_smul]
    simp
  have hfmid : f T.center = midpoint ℝ (f x) (f x') := by
    simpa [hmm] using (AffineMap.map_midpoint f x x')
  have hsub : f x - f T.center = (⅟2 : ℝ) • (f x - f x') := by
    rw [hfmid]
    exact left_sub_midpoint (f x) (f x')
  have hnorm : ‖(⅟2 : ℝ) • (f x - f x')‖ = ‖f x - f x'‖ / 2 := by
    rw [norm_smul]
    simp
    ring
  have hsum : (‖f x‖ + ‖f x'‖) / 2 ≤ 1 := by
    nlinarith [hnormx, hnormx']
  calc
    ‖f x - f T.center‖ = ‖(⅟2 : ℝ) • (f x - f x')‖ := by rw [hsub]
    _ = ‖f x - f x'‖ / 2 := hnorm
    _ ≤ (‖f x‖ + ‖f x'‖) / 2 := by
      have hsubn : ‖f x - f x'‖ ≤ ‖f x‖ + ‖f x'‖ := norm_sub_le (f x) (f x')
      linarith
    _ ≤ 1 := hsum

/-- **A plank centred in the unit ball lies in the working window.**  Its half-widths are at most
`1`, so its carrier lies within `√3 ≤ 3` of its centre. -/
theorem carrier_subset_window {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
    (P : Plank a' b' ha'b' hb'1) (hcen : ‖P.center‖ ≤ 1) :
    (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ) := by
  intro y hy
  have hmem := (P.mem_carrier_iff y).1 hy
  have hthick_le_one : ∀ j : Fin 3, (P.thicknesses j : ℝ) ≤ 1 := by
    intro j
    rw [P.thicknesses_eq]
    fin_cases j
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
        Matrix.cons_val_zero, NNReal.coe_le_one]
      exact_mod_cast (le_trans ha'b' hb'1)
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_one, Matrix.cons_val_zero, NNReal.coe_le_one]
      exact_mod_cast hb'1
    · norm_num
  have hcoord : ∀ j : Fin 3, |P.basis.repr (y -ᵥ P.center) j| ≤ (1 : ℝ) := fun j =>
    le_trans (hmem j) (hthick_le_one j)
  have hnorm : ‖y - P.center‖ ^ 2 ≤ 3 := by
    calc
      ‖y - P.center‖ ^ 2 = ‖y -ᵥ P.center‖ ^ 2 := by rw [vsub_eq_sub]
      _ = ‖P.basis.repr (y -ᵥ P.center)‖ ^ 2 := by
        exact congrArg (fun z : ℝ => z ^ 2)
          (LinearIsometryEquiv.norm_map (P.basis.repr) (y -ᵥ P.center)).symm
      _ = ∑ j : Fin 3, (P.basis.repr (y -ᵥ P.center) j) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq (P.basis.repr (y -ᵥ P.center))
      _ ≤ 3 := by
        calc
          ∑ j : Fin 3, (P.basis.repr (y -ᵥ P.center) j) ^ 2 ≤ ∑ j : Fin 3, (1 : ℝ) := by
            exact Finset.sum_le_sum fun j _ => by
              have hc2 : (P.basis.repr (y -ᵥ P.center) j) ^ 2 ≤ (1 : ℝ) := by
                rw [← sq_abs (P.basis.repr (y -ᵥ P.center) j)]
                nlinarith [hcoord j, abs_nonneg (P.basis.repr (y -ᵥ P.center) j)]
              exact hc2
          _ = 3 := by norm_num [Fin.sum_univ_three]
  have hnonneg : 0 ≤ ‖y - P.center‖ := norm_nonneg _
  have hdist : ‖y - P.center‖ ≤ 3 := by nlinarith
  have htri : ‖y‖ ≤ ‖y - P.center‖ + ‖P.center‖ := by
    calc
      ‖y‖ = ‖(y - P.center) + P.center‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - P.center‖ + ‖P.center‖ := norm_add_le _ _
  have hnorm_y : ‖y‖ ≤ 4 := by
    calc
      ‖y‖ ≤ ‖y - P.center‖ + ‖P.center‖ := htri
      _ ≤ 3 + 1 := add_le_add hdist hcen
      _ = 4 := by norm_num
  rw [Metric.mem_closedBall]
  rw [dist_eq_norm]
  rw [sub_zero]
  have h4 : ((plankWindowRadius : ℝ≥0) : ℝ) = 4 := by norm_num [plankWindowRadius]
  exact le_trans hnorm_y (le_of_eq h4.symm)

/-- **Axis-plus-transverse decomposition of a normalised tube point.**  A point of a `δ`-tube is an
axis point plus a vector of norm at most `δ`, and the axis point is `s • (T.y - T.x)` away from the
centre with `|s| ≤ 1/2`.  Testing the image displacement against any direction therefore splits into
an axis term, proportional to `f T.y - f T.x`, and a transverse term of the shape estimated by
`Plank.abs_inner_le_thin` and `Plank.abs_inner_le_mid`. -/
theorem exists_axis_decomposition_of_mem_tube (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g)
    {δ : ℝ≥0} (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (T.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    ∃ (s : ℝ) (e : EuclideanSpace ℝ (Fin 3)), |s| ≤ 1 / 2 ∧ ‖e‖ ≤ (δ : ℝ) ∧
      ∀ m : EuclideanSpace ℝ (Fin 3),
        inner ℝ (f x - f T.center) m
          = s * inner ℝ (f T.y - f T.x) m
            + ∑ i, inner ℝ m (g i)
                * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i)) := by
  rw [T.carrier_eq] at hx
  obtain ⟨z, hz_seg, hz⟩ := Set.mem_iUnion₂.mp hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  obtain ⟨u, v, hu0, hv0, huv, hz_eq⟩ := hz_seg
  let s : ℝ := v - 1 / 2
  let e : EuclideanSpace ℝ (Fin 3) := x - z
  have hcen : T.center = (1 / 2 : ℝ) • (T.x + T.y) := by
    change midpoint ℝ T.x T.y = (1 / 2 : ℝ) • (T.x + T.y)
    simpa using (midpoint_eq_smul_add ℝ T.x T.y)
  have hscalar : ∀ i : Fin 3, inner ℝ (x - T.center) (W.basis i)
      = s * inner ℝ (T.y - T.x) (W.basis i) + inner ℝ e (W.basis i) := by
    intro i
    dsimp [s, e]
    rw [hcen]
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
    rw [hz_eq.symm]
    simp only [real_inner_smul_left, inner_add_left]
    have hv : v = 1 - u := by linarith
    rw [hv]
    ring
  refine ⟨s, e, ?_, ?_, ?_⟩
  · dsimp [s]
    rw [abs_le]
    constructor <;> linarith
  · dsimp [e]
    exact hz
  · intro m
    have hL := inner_image_sub_expand W hnorm x T.center m
    have hR := inner_image_sub_expand W hnorm T.y T.x m
    calc
      inner ℝ (f x - f T.center) m
          = ∑ i, inner ℝ m (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (x - T.center) (W.basis i)) := hL
      _ = ∑ i, inner ℝ m (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹
            * (s * inner ℝ (T.y - T.x) (W.basis i) + inner ℝ e (W.basis i))) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [hscalar i]
      _ = ∑ i, (s * (inner ℝ m (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (T.y - T.x) (W.basis i)))
            + inner ℝ m (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i))) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            ring
      _ = s * (∑ i, inner ℝ m (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (T.y - T.x) (W.basis i)))
            + ∑ i, inner ℝ m (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i)) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      _ = s * inner ℝ (f T.y - f T.x) m
            + ∑ i, inner ℝ m (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i)) := by
            rw [hR.symm]

/-- **The inner plank model of a fine tube** (`lem:geometryTubeFamilyInsidePlankNormalisation`,
containment half).

Under the plank normalisation `f` of the `a × b × 1` plank `W`, a fine `δ`-tube `T ⊆ W` has its
image contained in a plank of the *exact* dimensions `(δ/b) × (δ/a) × 1` whose thin normal is
orthogonal to `g 0`, and that plank lies in the working window `closedBall 0 4`.

See the module docstring for the construction and the three independent estimates. -/
theorem exists_normalisedTubePlank {δ : ℝ≥0} (ha : 0 < a) (hδ0 : 0 < δ) (hδa : δ ≤ a)
    (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ} (hκ : 0 < κ)
    (hκ3 : 3 * κ ^ 2 ≤ 1)
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g)
    (himg : f '' (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 1)
    (ha'b' : δ / b ≤ δ / a) (hb'1 : δ / a ≤ 1)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hT : (T.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    ∃ P : Plank (δ / b) (δ / a) ha'b' hb'1,
      inner ℝ (P.basis 0) (g 0) = 0 ∧
      P.basis 2 = (‖f T.y - f T.x‖)⁻¹ • (f T.y - f T.x) ∧
      f '' (T.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∧
      (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ) := by
  classical
  -- scalar ℝ facts
  have hap : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbp : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (lt_of_lt_of_le ha hab)
  have hδr_pos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hthick_pos : ∀ i : Fin 3, (0 : ℝ) < (W.thicknesses i : ℝ) := by
    intro i
    rw [W.thicknesses_eq]
    fin_cases i <;> simp [hap, hbp, show (0 : ℝ) < (1 : ℝ) by norm_num]
  have hthick_ne : ∀ i : Fin 3, (W.thicknesses i : ℝ) ≠ 0 := by
    intro i
    exact ne_of_gt (hthick_pos i)
  -- the tube centre lies in the carrier
  have hTc_mem : T.center ∈ (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr ⟨T.center, midpoint_mem_segment (𝕜 := ℝ) T.x T.y,
      Metric.mem_closedBall_self (le_of_lt hδr_pos)⟩
  -- the normalised image of the tube axis is nonzero
  let d : EuclideanSpace ℝ (Fin 3) := f T.y - f T.x
  have hdir_nonzero : T.y - T.x ≠ 0 := by
    intro hu
    have h01 : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) = ‖T.direction‖ := T.norm_direction.symm
        _ = ‖(0 : EuclideanSpace ℝ (Fin 3))‖ := by
          change ‖T.y - T.x‖ = ‖(0 : EuclideanSpace ℝ (Fin 3))‖
          rw [hu]
        _ = 0 := by norm_num
    norm_num at h01
  have hd_ne : d ≠ 0 := by
    intro hd0
    apply hdir_nonzero
    calc
      T.y - T.x = ∑ i : Fin 3, W.basis.repr (T.y - T.x) i • W.basis i :=
        (W.basis.sum_repr _).symm
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hco : inner ℝ (T.y - T.x) (W.basis i) = 0 := by
          have hj := Plank.inner_image_sub_basis W hnorm T.y T.x i
          have hz : κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (T.y - T.x) (W.basis i) = 0 := by
            rw [← hj]
            simp [d, hd0]
          exact (mul_eq_zero.mp hz).resolve_left
            (mul_ne_zero (ne_of_gt hκ) (inv_ne_zero (hthick_ne i)))
        -- W.basis.repr (T.y - T.x) i = inner ℝ (W.basis i) (T.y - T.x)
        rw [W.basis.repr_apply_apply, real_inner_comm, hco]
        simp
  let ŵ : EuclideanSpace ℝ (Fin 3) := (‖d‖⁻¹) • d
  have hŵ_norm : ‖ŵ‖ = 1 := by
    rw [show ‖ŵ‖ = ‖(‖d‖⁻¹) • d‖ by rfl]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg d))]
    rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hd_ne)]
  obtain ⟨n, hnN, hnŵ, hng0⟩ := exists_unit_orthogonal_pair ŵ (g 0)
  obtain ⟨B, hB0, hB2⟩ := exists_orthonormalBasis_fst_thd_eq hnN hŵ_norm hnŵ
  -- check orthogonality of B to d in the first two slots
  have hdw : d = ‖d‖ • ŵ := by
    dsimp [ŵ]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hd_ne), one_smul]
  have hŵ_B : ∀ j : Fin 3, j ≠ 2 → inner ℝ ŵ (B j) = 0 := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      rw [hB0]
      rw [real_inner_comm]
      exact hnŵ
    · have hj1 : j = 1 := by
        fin_cases j
        · exfalso
          exact hj0 rfl
        · rfl
        · exfalso
          exact hj rfl
      subst j
      rw [show inner ℝ ŵ (B 1) = inner ℝ (B 2) (B 1) by rw [hB2]]
      exact B.inner_eq_zero (show (2 : Fin 3) ≠ 1 by decide)
  have hd_B : ∀ j : Fin 3, j ≠ 2 → inner ℝ d (B j) = 0 := by
    intro j hj
    rw [hdw, inner_smul_left]
    rw [hŵ_B j hj]
    ring
  -- the model plank
  let P : Plank (δ / b) (δ / a) ha'b' hb'1 :=
    { toPrismNDim := PrismNDim.mk' (f T.center) B ![δ / b, δ / a, 1]
      thicknesses_eq := rfl }
  have hP_basis : P.basis = B := by
    dsimp [P]
    exact PrismNDim.basis_mk' (f T.center) B ![δ / b, δ / a, 1]
  have hP_center : P.center = f T.center := by
    dsimp [P]
    exact PrismNDim.center_mk' (f T.center) B ![δ / b, δ / a, 1]
  have hP_thick : P.thicknesses = ![δ / b, δ / a, 1] := by
    dsimp [P]
    exact PrismNDim.thicknesses_mk' (f T.center) B ![δ / b, δ / a, 1]
  have hortho : inner ℝ (P.basis 0) (g 0) = 0 := by
    rw [hP_basis, hB0]
    exact hng0
  have hsubset : f '' (T.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rintro y ⟨x, hx, rfl⟩
    rw [P.mem_carrier_iff]
    intro j
    rw [hP_basis, hP_center]
    have hvsub : (f x -ᵥ f T.center : EuclideanSpace ℝ (Fin 3)) = f x - f T.center :=
      vsub_eq_sub (f x) (f T.center)
    rw [hvsub, B.repr_apply_apply, real_inner_comm]
    rcases (exists_axis_decomposition_of_mem_tube W hnorm T hx) with ⟨s, e, hsb, he, hdecomp⟩
    fin_cases j
    · -- j = 0, thickness δ/b
      rw [hP_thick]
      have horth : inner ℝ (B 0) (g 0) = 0 := by
        rw [hB0]
        exact hng0
      have hax : s * inner ℝ (f T.y - f T.x) (B 0) = 0 := by
        change s * inner ℝ d (B 0) = 0
        simp [hd_B 0 (by decide : (0 : Fin 3) ≠ 2)]
      have heqw : inner ℝ (f x - f T.center) (B 0)
          = ∑ i, inner ℝ (B 0) (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i)) := by
        rw [hdecomp (B 0)]
        rw [hax]
        simp
      calc
        |inner ℝ (f x - f T.center) (B 0)|
            = |∑ i, inner ℝ (B 0) (g i)
                * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i))| := by
                rw [heqw]
        _ ≤ ((δ / b : ℝ≥0) : ℝ) := by
                simpa [Matrix.cons_val_zero] using
                  (abs_inner_le_thin ha hκ hκ3 W (m := B 0) (B.norm_eq_one 0) horth (e := e) he)
    · -- j = 1, thickness δ/a
      rw [hP_thick]
      have hax : s * inner ℝ (f T.y - f T.x) (B 1) = 0 := by
        change s * inner ℝ d (B 1) = 0
        simp [hd_B 1 (by decide : (1 : Fin 3) ≠ 2)]
      have heqw : inner ℝ (f x - f T.center) (B 1)
          = ∑ i, inner ℝ (B 1) (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i)) := by
        rw [hdecomp (B 1)]
        rw [hax]
        simp
      calc
        |inner ℝ (f x - f T.center) (B 1)|
            = |∑ i, inner ℝ (B 1) (g i)
                * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i))| := by
                rw [heqw]
        _ ≤ ((δ / a : ℝ≥0) : ℝ) := by
                simpa [Matrix.cons_val_one] using
                  (abs_inner_le_mid ha hκ hκ3 W (m := B 1) (B.norm_eq_one 1) (e := e) he)
    · -- j = 2, thickness 1
      rw [hP_thick]
      calc
        |inner ℝ (f x - f T.center) (B 2)| ≤ ‖f x - f T.center‖ * ‖B 2‖ :=
          abs_real_inner_le_norm (f x - f T.center) (B 2)
        _ = ‖f x - f T.center‖ := by rw [B.norm_eq_one 2, mul_one]
        _ ≤ (1 : ℝ) := norm_image_sub_tubeCenter_le W himg T hT hx
  have hwin : (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ) := by
    refine carrier_subset_window P ?hcen
    have hTcW : T.center ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := hT hTc_mem
    have hfc : f T.center ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
      himg ⟨T.center, hTcW, rfl⟩
    have hlen : ‖f T.center‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hfc
      exact hfc
    simpa [hP_center] using hlen
  have halign : P.basis 2 = (‖f T.y - f T.x‖)⁻¹ • (f T.y - f T.x) := by
    rw [hP_basis]
    exact hB2
  exact ⟨P, hortho, halign, hsubset, hwin⟩

/-! ### Tangency and density transfer -/

/-- **The tangency bound consumed by S6G18.**  If the thin normal of a plank `P` is orthogonal to
a unit vector `e` and a slab `S` makes plane angle at most `θ ≤ 1` with `P`, then `S`'s own thin
normal is nearly orthogonal to `e`: `|⟪S.basis 0, e⟫| ≤ θ`.

Indeed `|⟪P.basis 0, S.basis 0⟫| = cos (angle P S) ≥ cos θ`, and writing `S.basis 0` as its
component along `P.basis 0` plus a remainder of norm `√(1 - cos²) ≤ sin θ ≤ θ`, only the remainder
pairs with `e`. -/
theorem abs_inner_slabNormal_le_of_angle {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
    (P : Plank a' b' ha'b' hb'1) {e : EuclideanSpace ℝ (Fin 3)} (he : ‖e‖ = 1)
    (hPe : inner ℝ (P.basis 0) e = 0)
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (hang : Prism3D.angle P S ≤ (θ : ℝ)) :
    |inner ℝ (S.basis 0) e| ≤ (θ : ℝ) := by
  let n : EuclideanSpace ℝ (Fin 3) := P.basis 0
  let mm : EuclideanSpace ℝ (Fin 3) := S.basis 0
  let c : ℝ := inner ℝ n mm
  have hn : ‖n‖ = 1 := by simp [n]
  have hmm : ‖mm‖ = 1 := by simp [mm]
  have htheta0 : 0 ≤ (θ : ℝ) := NNReal.coe_nonneg θ
  have hθ1' : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ1
  -- `1 ≤ π` (avoiding the `Mathlib.Analysis.Real.Pi.Bounds` module, which is not
  -- reachable from this module's `public import` chain): `sin (π/2) = 1` and `sin x ≤ x`.
  have hpi_ge_one : (1 : ℝ) ≤ Real.pi := by
    have hsin_le_pi2 : Real.sin (Real.pi / 2) ≤ Real.pi / 2 :=
      Real.sin_le (show 0 ≤ Real.pi / 2 by linarith [Real.pi_pos])
    have hsin_pi2 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    have h1le_pi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith
    have hpi2_le_pi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
    linarith
  have hθ1π : (θ : ℝ) ≤ Real.pi := by linarith [hθ1', hpi_ge_one]
  -- Step 1: cos θ ≤ |c|
  have hcosc : Real.cos (θ : ℝ) ≤ |c| := by
    change Real.cos (θ : ℝ) ≤ |inner ℝ (P.basis 0) (S.basis 0)|
    rw [← Prism3D.cos_angle P S]
    refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ ?_ ?_
    · exact Prism3D.angle_nonneg P S
    · exact hθ1π
    · exact hang
  -- cos θ ≥ 0 since 1 - θ²/2 ≤ cos θ and θ ≤ 1
  have hcosθ_nonneg : 0 ≤ Real.cos (θ : ℝ) := by
    have hlower : 1 - (θ : ℝ) ^ 2 / 2 ≤ Real.cos (θ : ℝ) := by
      simpa using (Real.one_sub_sq_div_two_le_cos (x := (θ : ℝ)))
    nlinarith [hlower, hθ1']
  -- Step 2: 1 - c² ≤ θ²
  have hsin_le_θ : Real.sin (θ : ℝ) ≤ (θ : ℝ) := Real.sin_le htheta0
  have hsin_nonneg : 0 ≤ Real.sin (θ : ℝ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi htheta0 hθ1π
  have hsin_sq : (Real.sin (θ : ℝ)) ^ 2 ≤ (θ : ℝ) ^ 2 := by
    nlinarith [hsin_le_θ, hsin_nonneg]
  have hcos_sq : (Real.cos (θ : ℝ)) ^ 2 = 1 - (Real.sin (θ : ℝ)) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (θ : ℝ)
    nlinarith
  have hcosθ_sq_ge : 1 - (θ : ℝ) ^ 2 ≤ (Real.cos (θ : ℝ)) ^ 2 := by
    nlinarith [hcos_sq, hsin_sq]
  have hc_sq_ge : (Real.cos (θ : ℝ)) ^ 2 ≤ |c| ^ 2 := by
    exact sq_le_sq' (by nlinarith [hcosθ_nonneg, abs_nonneg c]) hcosc
  have hcq : c ^ 2 = |c| ^ 2 := by rw [sq_abs]
  have hsq2 : 1 - c ^ 2 ≤ (θ : ℝ) ^ 2 := by
    rw [hcq]
    nlinarith [hcosθ_sq_ge, hc_sq_ge]
  -- Step 3: decompose w = mm - c • n
  let w : EuclideanSpace ℝ (Fin 3) := mm - c • n
  have hw_norm_sq : ‖w‖ ^ 2 = 1 - c ^ 2 := by
    change ‖mm - c • n‖ ^ 2 = 1 - c ^ 2
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm, norm_smul, hmm, hn]
    simp [c, n, mm, sq_abs]
    ring
  -- Step 4: inner mm e = inner w e
  have hw_e : inner ℝ w e = inner ℝ mm e := by
    change inner ℝ (mm - c • n) e = inner ℝ mm e
    rw [inner_sub_left, real_inner_smul_left, hPe]
    ring
  -- Step 5: |inner mm e| = |inner w e| ≤ ‖w‖ ≤ θ
  have hwle : |inner ℝ w e| ≤ ‖w‖ := by
    have hit := abs_real_inner_le_norm w e
    rwa [he, mul_one] at hit
  have hw_theta : ‖w‖ ≤ (θ : ℝ) := by
    nlinarith [hw_norm_sq, hsq2, norm_nonneg w, htheta0]
  have hw_e' : inner ℝ (S.basis 0) e = inner ℝ w e := by simpa [mm] using hw_e.symm
  calc
    |inner ℝ (S.basis 0) e| = |inner ℝ w e| := by rw [← hw_e']
    _ ≤ (θ : ℝ) := (hwle.trans hw_theta)

/-- **Volume of the inner plank model against the tube it contains.**  With Jacobian
`J = κ³/(ab)` and the tube volume lower bound `c₃ δ² ≤ |T|` of `Tube.le_volume`,

`|P| = 8 δ² / (ab) ≤ (8 / (κ³ c₃)) · J · |T|`. -/
theorem volume_normalisedPlank_le {δ : ℝ≥0} (ha : 0 < a) (hb : 0 < b) (hδ0 : 0 < δ)
    {κ : ℝ} (hκ : 0 < κ) {ha'b' : δ / b ≤ δ / a} {hb'1 : δ / a ≤ 1}
    (P : Plank (δ / b) (δ / a) ha'b' hb'1) (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    {J : ℝ≥0} (hJ : J * (a * b) = Real.toNNReal κ ^ 3) :
    volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ ((8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3) : ℝ≥0) : ENNReal)
        * ((J : ENNReal) * volume (T.carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
  have hk0 : 0 < Real.toNNReal κ := (Real.toNNReal_pos).mpr hκ
  have hkne : Real.toNNReal κ ≠ 0 := ne_of_gt hk0
  have hc0 : 0 < Tube.le_volume.c 3 := Tube.le_volume.c_pos 3
  have hcne : Tube.le_volume.c 3 ≠ 0 := ne_of_gt hc0
  have hane : a ≠ 0 := ne_of_gt ha
  have hbne : b ≠ 0 := ne_of_gt hb
  have hJ' : J = Real.toNNReal κ ^ 3 / (a * b) := by
    rw [← hJ]
    field_simp [hane, hbne]
  have hPVol : volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((8 * (δ / b) * (δ / a) : ℝ≥0) : ENNReal) := by
    simpa [one_mul] using (Prism3D.volume_carrier P :
      volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = 8 * (δ / b : ℝ≥0) * (δ / a : ℝ≥0) * (1 : ℝ≥0))
  have hTv : ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (δ : ENNReal) ^ 2
      ≤ (volume (T.carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
    simpa [finrank_euclideanSpace_fin] using (Tube.le_volume (E := EuclideanSpace ℝ (Fin 3)) T)
  have hId : (8 * (δ / b) * (δ / a) : ℝ≥0)
      = (8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3))
        * (J * (Tube.le_volume.c 3 * δ ^ 2)) := by
    rw [hJ']
    field_simp [hane, hbne, hkne, hcne]
  calc
    (volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3))))
        = ((8 * (δ / b) * (δ / a) : ℝ≥0) : ENNReal) := hPVol
    _ ≤ ((8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3) : ℝ≥0) : ENNReal)
          * ((J : ENNReal) * ((Tube.le_volume.c 3 * δ ^ 2 : ℝ≥0) : ENNReal)) := by
        rw [congrArg (fun z : ℝ≥0 => (z : ENNReal)) hId]
        simp
    _ ≤ ((8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3) : ℝ≥0) : ENNReal)
          * ((J : ENNReal) * (volume (T.carrier : Set (EuclideanSpace ℝ (Fin 3))))) := by
        apply mul_le_mul_right
        apply mul_le_mul_right
        simpa using hTv

/-- **Maximal density transfer** (`lem:geometryAffineShadingTransfer`).  If every fine tube's image
lies in its inner plank model, the maximal density of the model family is controlled by that of the
tube family, with the absolute constant `8 / (κ³ c₃)`.

The normalisation is an affine equivalence (`Plank.exists_affineEquiv_of_isPlankNormalisation`), so
`Kakeya.maxDensity_mapAffine` transports the tube family's maximal density exactly; the containment
plus `Plank.volume_normalisedPlank_le` then feeds
`Kakeya.maxDensity_le_of_subset_of_volume_le`. -/
theorem maxDensity_le_of_image_subset {ι : Type*} (s : Finset ι) {δ : ℝ≥0}
    (ha : 0 < a) (hδ0 : 0 < δ) (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ} (hκ : 0 < κ)
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g) {J : ℝ≥0}
    (hvolf : ∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    {ha'b' : δ / b ≤ δ / a} {hb'1 : δ / a ≤ 1} (P : ι → Plank (δ / b) (δ / a) ha'b' hb'1)
    (hsub : ∀ i ∈ s, f '' ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    Kakeya.maxDensity s (fun i => (P i).toConvexSpaceBody)
      ≤ ((8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3) : ℝ≥0) : ENNReal)
        * Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) := by
  classical
  obtain ⟨F, hF⟩ := exists_affineEquiv_of_isPlankNormalisation ha W hκ hnorm
  let Q : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun i => (T i).toConvexSpaceBody.mapAffine F
  let C : ENNReal := ((8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3) : ℝ≥0) : ENNReal)
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have himg (A : Set (EuclideanSpace ℝ (Fin 3))) :
      (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' A =
        (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' A := by
    apply congrArg (fun g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) => g '' A)
    funext x
    exact hF x
  have hV0 : volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0 :=
    ne_of_gt (Prism3D.volume_pos_of_pos W ha)
  have hVtop : volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ ⊤ := by
    rw [Prism3D.volume_carrier W]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) ENNReal.coe_ne_top)
      (by norm_num)
  have hvol_eq : affineJacobian F * volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (J : ENNReal) * volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [← Kakeya.volume_image_affineEquiv F (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))]
    rw [himg (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))]
    exact hvolf (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))
  have h_aff : affineJacobian F = (J : ENNReal) := by
    have hJswap :
        volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) * affineJacobian F
          = volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) * (J : ENNReal) := by
      calc
        volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) * affineJacobian F
            = affineJacobian F * volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
              rw [mul_comm]
        _ = (J : ENNReal) * volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := hvol_eq
        _ = volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) * (J : ENNReal) := by rw [mul_comm]
    exact (ENNReal.mul_right_inj (a := volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      hV0 hVtop).mp hJswap
  have h_cont : ∀ i ∈ s, (Q i).carrier ⊆ ((P i).toConvexSpaceBody).carrier := by
    intro i hi
    calc
      (Q i).carrier
          = (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
              '' ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
            simp [Q, ConvexSpaceBody.mapAffine_carrier]
      _ = (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
              '' ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
            himg ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      _ ⊆ (P i).carrier := by
            simpa using hsub i hi
  have h_vol : ∀ i ∈ s,
      volume ((P i).toConvexSpaceBody).carrier ≤ C * volume (Q i).carrier := by
    intro i hi
    have hJeq : J * (a * b) = Real.toNNReal κ ^ 3 := jacobian_eq ha W hκ hnorm hvolf
    have hvolPl := volume_normalisedPlank_le ha hb hδ0 hκ (P i) (T i).toTube hJeq
    have hVQ : volume ((Q i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = affineJacobian F * volume ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
      simp [Q, Kakeya.volume_image_affineEquiv]
    calc
      volume ((P i).toConvexSpaceBody).carrier
          ≤ ((8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3) : ℝ≥0) : ENNReal)
                * ((J : ENNReal) * volume ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
              simpa [C] using hvolPl
      _ = C * (affineJacobian F * volume ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
            rw [h_aff]
      _ = C * volume ((Q i).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
            rw [← hVQ]
  have hle : Kakeya.maxDensity s (fun i => (P i).toConvexSpaceBody)
      ≤ C * Kakeya.maxDensity s Q := by
    exact Kakeya.maxDensity_le_of_subset_of_volume_le s Q (fun i => (P i).toConvexSpaceBody)
      (C := C) h_cont h_vol
  have hden : Kakeya.maxDensity s Q = Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) := by
    simpa [Q] using (Kakeya.maxDensity_mapAffine s (fun i : ι => (T i).toConvexSpaceBody) F)
  calc
    Kakeya.maxDensity s (fun i : ι => (P i).toConvexSpaceBody) ≤ C * Kakeya.maxDensity s Q := hle
    _ = C * Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) := by rw [hden]

end Plank

end
