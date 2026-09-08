/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody
public import Kakeya.Thickness.Basic
public import Kakeya.Thickness.Projection
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Kakeya.Mathlib.Analysis.AddTorsor

/-!
# Rectangular prism in inner product spaces.
-/

open Metric Convexity

@[expose] public section

noncomputable section

/--
A `PrismNDim` is a Prism in n dimensions,
with thicknesses given by the input `thicknesses : Fin n → NNReal`.
(and side lengths twice the thicknesses).
-/
structure PrismNDim (n : ℕ) (E S : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [PseudoMetricSpace S] [NormedAddTorsor E S]
    extends ConvexSpaceBody S where
  /-- Center of the Prism. -/
  center : S
  /-- Orthonormal basis of directions of prism -/
  basis : OrthonormalBasis (Fin n) ℝ E
  /-- Thicknesses of the Prism in the normal directions. -/
  thicknesses : Fin n → NNReal
  /-- A point belongs to the Prism if and only if
  its inner product with each ith normal is at most `thicknesses i` in absolute value
  -/
  mem_carrier_iff (x : S) :
    x ∈ carrier ↔ ∀ i, |basis.repr (x -ᵥ center) i| ≤ thicknesses i

namespace PrismNDim

variable {n : ℕ} {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [PseudoMetricSpace S] [NormedAddTorsor E S]

/-- The carrier of an `n`-dimensional prism is the image of an axis-aligned box
in `Fin n → ℝ` under the canonical chain
`Set.Icc → EuclideanSpace ℝ (Fin n) → E → S`. -/
theorem carrier_eq_image_Icc (P : PrismNDim n E S) :
    (P.carrier : Set S) = (· +ᵥ P.center) '' (P.basis.repr.symm '' (WithLp.toLp 2 ''
        Set.Icc (fun i => - (P.thicknesses i : ℝ)) (fun i => (P.thicknesses i : ℝ)))) := by
  rw [Set.image_image, Set.image_image]
  ext x
  rw [P.mem_carrier_iff]
  simp only [Set.mem_image, Set.mem_Icc, Pi.le_def]
  constructor
  · intro hx
    use (P.basis.repr (x -ᵥ P.center)).ofLp
    refine ⟨⟨fun i => (abs_le.mp (hx i)).1, fun i => (abs_le.mp (hx i)).2⟩, ?_⟩
    simp [WithLp.toLp_ofLp, vsub_vadd]
  · rintro ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    intro i
    simp only [vadd_vsub, LinearIsometryEquiv.apply_symm_apply, WithLp.ofLp_toLp]
    exact abs_le.mpr ⟨hy₁ i, hy₂ i⟩

/-- The carrier of a prism is closed: it is the finite intersection of the closed slabs
`{x | |⟪eᵢ, x - center⟫| ≤ thicknessesᵢ}`. -/
theorem isClosed_carrier (P : PrismNDim n E S) : IsClosed (P.carrier : Set S) :=
  P.toConvexSpaceBody.isCompact.isClosed

/-- The carrier of a prism is measurable (it is closed). -/
theorem measurableSet_carrier [MeasurableSpace S] [BorelSpace S] (P : PrismNDim n E S) :
    MeasurableSet (P.carrier : Set S) :=
  P.isClosed_carrier.measurableSet

/-- The carrier of an `n`-dimensional prism is the preimage of an axis-aligned box under the
chain `S → E → EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)`. -/
theorem carrier_eq_preimage_Icc (P : PrismNDim n E S) :
    P.carrier = (· -ᵥ P.center) ⁻¹' (P.basis.repr ⁻¹' (WithLp.ofLp ⁻¹'
      Set.Icc (fun i => - (P.thicknesses i : ℝ)) (fun i => (P.thicknesses i : ℝ)))) := by
  ext x
  rw [P.mem_carrier_iff]
  simp [Set.mem_preimage, Set.mem_Icc, Pi.le_def, abs_le, forall_and]

/-- Build a `PrismNDim` from a center in `S` and an orthonormal frame with half-widths in `E`,
the prism being described through the displacement `x -ᵥ center`. -/
def mk' (center : S) (basis : OrthonormalBasis (Fin n) ℝ E) (thicknesses : Fin n → NNReal) :
    PrismNDim n E S :=
  haveI : FiniteDimensional ℝ E := Module.Basis.finiteDimensional_of_finite basis.toBasis
  { carrier := { x | ∀ i, |basis.repr (x -ᵥ center) i| ≤ thicknesses i }
    convex' := by
      refine .of_convexCombPair_mem fun a b ha hb hab x hx y hy => ?_
      intro i
      -- Convex combinations in the affine space `S` differ from `center` by the linear
      -- combination of the displacements `x -ᵥ center` and `y -ᵥ center` in `E`.
      have key : convexCombPair a b ha hb hab x y -ᵥ center
          = a • (x -ᵥ center) + b • (y -ᵥ center) := by
        rw [AddTorsor.convexCombPair_eq_lineMap, AffineMap.lineMap_apply, vadd_vsub_assoc,
          ← vsub_sub_vsub_cancel_right x y center]
        match_scalars <;> linarith
      simp only [key, map_add, map_smul, WithLp.ofLp_add, WithLp.ofLp_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg ha, abs_mul, abs_of_nonneg hb,
        show (thicknesses i : ℝ) = a * thicknesses i + b * thicknesses i from by
          rw [← add_mul, hab, one_mul]]
      gcongr <;> [exact hx i; exact hy i]
    isCompact' := by
      -- The carrier is the image, under the isometry `v ↦ v +ᵥ center`, of a compact box in `E`.
      have hbox : IsCompact {v : E | ∀ i, |basis.repr v i| ≤ thicknesses i} := by
        apply Metric.isCompact_of_isClosed_isBounded
        · rw [Set.setOf_forall]
          exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
        · refine (Metric.isBounded_closedBall (x := (0 : E))
            (r := ∑ i, (thicknesses i : ℝ))).subset fun v hv => ?_
          rw [Metric.mem_closedBall, dist_zero_right, ← basis.sum_repr v]
          refine norm_sum_le_of_le _ fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs, basis.norm_eq_one, mul_one]
          exact hv i
      have heq : {x : S | ∀ i, |basis.repr (x -ᵥ center) i| ≤ thicknesses i}
          = (· +ᵥ center) '' {v : E | ∀ i, |basis.repr v i| ≤ thicknesses i} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_image]
        refine ⟨fun hx => ⟨x -ᵥ center, hx, vsub_vadd x center⟩, ?_⟩
        rintro ⟨v, hv, rfl⟩
        simpa using hv
      rw [heq]
      exact hbox.image (IsometryEquiv.vaddConst center).continuous
    nonempty' := by
      use center
      simp
    center := center
    basis := basis
    thicknesses := thicknesses
    mem_carrier_iff := by simp
  }

/-- `mk'` keeps the given center. -/
theorem center_mk' (center : S) (basis : OrthonormalBasis (Fin n) ℝ E)
    (thicknesses : Fin n → NNReal) :
  (mk' center basis thicknesses).center = center := rfl

/-- `mk'` keeps the given orthonormal frame. -/
theorem basis_mk' (center : S) (basis : OrthonormalBasis (Fin n) ℝ E)
    (thicknesses : Fin n → NNReal) :
  (mk' center basis thicknesses).basis = basis := rfl

/-- `mk'` keeps the given half-widths. -/
theorem thicknesses_mk' (center : S) (basis : OrthonormalBasis (Fin n) ℝ E)
    (thicknesses : Fin n → NNReal) :
  (mk' center basis thicknesses).thicknesses = thicknesses := rfl

/-- Spanning form of the carrier of `mk' center basis thicknesses`: a point lies in the prism iff
it is `center` displaced by `∑ tᵢ • basisᵢ` with `|tᵢ| ≤ thicknesses i`. -/
theorem mk'_carrier_eq_spanning (center : S) (basis : OrthonormalBasis (Fin n) ℝ E)
    (thicknesses : Fin n → NNReal) :
    (mk' center basis thicknesses).carrier
      = { x | ∃ t : Fin n → ℝ,
          (∀ i, |t i| ≤ (thicknesses i : ℝ)) ∧ x = (∑ i, t i • basis i) +ᵥ center } := by
  have hrepr : ∀ (t : Fin n → ℝ) (i),
      basis.repr ((∑ j, t j • basis j) : E) i = t i := by
    intro t i
    simp only [OrthonormalBasis.repr_apply_apply, inner_sum, real_inner_smul_right]
    rw [Finset.sum_eq_single i]
    · rw [real_inner_self_eq_norm_sq, basis.norm_eq_one]; ring
    · intro j _ hji
      rw [basis.inner_eq_zero (Ne.symm hji)]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  ext x
  simp only [mk', Set.mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨fun i => basis.repr (x -ᵥ center) i, fun i => hx i, ?_⟩
    rw [basis.sum_repr (x -ᵥ center), vsub_vadd]
  · rintro ⟨t, ht, rfl⟩
    intro i
    rw [vadd_vsub, hrepr t i]
    exact ht i

/-- A prism is contained in the closed ball about its center whose radius is the sum of its
thicknesses. -/
theorem carrier_subset_closedBall (P : PrismNDim n E S) :
    (P.carrier : Set S) ⊆ Metric.closedBall P.center (∑ i, (P.thicknesses i : ℝ)) := by
  intro x hx
  rw [P.mem_carrier_iff] at hx
  rw [Metric.mem_closedBall, dist_eq_norm_vsub E, ← P.basis.sum_repr (x -ᵥ P.center)]
  refine norm_sum_le_of_le _ fun i _ => ?_
  rw [norm_smul, Real.norm_eq_abs, P.basis.norm_eq_one, mul_one]
  exact hx i

/-- The affine subspace through the center of a prism spanned by a chosen set of its axes. -/
def coordinateSubspace (P : PrismNDim n E S) (I : Finset (Fin n)) : AffineSubspace ℝ S :=
  AffineSubspace.mk' P.center
    (Submodule.span ℝ (Set.range (fun j : I => P.basis (j : Fin n))))

/-- The coordinate subspace spanned by the axes in `I` has dimension `I.card`. -/
theorem finrank_coordinateSubspace_direction (P : PrismNDim n E S) (I : Finset (Fin n)) :
    Module.finrank ℝ (P.coordinateSubspace I).direction = I.card := by
  have hli : LinearIndependent ℝ (fun j : I => P.basis (j : Fin n)) :=
    (P.basis.orthonormal.comp _ Subtype.val_injective).linearIndependent
  rw [coordinateSubspace, AffineSubspace.direction_mk', finrank_span_eq_card hli,
    Fintype.card_coe]

/-- A vector in the direction of a coordinate subspace has vanishing coordinates off `I`. -/
private theorem basis_repr_eq_zero_of_mem_coordinateSubspace_direction
    (P : PrismNDim n E S) {I : Finset (Fin n)} {v : E}
    (hv : v ∈ (P.coordinateSubspace I).direction) {j : Fin n} (hj : j ∉ I) :
    P.basis.repr v j = 0 := by
  rw [coordinateSubspace, AffineSubspace.direction_mk'] at hv
  refine Submodule.span_induction (p := fun v _ => P.basis.repr v j = 0) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨k, rfl⟩
    rw [P.basis.repr_apply_apply, P.basis.inner_eq_zero]
    exact fun hkj => hj (hkj ▸ k.property)
  · simp
  · intro x y _ _ hx hy
    simp [hx, hy]
  · intro a x _ hx
    simp [hx]

/-- A prism lies within distance `∑_{j ≥ i} thicknesses j` of the affine subspace through its
center spanned by the axes preceding `i`. -/
theorem carrier_subset_cthickening_coordinateSubspace_Iio
    (P : PrismNDim n E S) (i : Fin n) :
    (P.carrier : Set S) ⊆ Metric.cthickening
      (∑ j ∈ Finset.Ici i, P.thicknesses j : NNReal)
      (P.coordinateSubspace (Finset.Iio i)) := by
  intro x hx
  have hx' := (P.mem_carrier_iff x).1 hx
  set w : E := ∑ j ∈ Finset.Iio i, P.basis.repr (x -ᵥ P.center) j • P.basis j with hw
  refine Metric.mem_cthickening_of_dist_le x (w +ᵥ P.center) _ _ ?_ ?_
  · rw [coordinateSubspace, SetLike.mem_coe, AffineSubspace.mem_mk', vadd_vsub, hw]
    exact Submodule.sum_mem _ fun j hj =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
  · have hdisj : Disjoint (Finset.Iio i) (Finset.Ici i) := by
      rw [Finset.disjoint_left]
      intro j hj₁ hj₂
      rw [Finset.mem_Iio] at hj₁
      rw [Finset.mem_Ici] at hj₂
      omega
    have hunion : Finset.Iio i ∪ Finset.Ici i = Finset.univ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ici, Finset.mem_univ,
        iff_true]
      exact lt_or_ge j i
    have hdecomp :
        x -ᵥ P.center = w +
          ∑ j ∈ Finset.Ici i, P.basis.repr (x -ᵥ P.center) j • P.basis j := by
      rw [hw, ← Finset.sum_union hdisj, hunion, P.basis.sum_repr]
    rw [dist_eq_norm_vsub E, vsub_vadd_eq_vsub_sub, hdecomp, add_sub_cancel_left]
    simp only [NNReal.coe_sum]
    refine norm_sum_le_of_le _ fun j hj => ?_
    rw [norm_smul, Real.norm_eq_abs, P.basis.norm_eq_one, mul_one]
    exact hx' j

/-- The `i`-th ethickness of a prism is at most the sum of its half-widths from index
`i` onward. No ordering assumption on the half-widths is needed. -/
theorem ethickness_le_sum_Ici_thicknesses (P : PrismNDim n E S) (i : Fin n) :
    Metric.ethickness ℝ P.carrier i ≤
      (∑ j ∈ Finset.Ici i, P.thicknesses j : NNReal) := by
  have hfd : FiniteDimensional ℝ
      (P.coordinateSubspace (Finset.Iio i)).direction := by
    rw [coordinateSubspace, AffineSubspace.direction_mk']
    exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hrank : Module.rank ℝ (P.coordinateSubspace (Finset.Iio i)).direction =
      (i : Cardinal) := by
    rw [← Module.finrank_eq_rank, P.finrank_coordinateSubspace_direction,
      Fin.card_Iio]
  exact Metric.ethickness_le_of_cthickening _ hrank.le
    (P.carrier_subset_cthickening_coordinateSubspace_Iio i)

/-- If the half-widths of a prism are decreasing, then its `i`-th half-width is at most
its `i`-th ethickness. -/
theorem thicknesses_le_ethickness
    {S' : Type*} [MetricSpace S'] [NormedAddTorsor E S']
    (P : PrismNDim n E S')
    (hmono : Antitone P.thicknesses) (i : Fin n) :
    (P.thicknesses i : ENNReal) ≤ Metric.ethickness ℝ P.carrier i := by
  letI : FiniteDimensional ℝ E :=
    Module.Basis.finiteDimensional_of_finite P.basis.toBasis
  let A : AffineSubspace ℝ S' := P.coordinateSubspace (Finset.Iic i)
  have hc : P.center ∈ A := by
    change P.center ∈ P.coordinateSubspace (Finset.Iic i)
    rw [coordinateSubspace]
    exact AffineSubspace.self_mem_mk' _ _
  let c : ↥A := ⟨P.center, hc⟩
  letI : Nonempty A := ⟨c⟩
  have hfr : Module.finrank ℝ A.direction = (i : ℕ) + 1 := by
    change Module.finrank ℝ
      (P.coordinateSubspace (Finset.Iic i)).direction = (i : ℕ) + 1
    rw [P.finrank_coordinateSubspace_direction, Fin.card_Iic]
  have hball : Metric.closedBall c (P.thicknesses i : ℝ) ⊆
      (EuclideanGeometry.orthogonalProjection A : S' →ᵃ[ℝ] ↥A) '' P.carrier := by
    intro y hy
    have hynorm : ‖(y : S') -ᵥ P.center‖ ≤ (P.thicknesses i : ℝ) := by
      change dist (y : S') P.center ≤ (P.thicknesses i : ℝ) at hy
      rwa [dist_eq_norm_vsub E] at hy
    have hy_dir : (y : S') -ᵥ P.center ∈ A.direction :=
      (AffineSubspace.vsub_right_mem_direction_iff_mem hc (y : S')).2 y.property
    refine ⟨(y : S'), ?_, ?_⟩
    · rw [P.mem_carrier_iff]
      intro j
      by_cases hj : j ∈ Finset.Iic i
      · rw [P.basis.repr_apply_apply, real_inner_comm]
        calc
          |inner ℝ ((y : S') -ᵥ P.center) (P.basis j)|
              ≤ ‖(y : S') -ᵥ P.center‖ * ‖P.basis j‖ :=
                abs_real_inner_le_norm _ _
          _ = ‖(y : S') -ᵥ P.center‖ := by rw [P.basis.norm_eq_one, mul_one]
          _ ≤ (P.thicknesses i : ℝ) := hynorm
          _ ≤ (P.thicknesses j : ℝ) := by
            exact_mod_cast hmono (Finset.mem_Iic.mp hj)
      · have hzero : P.basis.repr ((y : S') -ᵥ P.center) j = 0 := by
          apply P.basis_repr_eq_zero_of_mem_coordinateSubspace_direction
            (I := Finset.Iic i) (j := j) (hj := hj)
          change (y : S') -ᵥ P.center ∈
            (P.coordinateSubspace (Finset.Iic i)).direction at hy_dir
          exact hy_dir
        rw [hzero, abs_zero]
        exact (P.thicknesses j).coe_nonneg
    · exact EuclideanGeometry.orthogonalProjection_mem_subspace_eq_self y
  have hlower := le_ethickness_cthickening
    (V := A.direction) (E := A) (s := ({c} : Set A)) (Set.singleton_nonempty c)
    (ρ := (P.thicknesses i : ℝ)) (n := (i : ℕ)) (by omega)
  rw [Set.subsingleton_singleton.ethickness_eq_zero, zero_add,
    Metric.cthickening_singleton c (P.thicknesses i).coe_nonneg] at hlower
  calc
    (P.thicknesses i : ENNReal)
        ≤ Metric.ethickness ℝ (Metric.closedBall c (P.thicknesses i : ℝ)) i := by
      simpa using hlower
    _ ≤ Metric.ethickness ℝ
        ((EuclideanGeometry.orthogonalProjection A : S' →ᵃ[ℝ] ↥A) '' P.carrier) i :=
      Metric.ethickness_monotone hball i
    _ ≤ Metric.ethickness ℝ P.carrier i :=
      ethickness_image_orthogonalProjection_le P.carrier i

/-- **Pairwise coordinate spread.** For `x`, `y` in a prism,
`|⟪y -ᵥ x, basis i⟫| ≤ 2 * thicknesses i`; the factor `2` is sharp, attained on opposite faces. -/
theorem abs_inner_vsub_basis_le (P : PrismNDim n E S) {x y : S}
    (hx : x ∈ P.carrier) (hy : y ∈ P.carrier) (i : Fin n) :
    |inner ℝ (y -ᵥ x) (P.basis i)| ≤ 2 * (P.thicknesses i : ℝ) := by
  rw [P.mem_carrier_iff] at hx hy
  rw [real_inner_comm, ← P.basis.repr_apply_apply]
  have key : P.basis.repr (y -ᵥ x) i
      = P.basis.repr (y -ᵥ P.center) i - P.basis.repr (x -ᵥ P.center) i := by
    rw [show y -ᵥ x = (y -ᵥ P.center) - (x -ᵥ P.center) from
        (vsub_sub_vsub_cancel_right y x P.center).symm, map_sub, PiLp.sub_apply]
  rw [key]
  calc |P.basis.repr (y -ᵥ P.center) i - P.basis.repr (x -ᵥ P.center) i|
      ≤ |P.basis.repr (y -ᵥ P.center) i| + |P.basis.repr (x -ᵥ P.center) i| := abs_sub _ _
    _ ≤ (P.thicknesses i : ℝ) + (P.thicknesses i : ℝ) := add_le_add (hy i) (hx i)
    _ = 2 * (P.thicknesses i : ℝ) := by ring

/-- The rank-`(n-1)` affine subspace through the center of the prism `P` spanned by all axes
except the `i`-th. -/
def hyperplane (P : PrismNDim n E S) (i : Fin n) : AffineSubspace ℝ S :=
  AffineSubspace.mk' P.center
    (Submodule.span ℝ (Set.range (fun j : {j : Fin n // j ≠ i} => P.basis j)))

/-- The direction of `P.hyperplane i` has dimension `n - 1`: it is spanned by the `n - 1`
orthonormal axes other than the `i`-th. -/
theorem finrank_hyperplane_direction (P : PrismNDim n E S) (i : Fin n) :
    Module.finrank ℝ (P.hyperplane i).direction = n - 1 := by
  have hli : LinearIndependent ℝ (fun j : {j : Fin n // j ≠ i} => P.basis j) :=
    (P.basis.orthonormal.comp _ Subtype.val_injective).linearIndependent
  rw [hyperplane, AffineSubspace.direction_mk', finrank_span_eq_card hli,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]

/-- **Carrier in a slab.** The prism `P` lies in the closed `thicknesses i`-neighbourhood of
`P.hyperplane i`. -/
theorem carrier_subset_cthickening_hyperplane (P : PrismNDim n E S) (i : Fin n) :
    (P.carrier : Set S) ⊆ Metric.cthickening (P.thicknesses i) (P.hyperplane i) := by
  intro x hx
  have hx' := (P.mem_carrier_iff x).1 hx
  set w : E := ∑ j ∈ Finset.univ.erase i, P.basis.repr (x -ᵥ P.center) j • P.basis j with hw
  refine Metric.mem_cthickening_of_dist_le x (w +ᵥ P.center) _ _ ?_ ?_
  · rw [hyperplane, SetLike.mem_coe, AffineSubspace.mem_mk', vadd_vsub, hw]
    exact Submodule.sum_mem _ fun j hj =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, Finset.ne_of_mem_erase hj⟩, rfl⟩)
  · have hxy : x -ᵥ (w +ᵥ P.center) = P.basis.repr (x -ᵥ P.center) i • P.basis i := by
      have hsum := P.basis.sum_repr (x -ᵥ P.center)
      rw [vsub_vadd_eq_vsub_sub, hw, Finset.sum_erase_eq_sub (Finset.mem_univ i), hsum]
      abel
    rw [dist_eq_norm_vsub E, hxy, norm_smul, Real.norm_eq_abs, P.basis.norm_eq_one, mul_one]
    exact hx' i

/-- **Prism thickness from a single half-width.** The affine thickness of an `n`-dimensional prism
at rank `n - 1` is bounded by the `i`-th half-width, for every axis `i`. -/
theorem thickness_carrier_le (P : PrismNDim n E S) (i : Fin n) :
    Metric.thickness ℝ (P.carrier : Set S) (n - 1) ≤ (P.thicknesses i : ℝ) := by
  have hfd : FiniteDimensional ℝ (P.hyperplane i).direction := by
    rw [hyperplane, AffineSubspace.direction_mk']
    exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hrank : Module.rank ℝ (P.hyperplane i).direction = (↑(n - 1) : Cardinal) := by
    rw [← Module.finrank_eq_rank, P.finrank_hyperplane_direction i]
  exact Metric.thickness_le_of_cthickening (P.thicknesses i).coe_nonneg hrank.le
    (P.carrier_subset_cthickening_hyperplane i)

/-- The axes of a prism are nonzero, being unit vectors. -/
theorem basis_ne_zero (P : PrismNDim n E S) (i : Fin n) : P.basis i ≠ 0 :=
  ne_zero_of_norm_ne_zero (ne_zero_of_eq_one (P.basis.norm_eq_one i))

/-- Two distinct axes of a prism are linearly independent. -/
theorem linearIndependent_pair_basis (P : PrismNDim n E S) (i j : Fin n) (hij : i ≠ j) :
    LinearIndependent ℝ ![(P.basis i), (P.basis j)] := by
  rw [LinearIndependent.pair_iff' (P.basis_ne_zero i)]
  intro a ha
  have := congr_arg (inner ℝ (P.basis j)) ha
  simp [inner_smul_right, P.basis.inner_eq_zero hij.symm, P.basis.norm_eq_one] at this

open MeasureTheory NNReal

/-- Two prisms are essentially distinct if their carriers are
(see `_root_.IsEssentiallyDistinct`). -/
def IsEssentiallyDistinct [MeasureSpace S] (P : PrismNDim n E S) (Q : PrismNDim n E S) : Prop :=
  _root_.IsEssentiallyDistinct P.carrier Q.carrier

/-- Prism essential distinctness is symmetric. -/
theorem IsEssentiallyDistinct.symm [MeasureSpace S] {P Q : PrismNDim n E S}
    (h : P.IsEssentiallyDistinct Q) : Q.IsEssentiallyDistinct P :=
  _root_.isEssentiallyDistinct_symm h

/-- Prism essential distinctness is a commutative relation. -/
theorem isEssentiallyDistinct_comm [MeasureSpace S] (P Q : PrismNDim n E S) :
    P.IsEssentiallyDistinct Q ↔ Q.IsEssentiallyDistinct P := by
  constructor
  · exact IsEssentiallyDistinct.symm
  · exact IsEssentiallyDistinct.symm

/-- A prism contains its own centre. -/
theorem center_mem_carrier (P : PrismNDim n E S) : P.center ∈ (P.carrier : Set S) := by
  rw [P.mem_carrier_iff]
  intro i
  simp

/-- Dilate a prism by a scalar, scaling every thickness by `c`. -/
def dilation (P : PrismNDim n E S) (c : ℝ≥0) : PrismNDim n E S :=
  mk' P.center P.basis (fun i => c * P.thicknesses i)

@[simp] theorem dilation_center (P : PrismNDim n E S) (c : ℝ≥0) :
    (P.dilation c).center = P.center := rfl

@[simp] theorem dilation_basis (P : PrismNDim n E S) (c : ℝ≥0) :
    (P.dilation c).basis = P.basis := rfl

@[simp] theorem dilation_thicknesses (P : PrismNDim n E S) (c : ℝ≥0) (i : Fin n) :
    (P.dilation c).thicknesses i = c * P.thicknesses i := rfl

/-- If `c ≥ 1` then every prism is contained in its own `c`-dilation. -/
theorem self_subset_dilation (P : PrismNDim n E S) {c : ℝ≥0} (hc : 1 ≤ c) :
    (P.carrier : Set S) ⊆ (P.dilation c).carrier := by
  intro x hx
  rw [P.mem_carrier_iff] at hx
  rw [(P.dilation c).mem_carrier_iff]
  intro i
  refine (hx i).trans ?_
  rw [dilation_thicknesses]
  have hpos : 0 ≤ (P.thicknesses i : ℝ) := NNReal.coe_nonneg _
  have hc' : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  push_cast
  nlinarith

/-- The dilation carrier is monotone in the scale: `c ≤ c'` gives containment. -/
theorem dilation_carrier_mono (P : PrismNDim n E S) {c c' : ℝ≥0} (h : c ≤ c') :
    ((P.dilation c).carrier : Set S) ⊆ (P.dilation c').carrier := by
  intro x hx
  rw [(P.dilation c).mem_carrier_iff] at hx
  rw [(P.dilation c').mem_carrier_iff]
  intro i
  refine (hx i).trans ?_
  rw [dilation_thicknesses, dilation_thicknesses]
  have hpos : 0 ≤ (P.thicknesses i : ℝ) := NNReal.coe_nonneg _
  have h' : (c : ℝ) ≤ (c' : ℝ) := by exact_mod_cast h
  push_cast
  nlinarith

/-- **Controlled enlargement of a containing prism.**  Dilation is taken about each prism's own
centre, so containment `Q ⊆ K` does not by itself transfer to the dilations.  It does transfer at
the cost of the fixed factor `1 + 2 * c`: a point of `Q.dilation c` is `Q.center` displaced by `c`
times a displacement inside `Q`, and both endpoints of that displacement lie in `K`, so each
`K`-coordinate is bounded by `(1 + 2 * c)` times the corresponding half-width of `K`.

This is the enlargement used to compare a maximal density taken over dilated prisms with one taken
over the undilated family: the enlarged test body is a prism, whose volume is controlled by
`PrismNDim.volume_dilation`. -/
theorem dilation_carrier_subset_dilation_of_subset {Q K : PrismNDim n E S}
    (h : (Q.carrier : Set S) ⊆ K.carrier) (c : ℝ≥0) :
    ((Q.dilation c).carrier : Set S) ⊆ (K.dilation (1 + 2 * c)).carrier := by
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ c from bot_le) with hc | hc
  · subst c
    intro x hx
    have hx0 : ∀ i, Q.basis.repr (x -ᵥ Q.center) i = 0 := by
      intro i
      have hle : |Q.basis.repr (x -ᵥ Q.center) i| ≤ (0 : ℝ≥0) := by
        simpa [dilation_thicknesses] using ((Q.dilation 0).mem_carrier_iff x).1 hx i
      have hle' : |Q.basis.repr (x -ᵥ Q.center) i| ≤ (0 : ℝ) := by
        exact_mod_cast hle
      exact abs_eq_zero.mp (le_antisymm hle' (abs_nonneg _))
    have hx_eq : x = Q.center := by
      apply vsub_eq_zero_iff_eq.mp
      calc
        x -ᵥ Q.center = ∑ i, Q.basis.repr (x -ᵥ Q.center) i • Q.basis i :=
          (Q.basis.sum_repr (x -ᵥ Q.center)).symm
        _ = 0 := by simp [hx0]
    rw [hx_eq]
    simpa using (self_subset_dilation K (le_refl (1 : ℝ≥0))) (h Q.center_mem_carrier)
  · intro x hx
    have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
    have hcne : (c : ℝ) ≠ 0 := ne_of_gt hcpos
    have hxQ := ((Q.dilation c).mem_carrier_iff x).1 hx
    set y : S := ((c : ℝ)⁻¹ • (x -ᵥ Q.center)) +ᵥ Q.center
    have hyQ : y ∈ (Q.carrier : Set S) := by
      rw [Q.mem_carrier_iff]
      intro j
      have hxj : |Q.basis.repr (x -ᵥ Q.center) j| ≤ (c : ℝ) * (Q.thicknesses j : ℝ) := by
        have hxj' : |Q.basis.repr (x -ᵥ Q.center) j| ≤ (c * Q.thicknesses j : ℝ≥0) := by
          simpa [dilation_thicknesses] using hxQ j
        exact_mod_cast hxj'
      dsimp [y]
      rw [vadd_vsub, map_smul, PiLp.smul_apply, smul_eq_mul]
      calc
        |(c : ℝ)⁻¹ * Q.basis.repr (x -ᵥ Q.center) j|
            ≤ (c : ℝ)⁻¹ * |Q.basis.repr (x -ᵥ Q.center) j| := by
              rw [abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hcpos))]
        _ ≤ (c : ℝ)⁻¹ * (c * (Q.thicknesses j : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hxj (le_of_lt (inv_pos.mpr hcpos))
        _ = (Q.thicknesses j : ℝ) := by
              rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
    have hyK : y ∈ (K.carrier : Set S) := h hyQ
    have hcenterK : Q.center ∈ (K.carrier : Set S) := h Q.center_mem_carrier
    have hxy_scal : (c : ℝ) • (y -ᵥ Q.center) = x -ᵥ Q.center := by
      dsimp [y]
      rw [vadd_vsub, smul_smul, mul_inv_cancel₀ hcne, one_smul]
    have hyK_vsub : y -ᵥ K.center = (y -ᵥ Q.center) + (Q.center -ᵥ K.center) := by
      exact (vsub_add_vsub_cancel y Q.center K.center).symm
    have hvec : x -ᵥ K.center
        = (c : ℝ) • (y -ᵥ K.center) + (1 - (c : ℝ)) • (Q.center -ᵥ K.center) := by
      calc
        x -ᵥ K.center = (x -ᵥ Q.center) + (Q.center -ᵥ K.center) := by
          rw [vsub_add_vsub_cancel]
        _ = (c : ℝ) • (y -ᵥ K.center) + (1 - (c : ℝ)) • (Q.center -ᵥ K.center) := by
          rw [← hxy_scal, hyK_vsub, smul_add]
          have hcomb : (c : ℝ) • (Q.center -ᵥ K.center)
              + (1 - (c : ℝ)) • (Q.center -ᵥ K.center)
              = (1 : ℝ) • (Q.center -ᵥ K.center) := by
            rw [← add_smul]
            congr 1
            ring
          rw [add_assoc, hcomb, one_smul]
    rw [(K.dilation (1 + 2 * c)).mem_carrier_iff]
    intro i
    simpa [dilation_thicknesses, dilation_center, dilation_basis] using
      (by
        have hrepr : K.basis.repr (x -ᵥ K.center) i
            = (c : ℝ) * K.basis.repr (y -ᵥ K.center) i
              + (1 - (c : ℝ)) * K.basis.repr (Q.center -ᵥ K.center) i := by
          rw [hvec, map_add, map_smul, map_smul]
          simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        calc
          |K.basis.repr (x -ᵥ K.center) i|
              ≤ (c : ℝ) * (K.thicknesses i : ℝ) + |1 - (c : ℝ)| * (K.thicknesses i : ℝ) := by
                rw [hrepr]
                refine (abs_add_le _ _).trans ?_
                rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt hcpos)]
                have hyb : |K.basis.repr (y -ᵥ K.center) i| ≤ (K.thicknesses i : ℝ) :=
                  ((K.mem_carrier_iff y).1 hyK i)
                have hcb : |K.basis.repr (Q.center -ᵥ K.center) i| ≤ (K.thicknesses i : ℝ) :=
                  ((K.mem_carrier_iff Q.center).1 hcenterK i)
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hyb (le_of_lt hcpos))
                  (mul_le_mul_of_nonneg_left hcb (abs_nonneg _))
          _ ≤ ((1 + 2 * c : ℝ≥0) * K.thicknesses i : ℝ) := by
                have hnn : ((1 + 2 * c : ℝ≥0) * K.thicknesses i : ℝ)
                    = (1 + 2 * (c : ℝ)) * (K.thicknesses i : ℝ) := by
                  push_cast
                  norm_num
                rw [hnn]
                have hnonneg : 0 ≤ (K.thicknesses i : ℝ) := NNReal.coe_nonneg _
                have hs : (c : ℝ) + |1 - (c : ℝ)| ≤ 1 + 2 * (c : ℝ) := by
                  by_cases hc1 : 1 - (c : ℝ) ≥ 0
                  · rw [abs_of_nonneg hc1]; linarith
                  · have hneg : 1 - (c : ℝ) < 0 := lt_of_not_ge hc1
                    rw [abs_of_neg hneg]; linarith
                rw [← add_mul]
                exact mul_le_mul_of_nonneg_right hs hnonneg)

/-- Dilating twice is the same as dilating by the product. -/
@[simp] theorem dilation_dilation (P : PrismNDim n E S) (c c' : ℝ≥0) :
    (P.dilation c').dilation c = P.dilation (c * c') := by
  calc
    (P.dilation c').dilation c
        = mk' P.center P.basis (fun i => c * (c' * P.thicknesses i)) := by
      simp [dilation, center_mk', basis_mk', thicknesses_mk']
    _ = mk' P.center P.basis (fun i => (c * c') * P.thicknesses i) := by
      congr; ext i; simp [mul_assoc]
    _ = P.dilation (c * c') := by
      simp [dilation]

/-- **Resize** a prism: keep its center and orthonormal frame, but replace the half-widths by `w`.
The carrier is the box with the same axes through the same center and the new half-widths. -/
def resize (P : PrismNDim n E S) (w : Fin n → ℝ≥0) : PrismNDim n E S :=
  mk' P.center P.basis w

/-- `resize` keeps the center. -/
@[simp] theorem resize_center (P : PrismNDim n E S) (w : Fin n → ℝ≥0) :
    (P.resize w).center = P.center := center_mk' _ _ _

/-- `resize` keeps the orthonormal frame. -/
@[simp] theorem resize_basis (P : PrismNDim n E S) (w : Fin n → ℝ≥0) :
    (P.resize w).basis = P.basis := basis_mk' _ _ _

/-- `resize` replaces the half-widths by the given ones. -/
@[simp] theorem resize_thicknesses (P : PrismNDim n E S) (w : Fin n → ℝ≥0) :
    (P.resize w).thicknesses = w := thicknesses_mk' _ _ _

/-- Membership in a resized prism, in terms of the original center and frame. -/
theorem mem_resize_carrier (P : PrismNDim n E S) (w : Fin n → ℝ≥0) (x : S) :
    x ∈ (P.resize w).carrier ↔ ∀ i, |P.basis.repr (x -ᵥ P.center) i| ≤ w i := by
  rw [(P.resize w).mem_carrier_iff]; simp

/-- Dilation is the special case of `resize` that scales every half-width by `c`. -/
theorem dilation_eq_resize (P : PrismNDim n E S) (c : ℝ≥0) :
    P.dilation c = P.resize (fun i => c * P.thicknesses i) := rfl

/-- Enlarging the half-widths enlarges the resized carrier. -/
theorem resize_carrier_mono (P : PrismNDim n E S) {w w' : Fin n → ℝ≥0} (h : w ≤ w') :
    (P.resize w).carrier ⊆ (P.resize w').carrier := by
  intro x hx
  rw [P.mem_resize_carrier] at hx ⊢
  exact fun i => (hx i).trans (by exact_mod_cast h i)

/-- **A prism sits inside any resizing that only enlarges its half-widths.**

This is `PrismNDim.resize_carrier_mono` with the source prism left unresized; it is the form
needed whenever a prism is enclosed in a coarser box with the same centre and frame. -/
theorem carrier_subset_resize (P : PrismNDim n E S) {w : Fin n → ℝ≥0}
    (h : ∀ i, P.thicknesses i ≤ w i) :
    (P.carrier : Set S) ⊆ (P.resize w).carrier := by
  intro x hx
  rw [P.mem_carrier_iff] at hx
  rw [P.mem_resize_carrier]
  exact fun i => (hx i).trans (by exact_mod_cast h i)

/-- A prism sits inside any dilation of itself by a factor at least `1`. -/
theorem carrier_subset_dilation (P : PrismNDim n E S) {c : ℝ≥0} (hc : 1 ≤ c) :
    P.carrier ⊆ (P.dilation c).carrier := fun x hx =>
  (P.mem_resize_carrier _ x).2 fun i => ((P.mem_carrier_iff x).1 hx i).trans
    (by exact_mod_cast le_mul_of_one_le_left zero_le hc)

/-- **Homothety of a prism.** The image of the prism `P` under the homothety of centre `x` and
ratio `t`: the centre is moved by `AffineMap.homothety x t`, the orthonormal frame is unchanged
and every half-width is scaled by `t`.

The ratio is taken in `ℝ≥0` because the half-widths are; this is no loss, since a prism is
symmetric about its centre. -/
def homothety (P : PrismNDim n E S) (x : S) (t : ℝ≥0) : PrismNDim n E S :=
  mk' (AffineMap.homothety x (t : ℝ) P.center) P.basis (fun i => t * P.thicknesses i)

/-- A prism homothety moves the center by the corresponding homothety of `S`. -/
@[simp] theorem homothety_center (P : PrismNDim n E S) (x : S) (t : ℝ≥0) :
    (P.homothety x t).center = AffineMap.homothety x (t : ℝ) P.center := center_mk' _ _ _

/-- A prism homothety leaves the orthonormal frame unchanged. -/
@[simp] theorem homothety_basis (P : PrismNDim n E S) (x : S) (t : ℝ≥0) :
    (P.homothety x t).basis = P.basis := basis_mk' _ _ _

/-- A prism homothety scales every half-width by the ratio. -/
@[simp] theorem homothety_thicknesses (P : PrismNDim n E S) (x : S) (t : ℝ≥0) :
    (P.homothety x t).thicknesses = fun i => t * P.thicknesses i := thicknesses_mk' _ _ _

/-- **Membership in a prism homothety.** For a positive ratio, a point `y` lies in `P` exactly
when its image under the homothety lies in the homothety of `P`. -/
theorem mem_homothety_iff (P : PrismNDim n E S) (x : S) {t : ℝ≥0} (ht : 0 < t) (y : S) :
    AffineMap.homothety x (t : ℝ) y ∈ (P.homothety x t).carrier ↔ y ∈ P.carrier := by
  rw [(P.homothety x t).mem_carrier_iff, P.mem_carrier_iff]
  simp only [homothety_basis, homothety_center, homothety_thicknesses, NNReal.coe_mul]
  have h_vsub : AffineMap.homothety x (t : ℝ) y -ᵥ AffineMap.homothety x (t : ℝ) P.center
      = (t : ℝ) • (y -ᵥ P.center) := by
    calc
      AffineMap.homothety x (t : ℝ) y -ᵥ AffineMap.homothety x (t : ℝ) P.center
          = ((t : ℝ) • (y -ᵥ x) +ᵥ x) -ᵥ ((t : ℝ) • (P.center -ᵥ x) +ᵥ x) := by
            simp [AffineMap.homothety_apply]
      _ = (t : ℝ) • (y -ᵥ x) - (t : ℝ) • (P.center -ᵥ x) := by
        simp
      _ = (t : ℝ) • ((y -ᵥ x) - (P.center -ᵥ x)) := by rw [smul_sub]
      _ = (t : ℝ) • (y -ᵥ P.center) := by rw [vsub_sub_vsub_cancel_right]
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rw [h_vsub]
  simp_rw [map_smul, PiLp.smul_apply, smul_eq_mul]
  constructor
  · intro h i
    have hi := h i
    rw [abs_mul, abs_of_nonneg (le_of_lt htpos)] at hi
    exact (mul_le_mul_iff_right₀ htpos).mp hi
  · intro h i
    rw [abs_mul, abs_of_nonneg (le_of_lt htpos)]
    exact (mul_le_mul_iff_right₀ htpos).mpr (h i)

/-- **Carrier of a prism homothety.** For a positive ratio, the carrier of `P.homothety x t` is
the image of the carrier of `P` under the homothety of centre `x` and ratio `t`. -/
theorem carrier_homothety (P : PrismNDim n E S) (x : S) {t : ℝ≥0} (ht : 0 < t) :
    ((P.homothety x t).carrier : Set S) = AffineMap.homothety x (t : ℝ) '' P.carrier := by
  ext z
  constructor
  · intro hz
    have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne.symm
    set y := AffineMap.homothety x ((t : ℝ)⁻¹) z with hy
    have hy' : AffineMap.homothety x (t : ℝ) y = z := by
      have h_mul : (t : ℝ) * ((t : ℝ)⁻¹) = (1 : ℝ) := by field_simp [ht']
      calc
        AffineMap.homothety x (t : ℝ) y = AffineMap.homothety x ((t : ℝ) * ((t : ℝ)⁻¹)) z := by
          rw [hy, AffineMap.homothety_mul_apply]
        _ = AffineMap.homothety x (1 : ℝ) z := by rw [h_mul]
        _ = z := by simp
    have hy_mem : y ∈ P.carrier := by
      have : AffineMap.homothety x (t : ℝ) y ∈ (P.homothety x t).carrier := by
        rw [hy']
        exact hz
      rw [mem_homothety_iff P x ht y] at this
      exact this
    exact ⟨y, hy_mem, hy'⟩
  · rintro ⟨y, hy, rfl⟩
    rw [mem_homothety_iff P x ht y]
    exact hy

/-! ### Homothety about the centre of the prism itself

The homothety `s · P := P.homothety P.center s` fixes the centre of `P`, so it is a prism *about
the same point* as `P` and membership in it is read off in the very coordinates that describe
membership in `P`.  That is `PrismNDim.mem_selfHomothety_iff`, and the two lemmas after it
are its two uses. -/

/-- **Membership in a self-centred prism homothety** (blueprint
`lem:prismSelfHomothety_mem_iff`).

Write `s · P := P.homothety P.center s` for the homothety of `P` of ratio `s ≥ 0` about its *own*
centre.  A homothety fixes its centre, so `s · P` has centre `P.center`, the same axes as `P` and
half-widths `s · P.thicknesses`; consequently, for **every** point `y` of the ambient space,

`y ∈ s · P ↔ ∀ i, |⟪b i, y -ᵥ c⟫| ≤ s * t i`.

`PrismNDim.mem_homothety_iff` does *not* supply this.  That lemma characterises membership
of the images `AffineMap.homothety x t y`, i.e. it transports membership along the homothety; here
`y` is an arbitrary point of the ambient space and the criterion is stated in the original
coordinates of `P`.  Both users below need the latter form. -/
theorem mem_selfHomothety_iff (P : PrismNDim n E S) (s : ℝ≥0) (y : S) :
    y ∈ (P.homothety P.center s).carrier ↔
      ∀ i, |P.basis.repr (y -ᵥ P.center) i| ≤ (s : ℝ) * (P.thicknesses i : ℝ) := by
  rw [(P.homothety P.center s).mem_carrier_iff]
  simp only [homothety_basis, homothety_thicknesses, homothety_center, NNReal.coe_mul]
  rw [AffineMap.homothety_apply_same]

/-- **A prism lies in every homothety of itself about its own centre of ratio `≥ 1`** (blueprint
`lem:prismSelfSubsetHomothety`).

For `s ≥ 1` we have `P ⊆ s · P`, the half-widths satisfying `t i ≤ s * t i`. -/
theorem subset_selfHomothety (P : PrismNDim n E S) {s : ℝ≥0} (hs : 1 ≤ s) :
    P.carrier ⊆ (P.homothety P.center s).carrier := by
  intro x hx
  rw [mem_selfHomothety_iff]
  exact_mod_cast fun i => ((P.mem_carrier_iff x).1 hx i).trans
    (le_mul_of_one_le_left (b := P.thicknesses i) (a := s) (by positivity) hs)

/-- **Two points of a prism and its ratio-`3` homothety** (blueprint
`lem:prismTwoPointHomothety`).

For `x, z ∈ P`, the image of `x` under the homothety of ratio `2` centred at `z` lies in the
homothety of `P` of ratio `3` about its own centre:

`AffineMap.homothety z 2 x ∈ 3 · P`.

The statement is affine on purpose: a prism lives in a torsor `S` over the model space `E`, where a
formal combination such as `2 x - z` of two *points* of `S` does not typecheck.  The point in
question is `AffineMap.homothety z (2 : ℝ) x`, which is also literally the form in which the
consumer `Kakeya.ml1Boot.dilate_tube_subset_dilateTestBody` produces its points: the carrier of
`Kakeya.Tube.dilate T 2` is the image of `T` under `AffineMap.homothety T.center 2`.  When `S = E`
is a vector space this is the familiar `2 (x - z) + z = 2 x - z`.

This is the one step at which the central symmetry of a prism is used, and it is precisely what a
general convex body does not supply.  The same computation gives
`AffineMap.homothety z (1 + l) x ∈ (1 + 2 l) · P` for every `l ≥ 0`, but only `l = 1` is ever
needed and the statement is kept in that simpler form. -/
theorem homothety_two_mem_selfHomothety (P : PrismNDim n E S) {x z : S}
    (hx : x ∈ P.carrier) (hz : z ∈ P.carrier) :
    AffineMap.homothety z (2 : ℝ) x ∈ (P.homothety P.center 3).carrier := by
  rw [P.mem_selfHomothety_iff]
  intro i
  have hx' : |P.basis.repr (x -ᵥ P.center) i| ≤ (P.thicknesses i : ℝ) :=
    (P.mem_carrier_iff x).1 hx i
  have hz' : |P.basis.repr (z -ᵥ P.center) i| ≤ (P.thicknesses i : ℝ) :=
    (P.mem_carrier_iff z).1 hz i
  have hvsub : AffineMap.homothety z (2 : ℝ) x -ᵥ P.center
      = 2 • (x -ᵥ P.center) - (z -ᵥ P.center) := by
    rw [AffineMap.homothety_apply, vadd_vsub_assoc,
      (vsub_sub_vsub_cancel_right x z P.center).symm, smul_sub, two_smul, two_smul]
    abel
  have hcoord : P.basis.repr (AffineMap.homothety z (2 : ℝ) x -ᵥ P.center) i
      = 2 * P.basis.repr (x -ᵥ P.center) i - P.basis.repr (z -ᵥ P.center) i := by
    rw [hvsub]
    simp [map_sub, PiLp.smul_apply, PiLp.sub_apply]
  calc
    |P.basis.repr (AffineMap.homothety z (2 : ℝ) x -ᵥ P.center) i|
        = |2 * P.basis.repr (x -ᵥ P.center) i - P.basis.repr (z -ᵥ P.center) i| := by
          rw [hcoord]
    _ ≤ |2 * P.basis.repr (x -ᵥ P.center) i| + |P.basis.repr (z -ᵥ P.center) i| :=
          abs_sub _ _
    _ ≤ 2 * (P.thicknesses i : ℝ) + (P.thicknesses i : ℝ) := by
      refine add_le_add ?_ hz'
      calc
        |2 * P.basis.repr (x -ᵥ P.center) i|
            = 2 * |P.basis.repr (x -ᵥ P.center) i| := by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ 2 * (P.thicknesses i : ℝ) := mul_le_mul_of_nonneg_left hx' (by norm_num)
    _ = (3 : ℝ) * (P.thicknesses i : ℝ) := by
      ring

/-- Two prisms are `c`-comparable if one is contained in the other's `c`-dilation. -/
def IsCComparable (P : PrismNDim n E S) (Q : PrismNDim n E S) (c : ℝ≥0) : Prop :=
  P.carrier ⊆ (Q.dilation c).carrier ∨ Q.carrier ⊆ (P.dilation c).carrier

/-- Operator-norm closeness of linear isometries implies pointwise closeness on the vectors
of an orthonormal basis. -/
theorem linearIsometry_apply_basis_sub_le
    (b : OrthonormalBasis (Fin n) ℝ E) (F F' : E →ₗᵢ[ℝ] E) (j : Fin n) :
    ‖F' (b j) - F (b j)‖ ≤
      ‖F'.toContinuousLinearMap - F.toContinuousLinearMap‖ := by
  change ‖(F'.toContinuousLinearMap - F.toContinuousLinearMap) (b j)‖ ≤ _
  calc
    ‖(F'.toContinuousLinearMap - F.toContinuousLinearMap) (b j)‖
        ≤ ‖F'.toContinuousLinearMap - F.toContinuousLinearMap‖ * ‖b j‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖F'.toContinuousLinearMap - F.toContinuousLinearMap‖ := by
      rw [b.norm_eq_one, mul_one]

/-- Q is an r-perturbation of P if its center and each vector of its frame move by at
most r, while its half-widths may only shrink. -/
def IsRPerturbation (P Q : PrismNDim n E S) (r : ℝ≥0) : Prop :=
  dist Q.center P.center ≤ r ∧
    (∀ i, ‖P.basis i - Q.basis i‖ ≤ r) ∧
    ∀ i, Q.thicknesses i ≤ P.thicknesses i

namespace perturbation_subset_dilation

/-- The dimensional dilation factor that absorbs an r-perturbation of a prism whose
half-widths lie between r and 1. -/
@[nolint defsWithUnderscore]
def C (n : ℕ) : ℝ≥0 := ⟨(n : ℝ) + 2, by positivity⟩

@[simp]
theorem coe_C (n : ℕ) : (C n : ℝ) = (n : ℝ) + 2 := rfl

end perturbation_subset_dilation

/-- An r-perturbation of a prism with half-widths between r and 1 is contained in
the (n + 2)-fold dilation of the original prism. -/
theorem perturbation_subset_dilation {r : ℝ≥0} (P Q : PrismNDim n E S)
    (hr : ∀ i, r ≤ P.thicknesses i) (hP_le_one : ∀ i, P.thicknesses i ≤ 1)
    (hPQ : P.IsRPerturbation Q r) :
    Q.carrier ⊆ (P.dilation (perturbation_subset_dilation.C n)).carrier := by
  rintro x hx
  rcases hPQ with ⟨hcenter, hframe, hwidth⟩
  rw [(P.dilation (perturbation_subset_dilation.C n)).mem_carrier_iff]
  simp only [dilation, basis_mk', center_mk', thicknesses_mk']
  intro i
  have hxQ := (Q.mem_carrier_iff x).1 hx
  have hri : (r : ℝ) ≤ P.thicknesses i := by
    exact_mod_cast hr i
  have hnorm_vsub : ‖x -ᵥ Q.center‖ ≤ (n : ℝ) := by
    have hxball := Q.carrier_subset_closedBall hx
    rw [Metric.mem_closedBall, dist_eq_norm_vsub E] at hxball
    refine hxball.trans ?_
    calc
      ∑ j, (Q.thicknesses j : ℝ) ≤ ∑ j, (P.thicknesses j : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact_mod_cast hwidth j
      _ ≤ ∑ _j : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact_mod_cast hP_le_one j
      _ = (n : ℝ) := by simp
  have hframe_coord :
      |P.basis.repr (x -ᵥ Q.center) i| ≤
        |Q.basis.repr (x -ᵥ Q.center) i| + (r : ℝ) * ‖x -ᵥ Q.center‖ := by
    rw [P.basis.repr_apply_apply, Q.basis.repr_apply_apply]
    have hsplit :
        inner ℝ (P.basis i) (x -ᵥ Q.center) =
          inner ℝ (Q.basis i) (x -ᵥ Q.center) +
            inner ℝ (P.basis i - Q.basis i) (x -ᵥ Q.center) := by
      rw [inner_sub_left]
      ring
    rw [hsplit]
    calc
      |inner ℝ (Q.basis i) (x -ᵥ Q.center) +
          inner ℝ (P.basis i - Q.basis i) (x -ᵥ Q.center)|
          ≤ |inner ℝ (Q.basis i) (x -ᵥ Q.center)| +
              |inner ℝ (P.basis i - Q.basis i) (x -ᵥ Q.center)| := abs_add_le _ _
      _ ≤ |inner ℝ (Q.basis i) (x -ᵥ Q.center)| +
            ‖P.basis i - Q.basis i‖ * ‖x -ᵥ Q.center‖ :=
        by
          gcongr
          exact abs_real_inner_le_norm (P.basis i - Q.basis i) (x -ᵥ Q.center)
      _ ≤ |inner ℝ (Q.basis i) (x -ᵥ Q.center)| +
            (r : ℝ) * ‖x -ᵥ Q.center‖ := by
        gcongr
        exact hframe i
  have hcenter_coord :
      |P.basis.repr (Q.center -ᵥ P.center) i| ≤ (r : ℝ) := by
    rw [P.basis.repr_apply_apply]
    calc
      |inner ℝ (P.basis i) (Q.center -ᵥ P.center)|
          ≤ ‖P.basis i‖ * ‖Q.center -ᵥ P.center‖ := abs_real_inner_le_norm _ _
      _ = ‖Q.center -ᵥ P.center‖ := by rw [P.basis.norm_eq_one, one_mul]
      _ = dist Q.center P.center := by rw [dist_eq_norm_vsub E]
      _ ≤ (r : ℝ) := hcenter
  have hmul_norm :
      (r : ℝ) * ‖x -ᵥ Q.center‖ ≤ (r : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hnorm_vsub r.coe_nonneg
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hrn_le :
      (r : ℝ) * (n : ℝ) ≤ (P.thicknesses i : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hri hn_nonneg
  rw [← vsub_add_vsub_cancel x Q.center P.center, map_add, PiLp.add_apply]
  calc
    |P.basis.repr (x -ᵥ Q.center) i + P.basis.repr (Q.center -ᵥ P.center) i|
        ≤ |P.basis.repr (x -ᵥ Q.center) i| +
            |P.basis.repr (Q.center -ᵥ P.center) i| := abs_add_le _ _
    _ ≤ |Q.basis.repr (x -ᵥ Q.center) i| +
          (r : ℝ) * ‖x -ᵥ Q.center‖ + (r : ℝ) :=
      add_le_add hframe_coord hcenter_coord
    _ ≤ (Q.thicknesses i : ℝ) + (r : ℝ) * (n : ℝ) + (r : ℝ) := by
      exact add_le_add
        (add_le_add (hxQ i) hmul_norm) (le_refl (r : ℝ))
    _ ≤ (P.thicknesses i : ℝ) + (r : ℝ) * (n : ℝ) + (r : ℝ) := by
      gcongr
      exact_mod_cast hwidth i
    _ ≤ ((n : ℝ) + 2) * (P.thicknesses i : ℝ) := by
      nlinarith
    _ = ((perturbation_subset_dilation.C n * P.thicknesses i : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_mul, perturbation_subset_dilation.coe_C]

end PrismNDim

end
