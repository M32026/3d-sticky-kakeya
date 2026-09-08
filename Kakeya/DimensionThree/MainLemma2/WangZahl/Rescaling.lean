/-
The Wang--Zahl rescaling map `phi_W` and the rescaled family `U^W`.

Source: `blueprint/src/WZ2/250224e_K3.tex`
  * Definition `defnPhiW` (:837): the affine map `phi_W` taking the outer John
    ellipsoid of a convex set `W` to the unit ball, with the `j`-th axis sent
    to the `x_j` axis;
  * the definition immediately after (:845): `U[W]`, `U^W = phi_W(U[W])` and
    the transported shading `Y^W`;
  * Definition `defnOfCover` (:919): covers, `K`-almost partitioning covers,
    `K`-balanced covers;
  * Definition `defnConvexPrime` (:930) and Remark
    `remarksFollowingConvexWolffDefn` (:947): the Katz--Tao and Frostman Wolff
    constants `CKT`, `CFC`, `FS` of an arbitrary family of convex sets;
  * Definition :1001/:1004: `W` factors `U` from above / from below.

The `WangZahl` namespace previously had no rescaling map and no `U^W` at all,
which is why Definition `convexAtEveryScaleFromAssouadPaper` (:2257) and
Proposition `tubeTricotProp` (:2284) were not statable.  This file supplies the
vocabulary; the two source statements are in `TubeTrichotomy.lean`.
-/
module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.EToD
public import Kakeya.DimensionThree.Prism
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### The rescaling frame

Wang--Zahl Definition `defnPhiW` (:837) attaches to a convex set `W` the affine
map `phi_W` that takes the outer John ellipsoid of `W` to the unit ball, in
such a way that the `j`-th axis of that ellipsoid (ordered by increasing
length) goes to the `x_j` axis of `R^n`.

The John ellipsoid itself is not available in this project, and the source uses
it only through the two properties that (a) `phi_W` is affine with the
prescribed axis behaviour, and (b) `phi_W(W)` is comparable to the unit ball.
Every convex set the source actually rescales -- a `rho`-tube in Definition
:2257 and in clause (B) of :2284, an `a x b x 1` prism in clause (C) -- is a
*box*: it carries a distinguished centre, an orthonormal frame of axis
directions and three half-widths.  `Frame3` records exactly that data, and
`Frame3.map` is the corresponding `phi_W`, normalised so that the box goes to
the cube `[-1,1]^3` rather than to the unit ball.  The two normalisations
differ by the fixed linear map `sqrt 3`-scaling, which is inside the source's
own `~`.
-/

/-- A **rescaling frame** in `R^3`: a centre, an orthonormal frame of axis
directions, and three positive half-widths.  This is the data that Wang--Zahl
Definition `defnPhiW` (:837) reads off the outer John ellipsoid of a convex
set. -/
structure Frame3 where
  /-- The centre of the box. -/
  center : Space3
  /-- The axis directions, in the source's increasing-length order. -/
  basis : OrthonormalBasis (Fin 3) ℝ Space3
  /-- The half-widths along the axes. -/
  len : Fin 3 → ℝ
  /-- The half-widths are positive. -/
  len_pos : ∀ i, 0 < len i

namespace Frame3

variable (F : Frame3)

/-- The box cut out by a frame: the source's `W` in Definition `defnPhiW`. -/
def box : Set Space3 := {z | ∀ i, |F.basis.repr (z - F.center) i| ≤ F.len i}

/-- The diagonal part of `phi_W`, in the coordinates of the frame: the linear
map sending the `j`-th axis direction of the frame to `(len j)⁻¹` times the
`j`-th standard basis vector of `R^3`. -/
def linearMap : Space3 →ₗ[ℝ] Space3 where
  toFun v := (WithLp.toLp 2) fun i => F.basis.repr v i / F.len i
  map_add' v w := by
    ext i
    simp [add_div]
  map_smul' a v := by
    ext i
    simp [mul_div_assoc]

/-- **Wang--Zahl `phi_W`** (Definition `defnPhiW`, :837) for a box: the affine
map taking the centre to the origin and the `j`-th axis of the box to the
`x_j` axis, normalised so that the box becomes the cube `[-1,1]^3`. -/
def map (z : Space3) : Space3 := F.linearMap (z - F.center)

variable {F}

@[simp] theorem linearMap_apply (v : Space3) (i : Fin 3) :
    F.linearMap v i = F.basis.repr v i / F.len i := rfl

@[simp] theorem map_apply (z : Space3) (i : Fin 3) :
    F.map z i = F.basis.repr (z - F.center) i / F.len i := rfl

theorem mem_box_iff (z : Space3) :
    z ∈ F.box ↔ ∀ i, |F.basis.repr (z - F.center) i| ≤ F.len i := Iff.rfl

/-- `phi_W` takes the box exactly onto the cube `[-1,1]^3`; in particular
`phi_W(W)` is comparable to the unit ball, which is the only property of the
normalisation the source uses. -/
theorem mem_box_iff_map_mem_cube (z : Space3) :
    z ∈ F.box ↔ ∀ i, |F.map z i| ≤ 1 := by
  rw [mem_box_iff]
  refine forall_congr' fun i => ?_
  rw [map_apply, abs_div, abs_of_pos (F.len_pos i),
    div_le_one (F.len_pos i)]


/-! ### `phi_W` is an affine bijection, and how it moves volume -/

/-- The diagonal part of `phi_W` in standard coordinates. -/
def diagMap (len : Fin 3 → ℝ) : Space3 →ₗ[ℝ] Space3 where
  toFun v := (WithLp.toLp 2) fun i => v i / len i
  map_add' v w := by ext i; simp [add_div]
  map_smul' a v := by ext i; simp [mul_div_assoc]

@[simp] theorem diagMap_apply (len : Fin 3 → ℝ) (v : Space3) (i : Fin 3) :
    diagMap len v i = v i / len i := rfl

theorem det_diagMap {len : Fin 3 → ℝ} (h : ∀ i, len i ≠ 0) :
    LinearMap.det (diagMap len) = ∏ i, (len i)⁻¹ := by
  classical
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  rw [show LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (diagMap len)
      = Matrix.diagonal (fun i => (len i)⁻¹) from ?_]
  · exact Matrix.det_diagonal
  · ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply, OrthonormalBasis.repr_apply_apply]
    by_cases hij : i = j
    · subst hij
      rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, diagMap_apply]
      simp
    · rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, diagMap_apply]
      simp [hij]

/-- A linear isometry of `R^3` does not move volume, so its determinant has
absolute value one. -/
theorem abs_det_repr (b : OrthonormalBasis (Fin 3) ℝ Space3) :
    |LinearMap.det (b.repr.toLinearEquiv.toLinearMap : Space3 →ₗ[ℝ] Space3)| = 1 := by
  set f : Space3 →ₗ[ℝ] Space3 := b.repr.toLinearEquiv.toLinearMap with hf
  set s : Set Space3 := Metric.closedBall 0 1 with hs
  have hsm : MeasurableSet s := measurableSet_closedBall
  have h1 : volume (f '' s) = ENNReal.ofReal |LinearMap.det f| * volume s :=
    Measure.addHaar_image_linearMap volume f s
  have himg : (f '' s) = (b.repr.symm : Space3 → Space3) ⁻¹' s :=
    congrFun (Set.image_eq_preimage_of_inverse
      (fun x => b.repr.symm_apply_apply x) (fun x => b.repr.apply_symm_apply x)) s
  have h2 : volume (f '' s) = volume s := by
    rw [himg]
    exact (b.measurePreserving_repr_symm).measure_preimage hsm.nullMeasurableSet
  have hs0 : volume s ≠ 0 :=
    (Metric.measure_closedBall_pos volume (0 : Space3) one_pos).ne'
  have hstop : volume s ≠ ⊤ := measure_closedBall_lt_top.ne
  rw [h2] at h1
  have h3 : ENNReal.ofReal |LinearMap.det f| = 1 := by
    have h4 : ENNReal.ofReal |LinearMap.det f| * volume s = 1 * volume s := by
      rw [one_mul, ← h1]
    exact (ENNReal.mul_left_inj hs0 hstop).mp h4
  exact ENNReal.ofReal_eq_one.mp h3


theorem linearMap_eq_comp (F : Frame3) :
    F.linearMap = (diagMap F.len).comp
      (F.basis.repr.toLinearEquiv.toLinearMap : Space3 →ₗ[ℝ] Space3) := rfl

theorem det_linearMap_abs (F : Frame3) :
    |LinearMap.det F.linearMap| = ∏ i, (F.len i)⁻¹ := by
  have hlen : ∀ i, F.len i ≠ 0 := fun i => (F.len_pos i).ne'
  rw [linearMap_eq_comp, LinearMap.det_comp, abs_mul, det_diagMap hlen, abs_det_repr,
    mul_one, abs_of_pos]
  exact Finset.prod_pos fun i _ => inv_pos.mpr (F.len_pos i)

/-- **How `phi_W` moves volume** (the source's `|U^W| ~ |U|/|W|`, :839): the
image of any set under `phi_W` has volume scaled by the reciprocal product of
the half-widths of the frame. -/
theorem volume_image_map (F : Frame3) (A : Set Space3) :
    volume (F.map '' A) = ENNReal.ofReal (∏ i, (F.len i)⁻¹) * volume A := by
  have himg : F.map '' A = F.linearMap '' ((fun z => z + (-F.center)) '' A) := by
    rw [Set.image_image]
    rfl
  have htrans : volume ((fun z => z + (-F.center)) '' A) = volume A := by
    rw [Set.image_add_right, neg_neg]
    exact measure_preimage_add_right volume _ _
  rw [himg, Measure.addHaar_image_linearMap, htrans, det_linearMap_abs]

/-- `phi_W` is injective. -/
theorem map_injective (F : Frame3) : Function.Injective F.map := by
  intro z w hzw
  have h : ∀ i, F.basis.repr (z - F.center) i = F.basis.repr (w - F.center) i := by
    intro i
    have := congrFun (congrArg WithLp.ofLp hzw) i
    simp only [map_apply] at this
    exact (div_left_inj' (F.len_pos i).ne').mp this
  have h2 : F.basis.repr (z - F.center) = F.basis.repr (w - F.center) := by
    ext i; exact h i
  have h3 : z - F.center = w - F.center := by
    simpa using congrArg F.basis.repr.symm h2
  exact sub_left_injective h3

/-- `phi_W` as an affine map. -/
def affineMap (F : Frame3) : Space3 →ᵃ[ℝ] Space3 where
  toFun := F.map
  linear := F.linearMap
  map_vadd' p v := by
    show F.linearMap (v + p - F.center) = F.linearMap v + F.linearMap (p - F.center)
    rw [← map_add]
    congr 1
    abel

@[simp] theorem affineMap_apply (F : Frame3) (z : Space3) : F.affineMap z = F.map z := rfl

theorem convex_image (F : Frame3) {A : Set Space3} (hA : Convex ℝ A) :
    Convex ℝ (F.map '' A) := hA.affine_image F.affineMap

theorem convex_preimage (F : Frame3) {A : Set Space3} (hA : Convex ℝ A) :
    Convex ℝ (F.map ⁻¹' A) := hA.affine_preimage F.affineMap

/-- The volume factor of `phi_W`. -/
noncomputable def volumeFactor (F : Frame3) : ENNReal :=
  ENNReal.ofReal (∏ i, (F.len i)⁻¹)

theorem volumeFactor_ne_zero (F : Frame3) : F.volumeFactor ≠ 0 := by
  rw [volumeFactor, ← pos_iff_ne_zero, ENNReal.ofReal_pos]
  exact Finset.prod_pos fun i _ => inv_pos.mpr (F.len_pos i)

theorem volumeFactor_ne_top (F : Frame3) : F.volumeFactor ≠ ⊤ := ENNReal.ofReal_ne_top

theorem volume_image_map' (F : Frame3) (A : Set Space3) :
    volume (F.map '' A) = F.volumeFactor * volume A := volume_image_map F A


end Frame3


/-! ### The frame of a tube

The convex sets Wang--Zahl rescales in Definition
`convexAtEveryScaleFromAssouadPaper` (:2257) and in clause (B) of Proposition
`tubeTricotProp` (:2284) are `rho`-tubes.  A `rho`-tube is a box: its axes are
any two unit vectors orthogonal to its direction, together with the direction
itself, and its half-widths are `rho, rho, 1/2 + rho` (the source's `rho x rho
x 1`, with the endpoint balls included).
-/

/-- Any unit vector of `R^3` is the last vector of some orthonormal basis. -/
theorem exists_orthonormalBasis_last {v : Space3} (hv : ‖v‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ Space3, b 2 = v := by
  have hcard : Module.finrank ℝ Space3 = Fintype.card (Fin 3) := by simp [Space3]
  have hon : Orthonormal ℝ (Set.restrict ({2} : Set (Fin 3)) (fun _ : Fin 3 => v)) := by
    constructor
    · intro i; simpa using hv
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      exact absurd (Subtype.ext (hi.trans hj.symm)) hij
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨b, hb 2 rfl⟩

/-- A choice of orthonormal basis of `R^3` whose last vector is the direction
of the tube `T`. -/
def tubeAxes {ρ : NNReal} (T : Tube ρ Space3) : OrthonormalBasis (Fin 3) ℝ Space3 :=
  Classical.choose (exists_orthonormalBasis_last T.norm_direction)

theorem tubeAxes_two {ρ : NNReal} (T : Tube ρ Space3) : tubeAxes T 2 = T.direction :=
  Classical.choose_spec (exists_orthonormalBasis_last T.norm_direction)

/-- **The rescaling frame of a `rho`-tube**: centre at the midpoint of the
defining segment, axes as above, half-widths `rho, rho, 1/2 + rho`.  This is
the box the source's `phi_{T_rho}` normalises. -/
def tubeFrame3 {ρ : NNReal} (hρ : 0 < ρ) (T : Tube ρ Space3) : Frame3 where
  center := T.center
  basis := tubeAxes T
  len := ![(ρ : ℝ), (ρ : ℝ), 1 / 2 + (ρ : ℝ)]
  len_pos := by
    intro i
    have hρ' : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
    fin_cases i <;> simp <;> first | exact hρ | linarith

@[simp] theorem tubeFrame3_center {ρ : NNReal} (hρ : 0 < ρ) (T : Tube ρ Space3) :
    (tubeFrame3 hρ T).center = T.center := rfl

@[simp] theorem tubeFrame3_basis {ρ : NNReal} (hρ : 0 < ρ) (T : Tube ρ Space3) :
    (tubeFrame3 hρ T).basis = tubeAxes T := rfl

theorem tubeFrame3_len {ρ : NNReal} (hρ : 0 < ρ) (T : Tube ρ Space3) :
    (tubeFrame3 hρ T).len = ![(ρ : ℝ), (ρ : ℝ), 1 / 2 + (ρ : ℝ)] := rfl

/-- A `rho`-tube is contained in its own rescaling box; hence `phi_T` maps it
into the cube `[-1,1]^3`, which is the source's "`W^W` is comparable to the
unit ball". -/
theorem carrier_subset_tubeFrame3_box {ρ : NNReal} (hρ : 0 < ρ) (T : Tube ρ Space3) :
    T.carrier ⊆ (tubeFrame3 hρ T).box := by
  intro z hz
  rw [T.carrier_eq] at hz
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
  rw [Metric.mem_closedBall] at hzw
  rw [segment_eq_image' ℝ T.x T.y] at hw
  obtain ⟨t, ht, hwt⟩ := hw
  subst hwt
  intro i
  have hbnorm : ‖tubeAxes T i‖ = 1 := (tubeAxes T).orthonormal.1 i
  have hrepr : (tubeFrame3 hρ T).basis.repr (z - (tubeFrame3 hρ T).center) i
      = inner ℝ (tubeAxes T i) (z - T.center) := by
    rw [tubeFrame3_basis, tubeFrame3_center, OrthonormalBasis.repr_apply_apply]
  set w : Space3 := T.x + t • (T.y - T.x) with hwdef
  have hsplit : z - T.center = (z - w) + (w - T.center) := by abel
  have hmid : w - T.center = (t - 2⁻¹ : ℝ) • T.direction := by
    rw [hwdef, Tube.center, midpoint_eq_smul_add, Tube.direction, invOf_eq_inv]
    module
  have hzwnorm : ‖z - w‖ ≤ (ρ : ℝ) := by
    rw [← dist_eq_norm]; exact hzw
  have h1 : |inner ℝ (tubeAxes T i) (z - w)| ≤ (ρ : ℝ) := by
    calc |inner ℝ (tubeAxes T i) (z - w)| ≤ ‖tubeAxes T i‖ * ‖z - w‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ 1 * (ρ : ℝ) := by rw [hbnorm]; gcongr
      _ = (ρ : ℝ) := one_mul _
  rw [hrepr, hsplit, inner_add_right, hmid, real_inner_smul_right]
  have ht0 : |t - 2⁻¹| ≤ 2⁻¹ := by
    rw [abs_le]; constructor <;> [linarith [ht.1]; linarith [ht.2]]
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi3 with rfl | rfl | rfl
  · have h0 : inner ℝ (tubeAxes T 0) T.direction = 0 := by
      rw [← tubeAxes_two T]; exact (tubeAxes T).orthonormal.2 (by decide)
    rw [h0, mul_zero, add_zero, tubeFrame3_len]
    simpa using h1
  · have h0 : inner ℝ (tubeAxes T 1) T.direction = 0 := by
      rw [← tubeAxes_two T]; exact (tubeAxes T).orthonormal.2 (by decide)
    rw [h0, mul_zero, add_zero, tubeFrame3_len]
    simpa using h1
  · have h0 : inner ℝ (tubeAxes T 2) T.direction = 1 := by
      rw [← tubeAxes_two T, real_inner_self_eq_norm_sq, (tubeAxes T).orthonormal.1 2]
      norm_num
    rw [h0, mul_one, tubeFrame3_len]
    simp only [Matrix.cons_val]
    calc |inner ℝ (tubeAxes T 2) (z - w) + (t - 2⁻¹)|
        ≤ |inner ℝ (tubeAxes T 2) (z - w)| + |t - 2⁻¹| :=
          abs_add_le _ _
      _ ≤ (ρ : ℝ) + 2⁻¹ := by gcongr
      _ = 1 / 2 + (ρ : ℝ) := by ring

/-! ### The frame of a prism

Clause (C) of Proposition `tubeTricotProp` (:2284) rescales `a x b x 1`
prisms, so those need frames too.  A `Prism3D` already carries exactly the
data of a `Frame3`; note that the project's `Prism3D a b c` has *half*-widths
`a, b, c`, hence dimensions `2a x 2b x 2c` (this is the trap recorded in
`Plank.half_le_of_le_tube`), so the source's `a x b x 1` prism is the frame
with half-widths `a/2, b/2, 1/2`. -/

/-- The rescaling frame of a `Prism3D`. -/
def prismFrame3 {a b c : NNReal} {hab : a ≤ b} {hbc : b ≤ c} (ha : 0 < a)
    (P : Prism3D a b c hab hbc) : Frame3 where
  center := P.center
  basis := P.basis
  len := ![(a : ℝ), (b : ℝ), (c : ℝ)]
  len_pos := by
    intro i
    have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have hbc' : (b : ℝ) ≤ (c : ℝ) := by exact_mod_cast hbc
    fin_cases i <;> simp <;>
      first
        | exact ha
        | exact lt_of_lt_of_le ha hab
        | exact lt_of_lt_of_le ha (hab.trans hbc)

/-- A prism *is* the box of its frame: `phi_P` takes it exactly onto the cube
`[-1,1]^3`. -/
theorem carrier_eq_prismFrame3_box {a b c : NNReal} {hab : a ≤ b} {hbc : b ≤ c}
    (ha : 0 < a) (P : Prism3D a b c hab hbc) :
    (P.carrier : Set Space3) = (prismFrame3 ha P).box := by
  ext x
  rw [P.mem_carrier_iff, Frame3.mem_box_iff]
  refine forall_congr' fun i => ?_
  have hth : (P.thicknesses i : ℝ) = (prismFrame3 ha P).len i := by
    rw [P.thicknesses_eq]
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi with rfl | rfl | rfl <;> rfl
  rw [← hth]
  rfl

/-! ### Wolff constants of an arbitrary family of convex sets

Wang--Zahl Definition `defnConvexPrime` (:930) and Remark
`remarksFollowingConvexWolffDefn`(A) (:947) define `CKT`, `CFC` and `FS` for an
*arbitrary* collection `U` of convex subsets of `R^n`, not only for a family of
congruent `delta`-tubes.  That generality is exactly what the rescaled families
`U^W` need: `phi_W` of a `delta`-tube is not a tube, only a convex set.

The project's `katzTaoConvexWolffConstant`, `frostmanConvexWolffConstant` and
`frostmanSlabWolffConstant` are the tube specialisations, in which the source's
`sum_{U in U[W]} |U|` has been divided by the common tube volume `|T|`.  The
versions below are the source's literal, undivided ones; the two agree on tube
families (`katzTaoConvexWolffConstantSets_eq`,
`frostmanConvexWolffConstantSets_eq`, `frostmanSlabWolffConstantSets_eq`). -/

/-- `U[W]`, Wang--Zahl :845: the members of the family that are contained in
`W`. -/
def subfamilyIn {ι : Type u} (s : Finset ι) (U : ι → Set Space3) (W : Set Space3) :
    Finset ι :=
  @Finset.filter ι (fun i => U i ⊆ W) (Classical.decPred _) s

theorem mem_subfamilyIn {ι : Type u} {s : Finset ι} {U : ι → Set Space3}
    {W : Set Space3} {i : ι} : i ∈ subfamilyIn s U W ↔ i ∈ s ∧ U i ⊆ W :=
  @Finset.mem_filter ι (fun i => U i ⊆ W) (Classical.decPred _) s i

theorem subfamilyIn_subset {ι : Type u} (s : Finset ι) (U : ι → Set Space3)
    (W : Set Space3) : subfamilyIn s U W ⊆ s :=
  @Finset.filter_subset ι (fun i => U i ⊆ W) (Classical.decPred _) s

/-- `U^W`, Wang--Zahl :845: the carriers of `U[W]` pushed forward by
`phi_W`. -/
def rescaleCarriers {ι : Type u} (F : Frame3) (U : ι → Set Space3) : ι → Set Space3 :=
  fun i => F.map '' U i

@[simp] theorem rescaleCarriers_apply {ι : Type u} (F : Frame3) (U : ι → Set Space3)
    (i : ι) : rescaleCarriers F U i = F.map '' U i := rfl

/-- `Y^W`, the transported shading of Wang--Zahl :854.  It is `phi_W` of the
shading, and it remains inside the transported carrier. -/
theorem rescaleCarriers_shade_subset {ι : Type u} (F : Frame3) (U Y : ι → Set Space3)
    (hY : ∀ i, Y i ⊆ U i) (i : ι) :
    rescaleCarriers F Y i ⊆ rescaleCarriers F U i :=
  Set.image_mono (hY i)

/-- A Wang--Zahl slab is a convex test set: it is the intersection of the unit
ball with a closed thickening of an affine subspace. -/
def SlabTestSet.toConvexTestSet (W : SlabTestSet) : ConvexTestSet where
  carrier := W.carrier
  convex_carrier := by
    rw [SlabTestSet.carrier]
    exact (convex_closedBall (0 : Space3) 1).inter
      (W.plane.carrier.convex.cthickening _)

@[simp] theorem SlabTestSet.toConvexTestSet_carrier (W : SlabTestSet) :
    W.toConvexTestSet.carrier = W.carrier := rfl

/-- **Katz--Tao convex Wolff constant of an arbitrary family**, Wang--Zahl
Definition `defnConvexPrime`(A) (:934) with `W` the set of all convex subsets
of `R^3` (Remark :947). -/
noncomputable def katzTaoConvexWolffConstantSets {ι : Type u} (s : Finset ι)
    (U : ι → Set Space3) : ENNReal :=
  @sInf ENNReal _
    {C : ENNReal | 0 < C ∧ ∀ W : ConvexTestSet,
      ∑ i ∈ subfamilyIn s U W.carrier, volume (U i) ≤ C * volume W.carrier}

/-- **Frostman convex Wolff constant of an arbitrary family**, Wang--Zahl
Definition `defnConvexPrime`(B) (:941) with `W` the set of all convex subsets
of `R^3` (Remark :947). -/
noncomputable def frostmanConvexWolffConstantSets {ι : Type u} (s : Finset ι)
    (U : ι → Set Space3) : ENNReal :=
  @sInf ENNReal _
    {C : ENNReal | 0 < C ∧ ∀ W : ConvexTestSet,
      ∑ i ∈ subfamilyIn s U W.carrier, volume (U i) ≤
        C * volume W.carrier * ∑ i ∈ s, volume (U i)}

/-- **Frostman slab Wolff constant of an arbitrary family**, Wang--Zahl
Definition `defnConvexPrime`(B) (:941) with `W` the set of slabs
(Remark :947). -/
noncomputable def frostmanSlabWolffConstantSets {ι : Type u} (s : Finset ι)
    (U : ι → Set Space3) : ENNReal :=
  @sInf ENNReal _
    {C : ENNReal | 0 < C ∧ ∀ W : SlabTestSet,
      ∑ i ∈ subfamilyIn s U W.carrier, volume (U i) ≤
        C * volume W.carrier * ∑ i ∈ s, volume (U i)}

/-- Slabs are convex, so the Frostman slab constant never exceeds the Frostman
convex constant, for an arbitrary family: the general form of the source's
`FS <= CFC` (:2044). -/
theorem frostmanSlabWolffConstantSets_le_frostmanConvexWolffConstantSets
    {ι : Type u} (s : Finset ι) (U : ι → Set Space3) :
    frostmanSlabWolffConstantSets s U ≤ frostmanConvexWolffConstantSets s U := by
  rw [frostmanSlabWolffConstantSets, frostmanConvexWolffConstantSets]
  refine sInf_le_sInf ?_
  rintro C ⟨hC0, hC⟩
  exact ⟨hC0, fun W => hC W.toConvexTestSet⟩

/-! ### The tube specialisations agree with the general definitions -/

theorem sum_volume_subfamilyIn {δ : NNReal} {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) (W : Set Space3) :
    ∑ i ∈ subfamilyIn s (fun i => (T i).carrier) W, volume (T i).carrier
      = ((subfamilyIn s (fun i => (T i).carrier) W).card : ENNReal) * tubeVolume δ := by
  rw [Finset.sum_congr rfl (fun i _ => volume_carrier_eq_tubeVolume T i),
    Finset.sum_const, nsmul_eq_mul]

/-- The canonical **Frostman Convex Wolff constant** `CFC` of a family of
shaded `delta`-tubes: Wang--Zahl Definition `defnConvexPrime`(B) (:941), taken
over the convex test sets (Remark :952).

It is the same infimum as `frostmanSlabWolffConstant` with `SlabTestSet`
replaced by `ConvexTestSet`; as there, the source's
`sum_{U in U[W]} |U| <= C |W| sum_{U in U} |U|` has been divided through by the
common tube volume `|T|`. -/
noncomputable def frostmanConvexWolffConstant {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) : ENNReal :=
  @sInf ENNReal _
    {C : ENNReal | 0 < C ∧ ∀ W : ConvexTestSet,
      ((@Finset.filter ι (fun i => (T i).carrier ⊆ W.carrier)
        (Classical.decPred _) s).card : ENNReal) ≤
        C * volume W.carrier * (s.card : ENNReal)}

/-- `FS(T) <= CFC(T)`: the source's inequality at :2044
("`ell_W = FS(T^W) <= CFC(T^W)`").  Slabs are convex, so the convex constraint
set is contained in the slab constraint set and its infimum is the larger. -/
theorem frostmanSlabWolffConstant_le_frostmanConvexWolffConstant {δ : NNReal}
    {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3) :
    frostmanSlabWolffConstant s T ≤ frostmanConvexWolffConstant s T := by
  rw [frostmanSlabWolffConstant, frostmanConvexWolffConstant]
  refine sInf_le_sInf ?_
  rintro C ⟨hC0, hC⟩
  exact ⟨hC0, fun W => hC W.toConvexTestSet⟩

/-- The project's `CKT` for tube families is the source's general `CKT`
(Definition `defnConvexPrime`(A), :934) divided through by the common tube
volume `|T|`. -/
theorem katzTaoConvexWolffConstantSets_eq {δ : NNReal} (hδ : 0 < δ) {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) :
    katzTaoConvexWolffConstantSets s (fun i => (T i).carrier)
      = katzTaoConvexWolffConstant s T := by
  obtain ⟨hV0, hVtop⟩ := tubeVolume_pos_and_ne_top hδ
  rw [katzTaoConvexWolffConstantSets, katzTaoConvexWolffConstant]
  congr 1
  ext C
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => forall_congr' fun W => ?_
  rw [sum_volume_subfamilyIn s T W.carrier,
    ← ENNReal.le_div_iff_mul_le (Or.inl hV0.ne') (Or.inl hVtop),
    ENNReal.div_eq_inv_mul,
    show (tubeVolume δ)⁻¹ * (C * volume W.carrier)
      = C * volume W.carrier * (tubeVolume δ)⁻¹ from by ring]
  rfl

/-- The project's `CFC` for tube families is the source's general `CFC`
(Definition `defnConvexPrime`(B), :941) divided through by `|T|`. -/
theorem frostmanConvexWolffConstantSets_eq {δ : NNReal} (hδ : 0 < δ) {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) :
    frostmanConvexWolffConstantSets s (fun i => (T i).carrier)
      = frostmanConvexWolffConstant s T := by
  obtain ⟨hV0, hVtop⟩ := tubeVolume_pos_and_ne_top hδ
  rw [frostmanConvexWolffConstantSets, frostmanConvexWolffConstant]
  congr 1
  ext C
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => forall_congr' fun W => ?_
  rw [sum_volume_subfamilyIn s T W.carrier,
    Finset.sum_congr rfl (fun i (_ : i ∈ s) => volume_carrier_eq_tubeVolume T i),
    Finset.sum_const, nsmul_eq_mul,
    show C * volume W.carrier * ((s.card : ENNReal) * tubeVolume δ)
      = (C * volume W.carrier * (s.card : ENNReal)) * tubeVolume δ from by ring,
    ENNReal.mul_le_mul_iff_left hV0.ne' hVtop]
  rfl

/-- The project's `FS` for tube families is the source's general `FS`
(Definition `defnConvexPrime`(B) over slabs, :941/:947) divided through by
`|T|`. -/
theorem frostmanSlabWolffConstantSets_eq {δ : NNReal} (hδ : 0 < δ) {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) :
    frostmanSlabWolffConstantSets s (fun i => (T i).carrier)
      = frostmanSlabWolffConstant s T := by
  obtain ⟨hV0, hVtop⟩ := tubeVolume_pos_and_ne_top hδ
  rw [frostmanSlabWolffConstantSets, frostmanSlabWolffConstant]
  congr 1
  ext C
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => forall_congr' fun W => ?_
  rw [sum_volume_subfamilyIn s T W.carrier,
    Finset.sum_congr rfl (fun i (_ : i ∈ s) => volume_carrier_eq_tubeVolume T i),
    Finset.sum_const, nsmul_eq_mul,
    show C * volume W.carrier * ((s.card : ENNReal) * tubeVolume δ)
      = (C * volume W.carrier * (s.card : ENNReal)) * tubeVolume δ from by ring,
    ENNReal.mul_le_mul_iff_left hV0.ne' hVtop]
  rfl

/-- The convex test set obtained by pushing a convex test set forward by
`phi_W`. -/
def ConvexTestSet.push (F : Frame3) (V : ConvexTestSet) : ConvexTestSet where
  carrier := F.map '' V.carrier
  convex_carrier := F.convex_image V.convex_carrier

/-- The convex test set obtained by pulling a convex test set back by
`phi_W`. -/
def ConvexTestSet.pull (F : Frame3) (V : ConvexTestSet) : ConvexTestSet where
  carrier := F.map ⁻¹' V.carrier
  convex_carrier := F.convex_preimage V.convex_carrier

/-! ### How the Wolff constants of `U^W` relate to those of `U`

The source normalises `CKT` by `|W|` on both sides, so it is *invariant* under
the affine rescaling; `CFC` carries an extra copy of `sum |U|` on the right, so
it picks up exactly one factor of the volume Jacobian.  (Compare Remark
`remarksFollowingConvexWolffDefn`(C), :958, where the source discusses the
normalisation that makes these quantities transform naturally.)

Note that the family index set is *not* cut down here: the source's `U^W` is
this construction applied to `U[W]` (`subfamilyIn`), and these identities hold
for any index family. -/

/-- **`CKT` is invariant under `phi_W`.** -/
theorem katzTaoConvexWolffConstantSets_rescale {ι : Type u} (F : Frame3)
    (s : Finset ι) (U : ι → Set Space3) :
    katzTaoConvexWolffConstantSets s (rescaleCarriers F U)
      = katzTaoConvexWolffConstantSets s U := by
  have hc0 := F.volumeFactor_ne_zero
  have hctop := F.volumeFactor_ne_top
  have hfilter : ∀ V : Set Space3,
      subfamilyIn s (rescaleCarriers F U) V = subfamilyIn s U (F.map ⁻¹' V) := by
    intro V
    ext i
    simp only [mem_subfamilyIn, rescaleCarriers_apply]
    exact and_congr_right fun _ => Set.image_subset_iff
  have hsum : ∀ (V : Set Space3),
      ∑ i ∈ subfamilyIn s (rescaleCarriers F U) V, volume (rescaleCarriers F U i)
        = F.volumeFactor * ∑ i ∈ subfamilyIn s U (F.map ⁻¹' V), volume (U i) := by
    intro V
    rw [hfilter V, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => F.volume_image_map' (U i)
  rw [katzTaoConvexWolffConstantSets, katzTaoConvexWolffConstantSets]
  congr 1
  ext C
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun h V => ?_, fun h V => ?_⟩
  · have hV := h (ConvexTestSet.push F V)
    rw [hsum] at hV
    have hsub : subfamilyIn s U V.carrier ⊆
        subfamilyIn s U (F.map ⁻¹' (F.map '' V.carrier)) := by
      intro i hi
      obtain ⟨his, hiV⟩ := mem_subfamilyIn.mp hi
      exact mem_subfamilyIn.mpr ⟨his, hiV.trans (Set.subset_preimage_image _ _)⟩
    have h1 : F.volumeFactor * ∑ i ∈ subfamilyIn s U V.carrier, volume (U i)
        ≤ F.volumeFactor * ∑ i ∈ subfamilyIn s U (F.map ⁻¹' (F.map '' V.carrier)),
            volume (U i) :=
      mul_le_mul_left' (Finset.sum_le_sum_of_subset hsub) _
    have h2 : F.volumeFactor * ∑ i ∈ subfamilyIn s U V.carrier, volume (U i)
        ≤ C * (F.volumeFactor * volume V.carrier) := by
      refine h1.trans (hV.trans ?_)
      rw [show (ConvexTestSet.push F V).carrier = F.map '' V.carrier from rfl,
        F.volume_image_map']
    rw [show C * (F.volumeFactor * volume V.carrier)
        = F.volumeFactor * (C * volume V.carrier) from by ring] at h2
    exact (ENNReal.mul_le_mul_iff_right hc0 hctop).mp h2
  · have hV := h (ConvexTestSet.pull F V)
    have himg : F.volumeFactor * volume (F.map ⁻¹' V.carrier) ≤ volume V.carrier := by
      rw [← F.volume_image_map']
      exact measure_mono (Set.image_preimage_subset _ _)
    rw [hsum]
    calc F.volumeFactor * ∑ i ∈ subfamilyIn s U (F.map ⁻¹' V.carrier), volume (U i)
        ≤ F.volumeFactor * (C * volume (F.map ⁻¹' V.carrier)) :=
          mul_le_mul_left' hV _
      _ = C * (F.volumeFactor * volume (F.map ⁻¹' V.carrier)) := by ring
      _ ≤ C * volume V.carrier := by gcongr


/-- The constraint defining `CFC` transforms under `phi_W` by one factor of the
volume Jacobian: `C` is admissible for `U^W` exactly when `C * volumeFactor` is
admissible for `U`. -/
theorem frostmanCond_rescale_iff {ι : Type u} (F : Frame3) (s : Finset ι)
    (U : ι → Set Space3) (C : ENNReal) :
    (∀ W : ConvexTestSet, ∑ i ∈ subfamilyIn s (rescaleCarriers F U) W.carrier,
          volume (rescaleCarriers F U i) ≤
        C * volume W.carrier * ∑ i ∈ s, volume (rescaleCarriers F U i))
      ↔ (∀ W : ConvexTestSet, ∑ i ∈ subfamilyIn s U W.carrier, volume (U i) ≤
          C * F.volumeFactor * volume W.carrier * ∑ i ∈ s, volume (U i)) := by
  have hc0 := F.volumeFactor_ne_zero
  have hctop := F.volumeFactor_ne_top
  have hfilter : ∀ V : Set Space3,
      subfamilyIn s (rescaleCarriers F U) V = subfamilyIn s U (F.map ⁻¹' V) := by
    intro V
    ext i
    simp only [mem_subfamilyIn, rescaleCarriers_apply]
    exact and_congr_right fun _ => Set.image_subset_iff
  have hsum : ∀ V : Set Space3,
      ∑ i ∈ subfamilyIn s (rescaleCarriers F U) V, volume (rescaleCarriers F U i)
        = F.volumeFactor * ∑ i ∈ subfamilyIn s U (F.map ⁻¹' V), volume (U i) := by
    intro V
    rw [hfilter V, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => F.volume_image_map' (U i)
  have hall : ∑ i ∈ s, volume (rescaleCarriers F U i)
      = F.volumeFactor * ∑ i ∈ s, volume (U i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => F.volume_image_map' (U i)
  constructor
  · intro h V
    have hV := h (ConvexTestSet.push F V)
    rw [hsum, hall, show (ConvexTestSet.push F V).carrier = F.map '' V.carrier from rfl,
      F.volume_image_map'] at hV
    have hsub : subfamilyIn s U V.carrier ⊆
        subfamilyIn s U (F.map ⁻¹' (F.map '' V.carrier)) := fun i hi => by
      obtain ⟨his, hiV⟩ := mem_subfamilyIn.mp hi
      exact mem_subfamilyIn.mpr ⟨his, hiV.trans (Set.subset_preimage_image _ _)⟩
    have h2 : F.volumeFactor * ∑ i ∈ subfamilyIn s U V.carrier, volume (U i) ≤
        F.volumeFactor * (C * F.volumeFactor * volume V.carrier *
          ∑ i ∈ s, volume (U i)) := by
      refine le_trans (mul_le_mul_left' (Finset.sum_le_sum_of_subset hsub) _) ?_
      refine hV.trans (le_of_eq ?_)
      ring
    exact (ENNReal.mul_le_mul_iff_right hc0 hctop).mp h2
  · intro h V
    have hV := h (ConvexTestSet.pull F V)
    rw [show (ConvexTestSet.pull F V).carrier = F.map ⁻¹' V.carrier from rfl] at hV
    have himg : F.volumeFactor * volume (F.map ⁻¹' V.carrier) ≤ volume V.carrier := by
      rw [← F.volume_image_map']
      exact measure_mono (Set.image_preimage_subset _ _)
    rw [hsum, hall]
    calc F.volumeFactor * ∑ i ∈ subfamilyIn s U (F.map ⁻¹' V.carrier), volume (U i)
        ≤ F.volumeFactor * (C * F.volumeFactor * volume (F.map ⁻¹' V.carrier) *
            ∑ i ∈ s, volume (U i)) := mul_le_mul_left' hV _
      _ = C * (F.volumeFactor * volume (F.map ⁻¹' V.carrier)) *
            (F.volumeFactor * ∑ i ∈ s, volume (U i)) := by ring
      _ ≤ C * volume V.carrier * (F.volumeFactor * ∑ i ∈ s, volume (U i)) := by gcongr

/-- **`CFC` picks up exactly one factor of the volume Jacobian under `phi_W`:**
`CFC(U^W) * volumeFactor = CFC(U)`.  Together with
`katzTaoConvexWolffConstantSets_rescale` this is the transfer rule the source
uses whenever it applies an estimate to a rescaled family and "undoes the
scaling `phi_W`". -/
theorem frostmanConvexWolffConstantSets_rescale {ι : Type u} (F : Frame3)
    (s : Finset ι) (U : ι → Set Space3) :
    frostmanConvexWolffConstantSets s (rescaleCarriers F U) * F.volumeFactor
      = frostmanConvexWolffConstantSets s U := by
  have hc0 := F.volumeFactor_ne_zero
  have hctop := F.volumeFactor_ne_top
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    rintro C' ⟨hC'0, hC'⟩
    have hmem : C' / F.volumeFactor ∈
        {C : ENNReal | 0 < C ∧ ∀ W : ConvexTestSet,
          ∑ i ∈ subfamilyIn s (rescaleCarriers F U) W.carrier,
              volume (rescaleCarriers F U i) ≤
            C * volume W.carrier * ∑ i ∈ s, volume (rescaleCarriers F U i)} := by
      refine ⟨ENNReal.div_pos hC'0.ne' hctop, ?_⟩
      refine (frostmanCond_rescale_iff F s U _).mpr ?_
      rw [ENNReal.div_mul_cancel hc0 hctop]
      exact hC'
    calc frostmanConvexWolffConstantSets s (rescaleCarriers F U) * F.volumeFactor
        ≤ (C' / F.volumeFactor) * F.volumeFactor := by
          exact mul_le_mul_right' (sInf_le hmem) _
      _ = C' := ENNReal.div_mul_cancel hc0 hctop
  · rw [← ENNReal.div_le_iff_le_mul (Or.inl hc0) (Or.inl hctop)]
    refine le_sInf ?_
    rintro C ⟨hC0, hC⟩
    rw [ENNReal.div_le_iff_le_mul (Or.inl hc0) (Or.inl hctop)]
    refine sInf_le ⟨?_, (frostmanCond_rescale_iff F s U C).mp hC⟩
    rw [pos_iff_ne_zero]
    exact mul_ne_zero hC0.ne' hc0


end

end Kakeya.WangZahl
