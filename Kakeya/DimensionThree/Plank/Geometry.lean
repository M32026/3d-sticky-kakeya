/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody
public import Kakeya.Pigeonhole
public import Kakeya.DimensionThree.Plank
public import Kakeya.DimensionThree.Slab.Basic
public import Kakeya.DimensionThree.Volume
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Plank geometry for GWZ Lemma 6.11/6.13

This file contains the foundational plank geometry, organized so that
each file stays under 800 lines. It contains the plane-angle between prisms, the thickened plank and
containing slab, the slab subfamily, the thickened-plank ensemble and its representative
(`ThickenedRepr`) with the constant-multiplicity pigeonhole, and the slab assignment. The remaining
parts are chained via `public import` and re-exported by the downstream
representative-selection and reduction modules.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real

noncomputable section

namespace Prism3D

variable {a b c : NNReal} {a_le_b : a ≤ b} {b_le_c : b ≤ c}

/-- The angle between the spanning planes (`longPlane`) of two `Prism3D`s, i.e. the angle
`∠(TP₁, TP₂)` between their tangent planes. Since `basis 0` is a unit normal to `longPlane`
(`longPlane_eq_orthocomp`), this is the dihedral angle `arccos |⟪n₁, n₂⟫|`, valued in `[0, π/2]`. -/
def planeAngle {a' b' c' : NNReal} {a_le_b' : a' ≤ b'} {b_le_c' : b' ≤ c'}
    (P : Prism3D a b c a_le_b b_le_c) (Q : Prism3D a' b' c' a_le_b' b_le_c') : ℝ :=
  Real.arccos |inner ℝ (P.basis 0) (Q.basis 0)|

variable {a' b' c' : NNReal} {a_le_b' : a' ≤ b'} {b_le_c' : b' ≤ c'}
  (P : Prism3D a b c a_le_b b_le_c) (Q : Prism3D a' b' c' a_le_b' b_le_c')

theorem planeAngle_nonneg : 0 ≤ P.planeAngle Q :=
  Real.arccos_nonneg _

theorem planeAngle_le_pi_div_two : P.planeAngle Q ≤ π / 2 :=
  Real.arccos_le_pi_div_two.2 (abs_nonneg _)

theorem planeAngle_comm : P.planeAngle Q = Q.planeAngle P := by
  rw [planeAngle, planeAngle, real_inner_comm]

/-- The angle between the spanning planes of two `Prism3D`s, valued in `ℝ≥0`. -/
def planeAngleNN {a' b' c' : NNReal} {a_le_b' : a' ≤ b'} {b_le_c' : b' ≤ c'}
    (P : Prism3D a b c a_le_b b_le_c) (Q : Prism3D a' b' c' a_le_b' b_le_c') : ℝ≥0 :=
  (P.planeAngle Q).toNNReal

end Prism3D

namespace ShadedPlank

open MeasureTheory

/-- The exact volume of a shaded plank's carrier: `8ab`, since the third half-width is `1`.
Because `ShadedPlank` bundles the plank and the shading over a *shared* `ConvexSpaceBody`, this is
simultaneously the plank volume and the shading's carrier volume — the coherence that an unbundled
`(P, Y)` pair has to assume as an extra hypothesis. -/
theorem volume_carrier {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    (Y : ShadedPlank a b hab hb1) :
    volume Y.carrier = 8 * (a : ENNReal) * (b : ENNReal) := by
  rw [show (Y.carrier : Set (EuclideanSpace ℝ (Fin 3))) = Y.plank.carrier from rfl,
    Prism3D.volume_carrier Y.plank]
  simp

end ShadedPlank

/-! ## The slab subfamily and the thickened-plank ensemble (extra6) -/

namespace Plank

open MeasureTheory
open scoped NNReal

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}

/-- The genuine typed `θb × b × 1` plank used as a standard thickened representative.

This is only a readability alias for the corresponding `Plank`; it carries no additional data. -/
abbrev ThickenedPlank (θ b : ℝ≥0) (hθ1 : θ ≤ 1) (hb1 : b ≤ 1) : Type :=
  Plank (θ * b) b (by simpa using mul_le_mul_left hθ1 b) hb1

/-- The fixed ambient window used throughout Section 6.  Its precise radius is immaterial; the
constant `4` agrees with the normalisation used by the plank estimates. -/
def windowRadius : ℝ := 4

/-- A family of planks contained in the fixed Section 6 working window. -/
def IsWindowedFamily (s : Finset ι) (P : ι → Plank a b hab hb1) : Prop :=
  ∀ i ∈ s, (P i).carrier ⊆
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) windowRadius

/-- **Unit-ball centres give a windowed family.**  This is the bridge between the paper's
normalisation, which places the plank *centres* in the unit ball, and the working window used
throughout Section 6.

The repository records prism dimensions as half-axis lengths, so an `a × b × 1` plank is contained
in the ball of radius `a + b + 1` about its own centre (`PrismNDim.carrier_subset_closedBall`), and
`a ≤ b ≤ 1` bounds that by `3`.  The triangle inequality then puts the whole plank inside the ball
of radius `1 + 3 = 4 = Plank.windowRadius` about the origin. -/
theorem isWindowedFamily_of_dist_center_le_one (s : Finset ι) (P : ι → Plank a b hab hb1)
    (hcenter : ∀ i ∈ s, dist (P i).center (0 : EuclideanSpace ℝ (Fin 3)) ≤ 1) :
    IsWindowedFamily s P := by
  intro i hi x hx
  rw [Metric.mem_closedBall]
  have hball := (P i).carrier_subset_closedBall hx
  rw [Metric.mem_closedBall] at hball
  have hthick : ∀ k : Fin 3, (((P i).thicknesses k : ℝ)) = ((![a, b, (1:ℝ≥0)] k : ℝ≥0) : ℝ) := by
    intro k
    rw [(P i).thicknesses_eq]
  have hsum : ∑ k : Fin 3, (((P i).thicknesses k : ℝ)) ≤ 3 := by
    rw [Fin.sum_univ_three]
    rw [hthick 0, hthick 1, hthick 2]
    simp [Matrix.cons_val_zero]
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have hb1' : (b : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hb1
    linarith
  have htri := dist_triangle x ((P i).center) (0 : EuclideanSpace ℝ (Fin 3))
  rw [windowRadius]
  linarith [hball, hsum, htri, hcenter i hi]

/-- The **thickened plank** `P_θ` of GWZ Definition 6.10 (`def:thickenedPlankFamily`),
modelled as the genuine `θb × b × 1` prism sharing `P`'s center and axes. When `a ≤ θ b`
(i.e. `θ ≥ a/b`) this is the smallest plank-aligned prism of those dimensions containing `P`.
The blueprint's `θb`-neighbourhood `N_{θb}(P)` is comparable to this prism, so using it loses
only a constant factor, absorbed into the comparability constant `cThk` of `ThickenedRepr`. -/
def thickened (P : Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1) :
    ThickenedPlank θ b hθ1 hb1 where
  toPrismNDim := PrismNDim.mk' P.center P.basis ![θ * b, b, 1]
  thicknesses_eq := PrismNDim.thicknesses_mk' _ _ _

@[simp] theorem thickened_center (P : Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1) :
    (P.thickened θ hθ1).center = P.center := rfl

@[simp] theorem thickened_basis (P : Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1) :
    (P.thickened θ hθ1).basis = P.basis := rfl

/-- The thickened plank contains the original plank, provided `a ≤ θ b` (i.e. `θ ≥ a/b`). -/
theorem subset_thickened (P : Plank a b hab hb1) {θ : ℝ≥0} (hθa : a ≤ θ * b) (hθ1 : θ ≤ 1) :
    (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ (P.thickened θ hθ1).carrier := by
  intro x hx
  rw [(P.thickened θ hθ1).mem_carrier_iff]
  rw [P.mem_carrier_iff] at hx
  intro i
  refine (hx i).trans ?_
  rw [P.thicknesses_eq, (P.thickened θ hθ1).thicknesses_eq]
  fin_cases i
  · exact_mod_cast hθa
  · simp
  · simp

/-- Compatibility form of `subset_thickened` with the scale hypothesis ordered after `hθ1`. -/
theorem carrier_subset_thickened (P : Plank a b hab hb1) {θ : ℝ≥0} (hθ1 : θ ≤ 1)
    (haθb : a ≤ θ * b) :
    (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ (P.thickened θ hθ1).carrier :=
  P.subset_thickened haθb hθ1

/-- The closed `θb`-neighbourhood of a plank, as used in the non-concentration hypothesis of
GWZ Lemma 6.4.

This is strictly larger than the prism `P.thickened θ`, which has the same centre and basis but
half-widths `(θb, b, 1)`: the neighbourhood also grows by `θb` along the two long axes. The
non-concentration hypothesis of Lemma 6.4 must use the neighbourhood, since counting only planks
inside the smaller prism would omit configurations that the lemma has to exclude, such as a plank
parallel to `P` and shifted slightly along the long axis. -/
def thickenedNbhd (P : Plank a b hab hb1) (θ : ℝ≥0) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  Metric.cthickening ((θ * b : ℝ≥0) : ℝ) P.carrier

/-- The volume of the thickened plank `P_θ`, a `θb × b × 1` prism:
`|P_θ| = 8 · θ · b · b` (the `8 = 2³` is the `Prism3D` normalisation factor). -/
theorem volume_thickened (P : Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1) :
    volume (P.thickened θ hθ1).carrier = 8 * (θ : ENNReal) * b * b := by
  rw [Prism3D.volume_carrier (P.thickened θ hθ1)]
  push_cast
  ring

/-- A thickened plank is never essentially distinct from itself (positive-volume case).
Used to guarantee that the maximal essentially-distinct family in `exists_thickenedRepr`
does not contain any duplicate indices via `sel`. -/
theorem not_isEssentiallyDistinct_thickened_self (P : Plank a b hab hb1) {θ : ℝ≥0} (hθ1 : θ ≤ 1)
    (hθ0 : 0 < θ) (hb0 : 0 < b) :
    ¬ PrismNDim.IsEssentiallyDistinct ((P.thickened θ hθ1).toPrismNDim)
        ((P.thickened θ hθ1).toPrismNDim) := by
  intro h
  unfold PrismNDim.IsEssentiallyDistinct at h
  unfold _root_.IsEssentiallyDistinct at h
  have h_simplified : volume ((P.thickened θ hθ1).toPrismNDim).carrier ≤
      (1 / 2 : ENNReal) * volume ((P.thickened θ hθ1).toPrismNDim).carrier := by
    simpa [Set.inter_self, max_self] using h
  set v := volume ((P.thickened θ hθ1).toPrismNDim).carrier with hv_def
  have hcar : ((P.thickened θ hθ1).toPrismNDim).carrier = (P.thickened θ hθ1).carrier := rfl
  have hvol : v = 8 * (θ : ENNReal) * b * b := by
    dsimp [v]
    rw [hcar, Plank.volume_thickened P θ hθ1]
  have htemp : (1 / 2 : ENNReal) * v = v / 2 := by
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, mul_assoc, one_mul, mul_comm]
  rw [htemp] at h_simplified
  have hpos : v ≠ 0 := by
    rw [hvol]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hθ0.ne.symm))
        (by exact_mod_cast hb0.ne.symm)) (by exact_mod_cast hb0.ne.symm)
  have hfin : v ≠ ⊤ := by
    rw [hvol]
    repeat' apply ENNReal.mul_ne_top
    · simp
    · exact ENNReal.coe_ne_top
    · exact ENNReal.coe_ne_top
    · exact ENNReal.coe_ne_top
  have hlt : v / 2 < v := ENNReal.half_lt_self hpos hfin
  exact (lt_irrefl _) (h_simplified.trans_lt hlt)

/-- The thickened-plank volume identity of `multiplicityAlgebraHelpers` (1), in
division-free form: `a · |P_θ| = θb · |P|`. Equivalently `|P_θ| = (θb/a)·|P|` when
`a > 0`. Both sides equal `8·a·θ·b²`, so no positivity hypothesis is needed. -/
theorem mul_volume_thickened (P : Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1) :
    (a : ENNReal) * volume (P.thickened θ hθ1).carrier
      = (θ : ENNReal) * b * volume P.carrier := by
  rw [volume_thickened, Prism3D.volume_carrier P]
  push_cast
  ring

/-! ### The containing slab of a plank

The slab analogue of `Plank.thickened`. Where `thickened` widens an `a × b × 1` plank to the
`θb × b × 1` prism (short axis `a ↦ θb`), `toSlab` widens it to the genuine `θ × 1 × 1` slab
(short axis `a ↦ θ`, middle axis `b ↦ 1`), sharing the plank's center and axes. It exhibits,
for each plank, a concrete `θ × 1 × 1` slab containing it with induced slab angle `0`. -/

/-- The **containing slab** `S(P, θ)` of a plank `P`: the genuine `θ × 1 × 1` slab sharing `P`'s
center and orthonormal axes (thicknesses `![θ, 1, 1]`). This is the slab analogue of
`Plank.thickened`; when `a ≤ θ` it contains `P` (`subset_toSlab`) and its induced slab angle with
`P` is `0` (`angle_toSlab`). -/
def toSlab (P : Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1) : Slab θ hθ1 where
  toPrismNDim := PrismNDim.mk' P.center P.basis ![θ, 1, 1]
  thicknesses_eq := PrismNDim.thicknesses_mk' _ _ _

@[simp] theorem toSlab_center (P : Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1) :
    (P.toSlab θ hθ1).center = P.center := rfl

@[simp] theorem toSlab_basis (P : Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1) :
    (P.toSlab θ hθ1).basis = P.basis := rfl

/-- The plank is contained in its containing slab `S(P, θ)`, provided `a ≤ θ` (the analogue of
`Plank.subset_thickened`). -/
theorem subset_toSlab (P : Plank a b hab hb1) {θ : ℝ≥0} (hθa : a ≤ θ) (hθ1 : θ ≤ 1) :
    (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ (P.toSlab θ hθ1).carrier := by
  intro x hx
  rw [(P.toSlab θ hθ1).mem_carrier_iff]
  rw [P.mem_carrier_iff] at hx
  intro i
  refine (hx i).trans ?_
  rw [P.thicknesses_eq, (P.toSlab θ hθ1).thicknesses_eq, NNReal.coe_le_coe]
  fin_cases i
  · exact hθa
  · exact hb1
  · exact le_refl _

/-- The induced slab angle of a plank with its containing slab is `0`: they share the short
normal `basis 0`, so `∠(TP, T S(P, θ)) = 0`. -/
@[simp] theorem angle_toSlab (P : Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1) :
    Prism3D.angle P (P.toSlab θ hθ1) = 0 := by
  rw [Prism3D.angle_def, toSlab_basis, real_inner_self_eq_norm_sq, P.basis.norm_eq_one,
    one_pow, abs_one, Real.arccos_one]

/-- The volume of the containing slab `S(P, θ)`, a `θ × 1 × 1` slab: `|S(P, θ)| = 8 · θ`
(the analogue of `Plank.volume_thickened`). -/
theorem volume_toSlab (P : Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1) :
    volume (P.toSlab θ hθ1).carrier = 8 * (θ : ENNReal) :=
  Slab.volume_carrier (P.toSlab θ hθ1)

/-- **A dilated thickening sits inside the correspondingly dilated containing slab.** The
thickening `P_θ` (`θb × b × 1`) and the containing slab `S(P,θ)` (`θ × 1 × 1`) share `P`'s centre
and axes, and `b ≤ 1`, so for `c ≤ C` the `c`-dilation of the thickening lies in the `C`-dilation of
the slab: coordinatewise `c·θb ≤ C·θ`, `c·b ≤ C`, `c ≤ C`. This is the containment that turns the
directed `ThickenedRepr.repr_subset_thickened` field into fibre-slab carrier control. -/
theorem thickened_dilation_subset_toSlab_dilation (P : Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1)
    {c C : ℝ≥0} (hcC : c ≤ C) :
    (((P.thickened θ hθ1).toPrismNDim.dilation c).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) ⊆
      ((P.toSlab θ hθ1).toPrismNDim.dilation C).carrier := by
  intro x hx
  rw [PrismNDim.mem_carrier_iff] at hx
  simp only [PrismNDim.dilation_basis, thickened_basis, PrismNDim.dilation_center,
    thickened_center, vsub_eq_sub, map_sub, PiLp.sub_apply, PrismNDim.dilation_thicknesses,
    NNReal.coe_mul] at hx
  rw [PrismNDim.mem_carrier_iff]
  simp only [PrismNDim.dilation_basis, toSlab_basis, PrismNDim.dilation_center, toSlab_center,
    vsub_eq_sub, map_sub, PiLp.sub_apply, PrismNDim.dilation_thicknesses, NNReal.coe_mul]
  intro k
  have hcoord := hx k
  refine hcoord.trans ?_
  simp only [Plank.thickened, Plank.toSlab, PrismNDim.thicknesses_mk']
  have hb1' : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have hcC' : (c : ℝ) ≤ (C : ℝ) := by exact_mod_cast hcC
  have hθ_nonneg : 0 ≤ (θ : ℝ) := NNReal.coe_nonneg _
  have hb_nonneg : 0 ≤ (b : ℝ) := NNReal.coe_nonneg _
  have hc_nonneg : 0 ≤ (c : ℝ) := NNReal.coe_nonneg _
  have hC_nonneg : 0 ≤ (C : ℝ) := NNReal.coe_nonneg _
  fin_cases k
  · -- k = 0: c*(θ*b) ≤ C*θ
    have htemp : (c : ℝ) * ((θ : ℝ) * (b : ℝ)) ≤ (C : ℝ) * (θ : ℝ) := by
      have hcb_le_C : (c : ℝ) * (b : ℝ) ≤ (C : ℝ) := by
        calc
          (c : ℝ) * (b : ℝ) ≤ (C : ℝ) * (b : ℝ) := mul_le_mul_of_nonneg_right hcC' hb_nonneg
          _ ≤ (C : ℝ) := by
            simpa [mul_one] using mul_le_mul_of_nonneg_left hb1' hC_nonneg
      calc
        (c : ℝ) * ((θ : ℝ) * (b : ℝ)) = (θ : ℝ) * ((c : ℝ) * (b : ℝ)) := by ring
        _ ≤ (θ : ℝ) * (C : ℝ) := mul_le_mul_of_nonneg_left hcb_le_C hθ_nonneg
        _ = (C : ℝ) * (θ : ℝ) := mul_comm _ _
    simpa [Matrix.cons_val_zero, Matrix.head_cons] using htemp
  · -- k = 1: c*b ≤ C*1
    have htemp : (c : ℝ) * (b : ℝ) ≤ (C : ℝ) * (1 : ℝ) := by
      calc
        (c : ℝ) * (b : ℝ) ≤ (C : ℝ) * (b : ℝ) := mul_le_mul_of_nonneg_right hcC' hb_nonneg
        _ ≤ (C : ℝ) := by
          simpa [mul_one] using mul_le_mul_of_nonneg_left hb1' hC_nonneg
        _ = (C : ℝ) * (1 : ℝ) := by ring
    simpa [Matrix.cons_val_one, Matrix.head_cons] using htemp
  · -- k = 2: c*1 ≤ C*1, i.e. c ≤ C
    have htemp : (c : ℝ) * (1 : ℝ) ≤ (C : ℝ) * (1 : ℝ) := by
      simpa using hcC'
    simpa using htemp

open scoped Classical in
/-- The **slab subfamily** `𝒫_S` of GWZ §6 (`def:plankInSlabFamily`, see also `def:PS`):
the indices `i ∈ s` whose plank `P i` is contained in the slab `S` and whose tangent plane makes
angle at most `θ` with that of `S`. -/
def inSlabFamily (s : Finset ι) (V : ι → Plank a b hab hb1)
    {θ : ℝ≥0} {hθ : θ ≤ 1} (S : Slab θ hθ) : Finset ι :=
  {i ∈ s | (V i).carrier ⊆ S.carrier ∧ Prism3D.angle (V i) S ≤ (θ : ℝ)}

theorem mem_inSlabFamily {s : Finset ι} {V : ι → Plank a b hab hb1}
    {θ : ℝ≥0} {hθ : θ ≤ 1} {S : Slab θ hθ} {i : ι} :
    i ∈ inSlabFamily s V S ↔
      i ∈ s ∧ (V i).carrier ⊆ S.carrier ∧ Prism3D.angle (V i) S ≤ (θ : ℝ) := by
  classical
  simp [inSlabFamily]

theorem inSlabFamily_subset {s : Finset ι} {V : ι → Plank a b hab hb1}
    {θ : ℝ≥0} {hθ : θ ≤ 1} {S : Slab θ hθ} : inSlabFamily s V S ⊆ s := by
  intro i hi; exact (mem_inSlabFamily.mp hi).1

/-- Every plank `V i` lies in the slab subfamily of its own containing slab `S(V i, θ)`
(when `a ≤ θ`): the witness that each plank is captured by a concrete `θ × 1 × 1` slab, via
`Plank.toSlab` and `angle_toSlab`. -/
theorem mem_inSlabFamily_toSlab {s : Finset ι} {V : ι → Plank a b hab hb1}
    {i : ι} (hi : i ∈ s) {θ : ℝ≥0} (hθa : a ≤ θ) (hθ1 : θ ≤ 1) :
    i ∈ inSlabFamily s V ((V i).toSlab θ hθ1) := by
  rw [mem_inSlabFamily]
  exact ⟨hi, (V i).subset_toSlab hθa hθ1, by rw [angle_toSlab]; positivity⟩

open scoped Classical in
/-- The **controlled slab subfamily** `𝒫_S^{Cset,Cang}`: the faithful relaxation of `inSlabFamily`
by a fixed dilation `Cset ≥ 1` and a fixed angle constant `Cang ≥ 1`.  A plank `P i` belongs when
its carrier lies in the `Cset`-dilation of `S` and its induced plank angle with `S` is at most
`Cang · θ`.  The paper suppresses these fixed comparability constants; the exact family is the
special case `Cset = Cang = 1` (`inSlabFamily_subset_inSlabFamilyC`). -/
def inSlabFamilyC (Cset Cang : ℝ≥0) (s : Finset ι) (V : ι → Plank a b hab hb1)
    {θ : ℝ≥0} {hθ : θ ≤ 1} (S : Slab θ hθ) : Finset ι :=
  {i ∈ s | (V i).carrier ⊆ (S.toPrismNDim.dilation Cset).carrier ∧
    Prism3D.angle (V i) S ≤ (Cang : ℝ) * (θ : ℝ)}

theorem mem_inSlabFamilyC {Cset Cang : ℝ≥0} {s : Finset ι} {V : ι → Plank a b hab hb1}
    {θ : ℝ≥0} {hθ : θ ≤ 1} {S : Slab θ hθ} {i : ι} :
    i ∈ inSlabFamilyC Cset Cang s V S ↔
      i ∈ s ∧ (V i).carrier ⊆ (S.toPrismNDim.dilation Cset).carrier ∧
        Prism3D.angle (V i) S ≤ (Cang : ℝ) * (θ : ℝ) := by
  classical
  simp [inSlabFamilyC]

theorem inSlabFamilyC_subset {Cset Cang : ℝ≥0} {s : Finset ι} {V : ι → Plank a b hab hb1}
    {θ : ℝ≥0} {hθ : θ ≤ 1} {S : Slab θ hθ} : inSlabFamilyC Cset Cang s V S ⊆ s := by
  intro i hi; exact (mem_inSlabFamilyC.mp hi).1

/-- The exact slab subfamily is contained in every controlled one with `Cset, Cang ≥ 1`. -/
theorem inSlabFamily_subset_inSlabFamilyC {Cset Cang : ℝ≥0} (hCset : 1 ≤ Cset) (hCang : 1 ≤ Cang)
    {s : Finset ι} {V : ι → Plank a b hab hb1}
    {θ : ℝ≥0} {hθ : θ ≤ 1} {S : Slab θ hθ} :
    inSlabFamily s V S ⊆ inSlabFamilyC Cset Cang s V S := by
  intro i hi
  rw [mem_inSlabFamily] at hi
  rw [mem_inSlabFamilyC]
  refine ⟨hi.1, hi.2.1.trans (S.toPrismNDim.self_subset_dilation hCset), ?_⟩
  have hCang' : (1 : ℝ) ≤ (Cang : ℝ) := by exact_mod_cast hCang
  have hθ0 : (0 : ℝ) ≤ (θ : ℝ) := NNReal.coe_nonneg _
  have hle : (θ : ℝ) ≤ (Cang : ℝ) * (θ : ℝ) := by nlinarith
  exact hi.2.2.trans hle

/-- Each plank lies in every controlled slab subfamily of its own containing slab
(`Cset,Cang ≥ 1`). -/
theorem mem_inSlabFamilyC_toSlab {Cset Cang : ℝ≥0} (hCset : 1 ≤ Cset) (hCang : 1 ≤ Cang)
    {s : Finset ι} {V : ι → Plank a b hab hb1}
    {i : ι} (hi : i ∈ s) {θ : ℝ≥0} (hθa : a ≤ θ) (hθ1 : θ ≤ 1) :
    i ∈ inSlabFamilyC Cset Cang s V ((V i).toSlab θ hθ1) :=
  inSlabFamily_subset_inSlabFamilyC hCset hCang (mem_inSlabFamily_toSlab hi hθa hθ1)

/-! ### Concrete witnesses for `plankReduction` -/

/-- The concrete ambient type for an erased three-dimensional prism.

The ambient prism type of a thickened-plank ensemble: 3-dimensional prisms in `ℝ³`.
This is the concrete value of the existential index type `τ` in `Kakeya.plankReduction`
(with the prism map `Qθ` taken to be the identity). -/
abbrev EnsemblePrism : Type :=
  PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))

instance : Nonempty EnsemblePrism :=
  ⟨PrismNDim.mk' (0 : EuclideanSpace ℝ (Fin 3)) (EuclideanSpace.basisFun (Fin 3) ℝ) ![1, 1, 1]⟩

/-- **The thickened representative** (`def:thickenedRepr`). For a plank family `(s, V)`, a
typical angle `θ`, and a comparability constant `cThk`, this bundles a *selection* `sel i ∈ s` for
each plank `P i` (`i ∈ s`), whose **undilated** standard thickening is the representative prism
`repr i`. The selected indices range over a maximal pairwise essentially-distinct family of
standard thickenings, and `sel` assigns to each plank one selected thickening that its own
thickening fails to be essentially distinct from.

* `repr i` is literally the undilated thickening of the selected plank (`repr_eq`);
* `(P i)_θ` and `repr i` are *not* essentially distinct (`notEssentiallyDistinct_repr`) — this is
  the assignment property that maximality supplies, and the sole geometric input;
* `P i` lies in the `cThk`-dilation of `repr i` (`subset_repr`);
* `repr i` lies in the `cThk`-dilation of the thickening `(P i)_θ` (`repr_subset_thickened`) — the
  **directed** half of `cThk`-comparability.
* distinct active representatives are essentially distinct (`pairwise_repr`).

Both containment fields are *fixed-dilation*, not exact: they are the two directions of
`Plank.equalScaleThickening_twoSidedDilation` at `r = 1`, applied to
`notEssentiallyDistinct_repr`. Exact containment is unavailable, and a `cThk`-dilated
representative would be the wrong object to select, because dilation does not preserve essential
distinctness — so `pairwise_repr` would fail for a family of dilated prisms. That is why `repr i`
is the *undilated* thickening.

The directed field replaces the former undirected `IsCComparable` field: a disjunction cannot
supply the containment that fibre clustering needs. The undirected form is recovered as the theorem
`ThickenedRepr.comparable`. There is no separate set-of-sets `ensemble`; the active family is the
finite image `indexSet = s.image repr`. This packages the structural existential witnesses of
`Kakeya.plankReduction`: `τ := EnsemblePrism`, `Qθ := id`, and the representative map `repr`. -/
structure ThickenedRepr (s : Finset ι) (V : ι → Plank a b hab hb1)
    (θ : ℝ≥0) (hθ1 : θ ≤ 1) (cThk : ℝ≥0) where
  /-- The selected index whose standard thickening represents `i`. -/
  sel : ι → ι
  /-- The representative map sending each plank index to a typed thickened plank. -/
  repr : ι → ThickenedPlank θ b _ hb1
  /-- The representative is the **undilated** standard thickening of the selected plank. -/
  repr_eq : ∀ i ∈ s, repr i = (V (sel i)).thickened θ hθ1
  /-- The assignment property: a plank's own thickening is not essentially distinct from the
  thickening selected for it. -/
  notEssentiallyDistinct_repr : ∀ i ∈ s,
    ¬ PrismNDim.IsEssentiallyDistinct ((V i).thickened θ hθ1).toPrismNDim
      (repr i).toPrismNDim
  /-- The plank is contained in the `cThk`-dilation of its representative prism. -/
  subset_repr : ∀ i ∈ s, ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
    ((repr i).toPrismNDim.dilation cThk).carrier
  /-- **Directed** control: the representative lies in the `cThk`-dilation of the thickening. -/
  repr_subset_thickened : ∀ i ∈ s,
    ((repr i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (((V i).thickened θ hθ1).toPrismNDim.dilation cThk).carrier
  /-- Distinct active representatives are essentially distinct (nonoverlapping). -/
  pairwise_repr : ∀ i ∈ s, ∀ j ∈ s, repr i ≠ repr j →
    PrismNDim.IsEssentiallyDistinct (repr i).toPrismNDim (repr j).toPrismNDim

namespace ThickenedRepr

variable {s : Finset ι} {V : ι → Plank a b hab hb1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk : ℝ≥0}

/-- The thickening `(P i)_θ` is `cThk`-comparable to the representative: the undirected clause
consumed by `Kakeya.plankReduction`, derived from the directed containment field. -/
theorem comparable (R : ThickenedRepr s V θ hθ1 cThk) (i : ι) (hi : i ∈ s) :
    PrismNDim.IsCComparable ((V i).thickened θ hθ1).toPrismNDim
      (R.repr i).toPrismNDim cThk :=
  Or.inr (R.repr_subset_thickened i hi)

open scoped Classical in
/-- The finite set of *active* thickened planks: the representatives actually used by `s`.
This is the concrete value of the finset `𝒯` in `Kakeya.plankReduction`. -/
noncomputable def indexSet (R : ThickenedRepr s V θ hθ1 cThk) :
    Finset (ThickenedPlank θ b hθ1 hb1) :=
  s.image R.repr

theorem repr_mem_indexSet (R : ThickenedRepr s V θ hθ1 cThk) {i : ι} (hi : i ∈ s) :
    R.repr i ∈ R.indexSet := by
  classical
  exact Finset.mem_image_of_mem _ hi

/-- Restrict a thickened representative along a subfamily, keeping the *same* `repr` map. This is
what lets the constant-multiplicity pigeonhole (which refines `s` using `R.repr`-fibres) be
composed with the slab-mass decomposition (which needs a `ThickenedRepr` on the refined family):
both must speak about one and the same representative map. Every field is a `∀ i ∈ s` statement,
so restriction is immediate. -/
def restrict (R : ThickenedRepr s V θ hθ1 cThk) {s₂ : Finset ι} (hs₂ : s₂ ⊆ s) :
    ThickenedRepr s₂ V θ hθ1 cThk where
  sel := R.sel
  repr := R.repr
  repr_eq i hi := R.repr_eq i (hs₂ hi)
  notEssentiallyDistinct_repr i hi := R.notEssentiallyDistinct_repr i (hs₂ hi)
  subset_repr i hi := R.subset_repr i (hs₂ hi)
  repr_subset_thickened i hi := R.repr_subset_thickened i (hs₂ hi)
  pairwise_repr i hi j hj := R.pairwise_repr i (hs₂ hi) j (hs₂ hj)

@[simp] theorem restrict_repr (R : ThickenedRepr s V θ hθ1 cThk) {s₂ : Finset ι} (hs₂ : s₂ ⊆ s) :
    (R.restrict hs₂).repr = R.repr := rfl

/-- The active thickened planks are pairwise essentially distinct: the nonoverlapping clause
of `Kakeya.plankReduction` (with `Qθ = id`). -/
theorem indexSet_pairwise (R : ThickenedRepr s V θ hθ1 cThk) :
    (R.indexSet : Set (ThickenedPlank θ b hθ1 hb1)).Pairwise
      (fun P P' => PrismNDim.IsEssentiallyDistinct P.toPrismNDim P'.toPrismNDim) := by
  classical
  rw [indexSet, Finset.coe_image]
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hne
  exact R.pairwise_repr i hi j hj hne

open scoped Classical in
/-- **Fibrewise cardinality** (`multiplicityAlgebraHelpers`(2), double counting): the planks of
`s` are partitioned by their representative thickened plank, so `|𝒫| = ∑_Q |repr⁻¹(Q)|` over the
active ensemble `𝒯`. The fibre `repr⁻¹(Q)` is `s.filter (fun i => repr i = Q)`. -/
theorem card_eq_sum_fibre (R : ThickenedRepr s V θ hθ1 cThk) :
    s.card = ∑ Q ∈ R.indexSet, (s.filter (fun i => R.repr i = Q)).card :=
  Finset.card_eq_sum_card_fiberwise fun _ hi => R.repr_mem_indexSet hi

open scoped Classical in
/-- **Family cardinality double counting** (`multiplicityAlgebraHelpers`(2)): given a thickened
representative `R` and a constant fibre size `N` such that every fibre `repr⁻¹(Q)` has cardinality
between `(N : ℝ)/cN` and `cN * (N : ℝ)`, the total index set cardinality satisfies the two-sided
bound `(N/cN) * |indexSet| ≤ |s| ≤ (cN * N) * |indexSet|`. This is the double-counting argument of
`card_eq_sum_fibre` combined with constant-fibre-size bounds. -/
theorem card_fibreFamily_eq_sum_fibre {s : Finset ι} {V : ι → Plank a b hab hb1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk : ℝ≥0} (R : ThickenedRepr s V θ hθ1 cThk)
    (N : ℕ) (cN : ℝ≥0)
    (hlo : ∀ Q ∈ R.indexSet, (N : ℝ) / (cN : ℝ) ≤ ((s.filter (fun i => R.repr i = Q)).card : ℝ))
    (hhi : ∀ Q ∈ R.indexSet, ((s.filter (fun i => R.repr i = Q)).card : ℝ) ≤ (cN : ℝ) * (N : ℝ)) :
    (N : ℝ) / (cN : ℝ) * (R.indexSet.card : ℝ) ≤ (s.card : ℝ) ∧
    (s.card : ℝ) ≤ (cN : ℝ) * (N : ℝ) * (R.indexSet.card : ℝ) := by
  have hcard := R.card_eq_sum_fibre
  have hcardR : (s.card : ℝ) = ∑ Q ∈ R.indexSet, ((s.filter (fun i => R.repr i = Q)).card : ℝ) := by
    exact_mod_cast hcard
  have hsum_lower : (N : ℝ) / (cN : ℝ) * (R.indexSet.card : ℝ)
      ≤ ∑ Q ∈ R.indexSet, ((s.filter (fun i => R.repr i = Q)).card : ℝ) := by
    calc
      (N : ℝ) / (cN : ℝ) * (R.indexSet.card : ℝ)
          = ∑ Q ∈ R.indexSet, ((N : ℝ) / (cN : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ Q ∈ R.indexSet, ((s.filter (fun i => R.repr i = Q)).card : ℝ) :=
        Finset.sum_le_sum fun Q hQ => hlo Q hQ
  have hsum_upper : ∑ Q ∈ R.indexSet, ((s.filter (fun i => R.repr i = Q)).card : ℝ)
      ≤ (cN : ℝ) * (N : ℝ) * (R.indexSet.card : ℝ) := by
    calc
      ∑ Q ∈ R.indexSet, ((s.filter (fun i => R.repr i = Q)).card : ℝ)
          ≤ ∑ Q ∈ R.indexSet, ((cN : ℝ) * (N : ℝ)) :=
            Finset.sum_le_sum fun Q hQ => hhi Q hQ
      _ = (R.indexSet.card : ℝ) * ((cN : ℝ) * (N : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = (cN : ℝ) * (N : ℝ) * (R.indexSet.card : ℝ) := by ring
  constructor
  · calc
      (N : ℝ) / (cN : ℝ) * (R.indexSet.card : ℝ)
          ≤ ∑ Q ∈ R.indexSet, ((s.filter (fun i => R.repr i = Q)).card : ℝ) := hsum_lower
      _ = (s.card : ℝ) := by rw [hcardR]
  · calc
      (s.card : ℝ) = ∑ Q ∈ R.indexSet, ((s.filter (fun i => R.repr i = Q)).card : ℝ) := by rw
          [hcardR]
      _ ≤ (cN : ℝ) * (N : ℝ) * (R.indexSet.card : ℝ) := hsum_upper

open scoped Classical in
/-- The fibres `repr⁻¹(Q)` for distinct `Q ∈ indexSet` are pairwise disjoint
and their union (biUnion) over `indexSet` equals `s`. -/
theorem fibres_partition (R : ThickenedRepr s V θ hθ1 cThk) :
    (∀ Q ∈ R.indexSet, ∀ Q' ∈ R.indexSet, Q ≠ Q' →
      Disjoint (s.filter (fun i => R.repr i = Q)) (s.filter (fun i => R.repr i = Q'))) ∧
    (R.indexSet.biUnion (fun Q => s.filter (fun i => R.repr i = Q)) = s) := by
  classical
  constructor
  · intro Q hQ Q' hQ' hne
    rw [Finset.disjoint_filter]
    intro i hi hiQ
    have hiQ' : R.repr i ≠ Q' := by
      rw [hiQ]
      exact hne
    exact hiQ'
  · apply Finset.Subset.antisymm
    · refine Finset.biUnion_subset.2 ?_
      intro Q hQ x hx
      exact (Finset.mem_filter.mp hx).1
    · intro i hi
      have hQ : R.repr i ∈ R.indexSet := R.repr_mem_indexSet hi
      refine Finset.mem_biUnion.mpr ⟨R.repr i, hQ, ?_⟩
      exact Finset.mem_filter.mpr ⟨hi, rfl⟩

/-- The fibre-size function `φ(i) = |repr⁻¹(repr i) ∩ s|`, i.e., the number of indices in `s`
mapping to the same representative thickened plank as `i`. This is the `phi` of
`lem:pigeonholeThickenedMultiplicity`: level sets of `phi` are fibre-saturated. -/
noncomputable def phi (R : ThickenedRepr s V θ hθ1 cThk) (i : ι) : ℕ := by
  classical
  exact (s.filter (fun j => R.repr j = R.repr i)).card

/-- The fibre-size function `phi` is constant on each fibre `repr⁻¹(Q)`: if two indices share
the same representative, their fibre sizes are equal. -/
theorem phi_constant_on_fibre (R : ThickenedRepr s V θ hθ1 cThk) {i i' : ι}
    (h : R.repr i = R.repr i') : R.phi i = R.phi i' := by
  classical
  unfold phi
  rw [h]

open scoped Classical in
/-- For any `k : ℕ`, the level set `s.filter (fun i => R.phi i = k)` is fibre-saturated:
for each `Q ∈ R.indexSet` the fibre `repr⁻¹(Q) ∩ s` is either entirely contained in the level
set or entirely disjoint from it. Equivalently, the partition of `s` by `repr`-fibres refines
the partition by `phi`-level-sets. This is `lem:fibreSaturatedLevelSet` in the blueprint. -/
theorem fibre_subset_or_disjoint_levelSet (R : ThickenedRepr s V θ hθ1 cThk) (k : ℕ)
    (Q : ThickenedPlank θ b hθ1 hb1) (_hQ : Q ∈ R.indexSet) :
    let L := s.filter (fun i => R.phi i = k);
    let fibre := s.filter (fun i => R.repr i = Q);
    fibre ⊆ L ∨ Disjoint fibre L := by
  classical
  intro L fibre
  by_cases h : ∃ i ∈ fibre, R.phi i = k
  · obtain ⟨i, hi, hiL⟩ := h
    have hi_s : i ∈ s := by
      dsimp [fibre] at hi
      exact (Finset.mem_filter.mp hi).1
    have hi_repr : R.repr i = Q := by
      dsimp [fibre] at hi
      exact (Finset.mem_filter.mp hi).2
    refine Or.inl ?_
    intro j hj
    have hj_s : j ∈ s := by
      dsimp [fibre] at hj
      exact (Finset.mem_filter.mp hj).1
    have hj_repr : R.repr j = Q := by
      dsimp [fibre] at hj
      exact (Finset.mem_filter.mp hj).2
    have hphi_eq : R.phi j = k := by
      calc
        R.phi j = R.phi i := R.phi_constant_on_fibre (hj_repr.trans hi_repr.symm)
        _ = k := hiL
    exact Finset.mem_filter.mpr ⟨hj_s, hphi_eq⟩
  · refine Or.inr ?_
    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
    intro hne
    rcases hne with ⟨i, hi⟩
    rcases Finset.mem_inter.mp hi with ⟨hi_fibre, hi_L⟩
    have hi_phi : R.phi i = k := by
      dsimp [L] at hi_L
      exact (Finset.mem_filter.mp hi_L).2
    exact h ⟨i, hi_fibre, hi_phi⟩

/-- Every fibre is nonempty at its own index, so `1 ≤ phi i` for `i ∈ s`. -/
theorem one_le_phi (R : ThickenedRepr s V θ hθ1 cThk) {i : ι} (hi : i ∈ s) : 1 ≤ R.phi i := by
  classical
  rw [phi]
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩

open scoped Classical in
/-- Generalization of `fibre_subset_or_disjoint_levelSet` to any predicate `p` constant on
`repr`-fibres: each fibre `repr⁻¹(Q)` is either contained in `s.filter p` or disjoint from it. -/
theorem fibre_subset_or_disjoint_filter (R : ThickenedRepr s V θ hθ1 cThk) (p : ι → Prop)
    [DecidablePred p] (hp : ∀ i i', R.repr i = R.repr i' → p i → p i')
    (Q : ThickenedPlank θ b hθ1 hb1)
    (_hQ : Q ∈ R.indexSet) :
    (s.filter (fun i => R.repr i = Q)) ⊆ s.filter p ∨
      Disjoint (s.filter (fun i => R.repr i = Q)) (s.filter p) := by
  classical
  by_cases h : ∃ i ∈ s.filter (fun i => R.repr i = Q), p i
  · obtain ⟨i, hi, hpi⟩ := h
    obtain ⟨_, hi_repr⟩ := Finset.mem_filter.mp hi
    refine Or.inl fun j hj => ?_
    obtain ⟨hj_s, hj_repr⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hj_s, hp i j (hi_repr.trans hj_repr.symm) hpi⟩
  · refine Or.inr (Finset.disjoint_left.mpr fun i hi hip => ?_)
    exact h ⟨i, hi, (Finset.mem_filter.mp hip).2⟩

open scoped Classical in
/-- **GWZ Lemma 6.13, pigeonhole for constant thickened multiplicity**
(`lem:pigeonholeThickenedMultiplicity`). Given a thickened representative `R` with fibre-size
function `phi` bounded by `K` on `s` (the packing bound of Step 1, supplied geometrically), there is
a good refinement `s₂ ⊆ s` (keeping a `cGood = (⌊log₂ K⌋+1)⁻¹ = (log 1/a)^{-O(1)}` fraction of the
shading mass), an integer `N ≥ 1` and a constant `cN = 2`, such that every thickened plank
`Q ∈ 𝒯` meeting `s₂` has fibre cardinality `∼ N`:
`N/cN ≤ |repr⁻¹(Q) ∩ s₂| ≤ cN · N`. The two-sided bound `1 ≤ cN ≤ 2` is returned, not just
positivity: `cN` is the literal `2` of the dyadic level set, and consumers such as
`Kakeya.plankReduction` need a *uniform* upper bound on the fibre constant, which an existential
`1 ≤ cN` alone does not provide. The refinement `s₂` is the heaviest dyadic level set
`{i : ⌊log₂ φ(i)⌋ = j⋆}`, which is fibre-saturated since `phi` is constant on fibres, so the whole
fibre lies in `s₂` and its cardinality equals `φ ∈ [N, 2N)`. -/
theorem pigeonholeThickenedMultiplicity (R : ThickenedRepr s V θ hθ1 cThk)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (K : ℕ) (hK : ∀ i ∈ s, R.phi i ≤ K) :
    ∃ (s₂ : Finset ι) (N : ℕ) (cGood cN : ℝ≥0),
      s₂ ⊆ s ∧ 1 ≤ N ∧ 1 ≤ cN ∧ cN ≤ 2 ∧
      ((Nat.log 2 K : ℝ≥0) + 1)⁻¹ ≤ cGood ∧
      ShadedBody.IsCRefinement s₂ Y s Y cGood ∧
      (∀ Q ∈ R.indexSet, (s₂.filter (fun i => R.repr i = Q)).Nonempty →
        (N : ℝ) / (cN : ℝ) ≤ ((s₂.filter (fun i => R.repr i = Q)).card : ℝ) ∧
          ((s₂.filter (fun i => R.repr i = Q)).card : ℝ) ≤ (cN : ℝ) * (N : ℝ)) := by
  classical
  set L : ℕ := Nat.log 2 K with hLdef
  have hg : ∀ i ∈ s, Nat.log 2 (R.phi i) ≤ L := fun i hi => Nat.log_mono_right (hK i hi)
  obtain ⟨js, -, hmass⟩ :=
    ENNReal.exists_heavy_level s (fun i => volume (Y i).shade)
      (fun i => Nat.log 2 (R.phi i)) L hg
  have hne0 : ((L : ENNReal) + 1) ≠ 0 := by positivity
  have htop : ((L : ENNReal) + 1) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top L, ENNReal.one_ne_top⟩
  refine ⟨s.filter (fun i => Nat.log 2 (R.phi i) = js), 2 ^ js, ((L : ℝ≥0) + 1)⁻¹, 2,
    Finset.filter_subset _ _, Nat.one_le_two_pow, one_le_two, le_rfl, le_rfl, ?_, ?_⟩
  · -- good refinement: `IsRefinement` is trivial (same shadings), mass bound from `hmass`
    refine ⟨⟨Finset.filter_subset _ _, fun i _ => ⟨rfl, subset_rfl⟩⟩, ?_⟩
    have hcoe2 : ((((L : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ENNReal) = ((L : ENNReal) + 1)⁻¹ := by
      rw [ENNReal.coe_inv (by positivity)]; push_cast; rfl
    rw [hcoe2]
    calc ((L : ENNReal) + 1)⁻¹ * ∑ i ∈ s, volume (Y i).shade
        ≤ ((L : ENNReal) + 1)⁻¹ * (((L : ENNReal) + 1) *
            ∑ i ∈ s.filter (fun i => Nat.log 2 (R.phi i) = js), volume (Y i).shade) := by
          gcongr
      _ = ∑ i ∈ s.filter (fun i => Nat.log 2 (R.phi i) = js), volume (Y i).shade := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hne0 htop, one_mul]
  · -- fibre cardinality `∼ N` on the saturated dyadic level set
    intro Q hQ hnonempty
    obtain ⟨i₀, hi₀⟩ := hnonempty
    rw [Finset.mem_filter] at hi₀
    obtain ⟨hi₀s₂, hi₀repr⟩ := hi₀
    rw [Finset.mem_filter] at hi₀s₂
    obtain ⟨hi₀s, hi₀p⟩ := hi₀s₂
    have hp : ∀ i i', R.repr i = R.repr i' →
        (fun i => Nat.log 2 (R.phi i) = js) i → (fun i => Nat.log 2 (R.phi i) = js) i' := by
      intro i i' hii hpi
      show Nat.log 2 (R.phi i') = js
      rw [← R.phi_constant_on_fibre hii]; exact hpi
    have hsat := R.fibre_subset_or_disjoint_filter (fun i => Nat.log 2 (R.phi i) = js) hp Q hQ
    have hfibre_sub : s.filter (fun i => R.repr i = Q) ⊆
        s.filter (fun i => Nat.log 2 (R.phi i) = js) := by
      rcases hsat with h | h
      · exact h
      · rw [Finset.disjoint_left] at h
        exact absurd (Finset.mem_filter.mpr ⟨hi₀s, hi₀p⟩)
          (h (Finset.mem_filter.mpr ⟨hi₀s, hi₀repr⟩))
    have hfilter_eq : (s.filter (fun i => Nat.log 2 (R.phi i) = js)).filter
        (fun i => R.repr i = Q) = s.filter (fun i => R.repr i = Q) := by
      apply Finset.Subset.antisymm
      · intro i hi
        rw [Finset.mem_filter] at hi ⊢
        exact ⟨(Finset.mem_filter.mp hi.1).1, hi.2⟩
      · intro i hi
        have hi' := hi
        rw [Finset.mem_filter] at hi ⊢
        exact ⟨hfibre_sub hi', hi.2⟩
    have hNc : ((s.filter (fun i => Nat.log 2 (R.phi i) = js)).filter
        (fun i => R.repr i = Q)).card = R.phi i₀ := by
      rw [hfilter_eq]; unfold phi; rw [hi₀repr]
    have hphi_ne : R.phi i₀ ≠ 0 := Nat.one_le_iff_ne_zero.mp (R.one_le_phi hi₀s)
    have hlo : 2 ^ js ≤ R.phi i₀ := by
      have := Nat.pow_log_le_self 2 hphi_ne; rwa [hi₀p] at this
    have hhi : R.phi i₀ < 2 ^ (js + 1) := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (R.phi i₀); rwa [hi₀p] at this
    rw [hNc]
    refine ⟨?_, ?_⟩
    · have h1 : (2 : ℝ) ^ js ≤ (R.phi i₀ : ℝ) := by exact_mod_cast hlo
      have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ js := by positivity
      push_cast
      linarith
    · have h3 : (R.phi i₀ : ℝ) < (2 : ℝ) ^ (js + 1) := by exact_mod_cast hhi
      rw [pow_succ] at h3
      push_cast
      linarith

end ThickenedRepr

/-- **The slab assignment** for a thickened ensemble: the concrete shape of `plankReduction`'s
slab witnesses `σ, Sl, slabOf, 𝒮`, together with clause (e). Taking `σ := Slab θ hθ1` and
`Sl := id`, each thickened prism is assigned a slab `slabOf Q`, every slab used by a plank of `s`
lies in the finite set `used = 𝒮`, and each plank `P i` lies in the slab subfamily
(`inSlabFamily`) of its representative's slab. Constructing an actual assignment is the
remaining geometric step; this structure fixes the witness shape so the proof of `plankReduction`
can supply it. -/
structure SlabAssignment (s : Finset ι) (V : ι → Plank a b hab hb1)
    (θ : ℝ≥0) (hθ1 : θ ≤ 1) (repr : ι → ThickenedPlank θ b hθ1 hb1) (Cset Cang : ℝ≥0) where
  /-- The slab assigned to each thickened prism (`slabOf`, with `σ = Slab θ hθ1`, `Sl = id`). -/
  slabOf : ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1
  /-- The finite set `𝒮` of slabs in play. -/
  used : Finset (Slab θ hθ1)
  /-- Every plank's representative slab is one of the slabs in `𝒮`. -/
  slabOf_mem : ∀ i ∈ s, slabOf (repr i) ∈ used
  /-- Clause (e): each plank lies in the *controlled* slab subfamily (fixed dilation `Cset`, fixed
  angle constant `Cang`) of its representative's slab. -/
  mem_inSlabFamily : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V (slabOf (repr i))

/-- Every *active* representative is assigned a used slab. `SlabAssignment.slabOf_mem` is stated
over the index family `s`; since `R.indexSet` is by definition the image of `s` under `R.repr`,
the same conclusion holds for every member of the active ensemble. -/
theorem SlabAssignment.slabOf_mem_of_mem_indexSet {s : Finset ι} {V : ι → Plank a b hab hb1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk Cset Cang : ℝ≥0} (R : ThickenedRepr s V θ hθ1 cThk)
    (SA : SlabAssignment s V θ hθ1 R.repr Cset Cang) {Q : ThickenedPlank θ b hθ1 hb1}
    (hQ : Q ∈ R.indexSet) : SA.slabOf Q ∈ SA.used := by
  classical
  rw [ThickenedRepr.indexSet, Finset.mem_image] at hQ
  obtain ⟨i, hi, rfl⟩ := hQ
  exact SA.slabOf_mem i hi

open scoped Classical in
/-- **Non-injective `SlabAssignment` where a whole `repr`-fibre shares one slab.** Choose a
representative plank `rep Q` for each thickened prism `Q`, so the *entire* fibre `repr⁻¹(Q)` is
assigned the single slab `(V (rep Q)).toSlab θ hθ1`. Given the geometric coherence `hcoh` that
every plank lies in the slab subfamily of its fibre's shared containing slab — the conclusion
supplied by `slabMassDecomposition` (a typical angle clusters a fibre's planks
in one `O(θ)`-slab) — this assembles a `SlabAssignment`. Unlike `ofToSlab`, `repr` need not be
injective. -/
noncomputable def SlabAssignment.ofFibreRep
    {s : Finset ι} {V : ι → Plank a b hab hb1} {θ : ℝ≥0} (hθ1 : θ ≤ 1)
    {repr : ι → ThickenedPlank θ b hθ1 hb1} (rep : ThickenedPlank θ b hθ1 hb1 → ι)
    (Cset Cang : ℝ≥0)
    (hcoh : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V ((V (rep (repr i))).toSlab θ hθ1)) :
    SlabAssignment s V θ hθ1 repr Cset Cang where
  slabOf Q := (V (rep Q)).toSlab θ hθ1
  used := s.image (fun i => (V (rep (repr i))).toSlab θ hθ1)
  slabOf_mem _ hi := Finset.mem_image_of_mem _ hi
  mem_inSlabFamily := hcoh

open scoped Classical in
/-- The **thickened shading** `Yθ Q` carried by a thickened prism `Q`: the union of the shadings
`(Y' i).shade` over the fibre `repr⁻¹(Q) ∩ s'`, as a `ShadedBody` with carrier `Q`. Provided each
plank's shading sits in its representative (`hsub`), this is the `Yθ` witness of `plankReduction`,
underlying the thickened-union identity `U(𝒫'_θ, Yθ) = U(𝒫', Y')`. -/
noncomputable def thickenedShading {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → ThickenedPlank θ b hθ1 hb1)
    (hsub : ∀ i ∈ s', (Y' i).shade ⊆ (repr i).carrier)
    (Q : ThickenedPlank θ b hθ1 hb1) : ShadedBody (EuclideanSpace ℝ (Fin 3)) where
  toConvexSpaceBody := Q.toConvexSpaceBody
  shade := ⋃ i ∈ s'.filter (fun i => repr i = Q), (Y' i).shade
  measurableSet_shade :=
    MeasurableSet.biUnion (s'.filter (fun i => repr i = Q)).countable_toSet
      fun i _ => (Y' i).measurableSet_shade
  shade_subset := Set.iUnion₂_subset fun i hi => by
    obtain ⟨hi', hQ⟩ := Finset.mem_filter.mp hi
    exact hQ ▸ hsub i hi'

open scoped Classical in
/-- **Thickened-union identity** (`lem:thickenedUnionIdentity`): the union of the thickened
shadings over the active ensemble `𝒯 = repr(s')` equals the shading union of `(s', Y')`, because
the fibres `repr⁻¹(Q)` partition `s'`. -/
theorem iUnion_thickenedShading {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → ThickenedPlank θ b hθ1 hb1)
    (hsub : ∀ i ∈ s', (Y' i).shade ⊆ (repr i).carrier) :
    ⋃ Q ∈ s'.image repr, (thickenedShading s' Y' repr hsub Q).shade
      = ⋃ i ∈ s', (Y' i).shade := by
  ext x
  simp only [thickenedShading, Set.mem_iUnion, Finset.mem_image, Finset.mem_filter, exists_prop]
  constructor
  · rintro ⟨Q, ⟨i, hi, rfl⟩, j, ⟨hj, _⟩, hxj⟩
    exact ⟨j, hj, hxj⟩
  · rintro ⟨i, hi, hxi⟩
    exact ⟨repr i, ⟨i, hi, rfl⟩, i, ⟨hi, rfl⟩, hxi⟩

/-! ### Minimal geometric middle-layer data for Lemma 6.13 -/

/-- The `theta * b × b × b` boxes used inside a `theta × 1 × 1` slab.  This is just a
specialized `Prism3D`, in the same spirit as `Plank` and `Slab`. -/
abbrev ThetaBox (theta b : ℝ≥0) (htheta1 : theta ≤ 1) :=
  Prism3D (theta * b) b b (by simpa using mul_le_mul_left htheta1 b) le_rfl

end Plank

namespace Kakeya

/-- **The fixed Section 6 working window, as a convex body.**  The Frostman hypothesis of GWZ
Lemma 6.4 is measured in this body.  It is the same window that `Plank.IsWindowedFamily` puts the
planks in — a windowed family lies in `Metric.closedBall 0 Plank.windowRadius` — so it is the body
in which the density of such a family is meaningful; the unit ball would not contain the family. -/
def plankWindow : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
  ConvexSpaceBody.closedBall 0 Plank.windowRadius (by rw [Plank.windowRadius]; norm_num)

/-- The absolute radius of the plank normalisation window. -/
def plankWindowRadius : ℝ≥0 := 4

@[simp]
theorem plankWindow_carrier :
    plankWindow.carrier = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3))
      (plankWindowRadius : ℝ) := rfl

end Kakeya

end
