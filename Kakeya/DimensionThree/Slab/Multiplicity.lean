/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Slab.Incidence
public import Kakeya.DimensionThree.Plank.RepresentativeFibres
public import Kakeya.Density
public import Kakeya.Homothety
public import Kakeya.Multiplicity
public import Kakeya.Thickness.HasThicknesses
public import Kakeya.Thickness.OuterPrism
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The multiplicity bound for families of `δ × b × c` slabs

This file states the multiplicity half of GWZ Lemma 6.9: for a family
`𝒮 = (Sᵢ)_{i ∈ r}` of shaded `δ × b × c` rectangular prisms (only the short axis is at
scale `δ`) with
`λ(𝒮, Y) ≥ δ^η`, `b, c ≥ δ^η` and `Δ_max(𝒮) ≤ δ^{-η}`, one has
`μ(𝒮, Y) ≤ C(η) δ^{-8η}`.

The argument is the one of `Kakeya.DimensionThree.Slab.Incidence` (Cauchy–Schwarz at a
typical intersection angle), but run over a dyadic family of angle scales rather than at a
single angle, and with the pairwise incidence count controlled by `Δ_max` through a
"neighbour prism" that confines all nearly parallel neighbours of a given prism.

## Main declarations

* `ShadedPrism3D`: a `δ × b × c` prism with a measurable shading.
* `ShadedPrism3D.toShadedSlab`: the enclosing `δ × 1 × 1` slab, which carries the same shading
  and the same pairwise angles; it lets the slab incidence API be applied verbatim.
* `ShadedPrism3D.neighbourPrism`: the prism confining the nearly parallel neighbours.
* `ShadedPrism3D.multiplicity_mul_le_maxDensity`: the master multiplicity estimate.
* `ShadedPrism3D.multiplicity_le_log_form`: GWZ Lemma 6.9 in its sharper logarithmic form.
* `ShadedPrism3D.multiplicity_le_rpow`: GWZ Lemma 6.9 as stated by GWZ.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal ENNReal

noncomputable section

/-! ## Resizing a three-dimensional prism -/

namespace Prism3D

variable {a b c : NNReal} {a_le_b : a ≤ b} {b_le_c : b ≤ c}

/-- A compact set of prescribed affine thicknesses sits inside a comparable `Prism3D`. -/
theorem exists_superset_of_hasThicknesses {C₀ : NNReal} (_hC₀ : 1 ≤ C₀)
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K) (hKne : K.Nonempty)
    {t₀ t₁ t₂ : ℝ} (ht : Kakeya.HasThicknesses K C₀ ![t₀, t₁, t₂])
    {a' b' c' : NNReal} (hab' : a' ≤ b') (hb'c' : b' ≤ c')
    (ha' : (C₀ : ℝ) * t₂ ≤ a') (hb' : (C₀ : ℝ) * t₁ ≤ b') (hc' : (C₀ : ℝ) * t₀ ≤ c') :
    ∃ P : Prism3D a' b' c' hab' hb'c', K ⊆ P.carrier := by
  have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  refine ⟨Prism3D.mk (PrismNDim.mk' (outerPrism.center h3 hK hKne)
        ((outerPrism.basis h3 hK hKne).reindex (Fin.revPerm : Fin 3 ≃ Fin 3))
        ![a', b', c']) (PrismNDim.thicknesses_mk' _ _ _), ?_⟩
  intro x hx
  rw [PrismNDim.mem_carrier_iff]
  intro i
  rw [PrismNDim.basis_mk', PrismNDim.center_mk', PrismNDim.thicknesses_mk',
    OrthonormalBasis.repr_reindex, Fin.revPerm_symm, Fin.revPerm_apply]
  calc
    |(outerPrism.basis h3 hK hKne).repr (x -ᵥ outerPrism.center h3 hK hKne) (Fin.rev i)|
        ≤ Metric.thickness ℝ K (Fin.rev i) := outerPrism.basis_repr_le h3 hK hKne hx (Fin.rev i)
    _ ≤ (C₀ : ℝ) * ![t₀, t₁, t₂] (Fin.rev i) := (ht (Fin.rev i)).2
    _ ≤ (![a', b', c'] i : ℝ) := by
      fin_cases i
      · simpa using ha'
      · simpa using hb'
      · simpa using hc'

/-- The standard axis-aligned `Prism3D`, centred at the origin. -/
def std (a b c : NNReal) (hab : a ≤ b) (hbc : b ≤ c) : Prism3D a b c hab hbc where
  toPrismNDim := PrismNDim.mk' 0 (EuclideanSpace.basisFun (Fin 3) ℝ) ![a, b, c]
  thicknesses_eq := PrismNDim.thicknesses_mk' _ _ _

instance : Nonempty (Prism3D a b c a_le_b b_le_c) := ⟨std a b c a_le_b b_le_c⟩

/-- The half-widths of the homothety image of a `Prism3D`. -/
theorem thicknesses_homothety (P : Prism3D a b c a_le_b b_le_c)
    (x : EuclideanSpace ℝ (Fin 3)) (ρ : NNReal) {a' b' c' : NNReal}
    (ha' : a' = ρ * a) (hb' : b' = ρ * b) (hc' : c' = ρ * c) :
    (P.toPrismNDim.homothety x ρ).thicknesses = ![a', b', c'] := by
  subst ha'
  subst hb'
  subst hc'
  funext i
  fin_cases i <;> simp [PrismNDim.homothety_thicknesses, P.thicknesses_eq]

/-- The homothety image of a `Prism3D`, with prescribed target half-widths. -/
def homothety (P : Prism3D a b c a_le_b b_le_c) (x : EuclideanSpace ℝ (Fin 3)) (ρ : NNReal)
    {a' b' c' : NNReal} (hab' : a' ≤ b') (hb'c' : b' ≤ c')
    (ha' : a' = ρ * a) (hb' : b' = ρ * b) (hc' : c' = ρ * c) :
    Prism3D a' b' c' hab' hb'c' where
  toPrismNDim := P.toPrismNDim.homothety x ρ
  thicknesses_eq := P.thicknesses_homothety x ρ ha' hb' hc'

/-- The carrier of `Prism3D.homothety` is the homothety image of the original carrier. -/
theorem carrier_homothety (P : Prism3D a b c a_le_b b_le_c) (x : EuclideanSpace ℝ (Fin 3))
    {ρ : NNReal} (hρ : 0 < ρ) {a' b' c' : NNReal} (hab' : a' ≤ b') (hb'c' : b' ≤ c')
    (ha' : a' = ρ * a) (hb' : b' = ρ * b) (hc' : c' = ρ * c) :
    ((P.homothety x ρ hab' hb'c' ha' hb' hc').carrier : Set (EuclideanSpace ℝ (Fin 3))) =
      AffineMap.homothety x (ρ : ℝ) '' P.carrier := by
  exact P.toPrismNDim.carrier_homothety x hρ

/-- Two points of an `a × b × c` prism are at distance at most `2 (a + b + c)`. -/
theorem norm_sub_le_of_mem (P : Prism3D a b c a_le_b b_le_c)
    {x y : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ P.carrier) (hy : y ∈ P.carrier) :
    ‖y - x‖ ≤ 2 * ((a : ℝ) + b + c) := by
  have hvsub : y -ᵥ x = y - x := vsub_eq_sub y x
  have hcoords : ∀ i : Fin 3, |P.basis.repr (y - x) i| ≤ 2 * (P.thicknesses i : ℝ) := by
    intro i
    have h := P.abs_inner_vsub_basis_le hx hy i
    rw [hvsub, real_inner_comm] at h
    rw [P.basis.repr_apply_apply]
    exact h
  calc
    ‖y - x‖ ≤ ∑ i : Fin 3, |P.basis.repr (y - x) i| := by
      conv_lhs => rw [← P.basis.sum_repr (y - x)]
      refine norm_sum_le_of_le _ fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs, P.basis.norm_eq_one, mul_one]
    _ ≤ ∑ i : Fin 3, 2 * (P.thicknesses i : ℝ) :=
      Finset.sum_le_sum fun i _ => hcoords i
    _ = 2 * ∑ i : Fin 3, (P.thicknesses i : ℝ) := by rw [Finset.mul_sum]
    _ = 2 * ((a : ℝ) + b + c) := by
      rw [P.thicknesses_eq, Fin.sum_univ_three]
      simp

/-- Crude diameter bound for a `Prism3D`: `‖y - x‖ ≤ 6c`. -/
theorem norm_sub_le_of_mem' (P : Prism3D a b c a_le_b b_le_c)
    {x y : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ P.carrier) (hy : y ∈ P.carrier) :
    ‖y - x‖ ≤ 6 * (c : ℝ) := by
  calc
    ‖y - x‖ ≤ 2 * ((a : ℝ) + b + c) := norm_sub_le_of_mem P hx hy
    _ ≤ 6 * (c : ℝ) := by
      have ha : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast a_le_b
      have hb : (b : ℝ) ≤ (c : ℝ) := by exact_mod_cast b_le_c
      nlinarith

/-- **Resize** a `Prism3D`: keep its centre and orthonormal frame, and replace the half-widths
by the prescribed `a' ≤ b' ≤ c'`. -/
def resize (P : Prism3D a b c a_le_b b_le_c) {a' b' c' : NNReal}
    (a'_le_b' : a' ≤ b') (b'_le_c' : b' ≤ c') : Prism3D a' b' c' a'_le_b' b'_le_c' where
  toPrismNDim := P.toPrismNDim.resize ![a', b', c']
  thicknesses_eq := PrismNDim.resize_thicknesses _ _

@[simp] lemma resize_center (P : Prism3D a b c a_le_b b_le_c) {a' b' c' : NNReal}
    (a'_le_b' : a' ≤ b') (b'_le_c' : b' ≤ c') :
    (P.resize a'_le_b' b'_le_c').center = P.center := rfl

@[simp] lemma resize_basis (P : Prism3D a b c a_le_b b_le_c) {a' b' c' : NNReal}
    (a'_le_b' : a' ≤ b') (b'_le_c' : b' ≤ c') :
    (P.resize a'_le_b' b'_le_c').basis = P.basis := rfl

/-- Enlarging all three half-widths enlarges the carrier. -/
theorem carrier_subset_resize (P : Prism3D a b c a_le_b b_le_c) {a' b' c' : NNReal}
    (a'_le_b' : a' ≤ b') (b'_le_c' : b' ≤ c')
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (P.resize a'_le_b' b'_le_c').carrier := by
  refine P.toPrismNDim.carrier_subset_resize (w := ![a', b', c']) fun i => ?_
  rw [P.thicknesses_eq]
  fin_cases i
  · simpa using ha
  · simpa using hb
  · simpa using hc

/-- The angle between two prisms depends only on their frames, hence is unchanged by resizing. -/
@[simp] theorem angle_resize {a₂ b₂ c₂ : NNReal} {h₂ : a₂ ≤ b₂} {h₂' : b₂ ≤ c₂}
    (P : Prism3D a b c a_le_b b_le_c) (Q : Prism3D a₂ b₂ c₂ h₂ h₂')
    {a' b' c' : NNReal} (a'_le_b' : a' ≤ b') (b'_le_c' : b' ≤ c')
    {a'' b'' c'' : NNReal} (a''_le_b'' : a'' ≤ b'') (b''_le_c'' : b'' ≤ c'') :
    (P.resize a'_le_b' b'_le_c').angle (Q.resize a''_le_b'' b''_le_c'') = P.angle Q := rfl

end Prism3D

/-! ## Shaded `δ × b × c` slabs -/

/-- A shaded `δ × b × c` slab: a rectangular prism in `ℝ³` with half-widths `δ ≤ b ≤ c ≤ 1`,
together with a measurable shading `Y(S) ⊆ S.carrier`.

Only the short axis is at scale `δ`; a `ShadedSlab` is the special case `b = c = 1`. -/
structure ShadedPrism3D (δ b c : NNReal) (δ_le_b : δ ≤ b) (b_le_c : b ≤ c) (c_le_one : c ≤ 1)
    extends Prism3D δ b c δ_le_b b_le_c, ShadedBody (EuclideanSpace ℝ (Fin 3))

attribute [nolint docBlame] ShadedPrism3D.toShadedBody

namespace ShadedPrism3D

variable {δ b c : NNReal} {δ_le_b : δ ≤ b} {b_le_c : b ≤ c} {c_le_one : c ≤ 1} {ι : Type*}

/-- The short axis of a `δ × b × c` slab is at most as thick as the ambient unit scale. -/
theorem delta_le_one (δ_le_b : δ ≤ b) (b_le_c : b ≤ c) (c_le_one : c ≤ 1) : δ ≤ 1 :=
  δ_le_b.trans (b_le_c.trans c_le_one)

/-! ### Shading a prism -/

/-- **Shade a `Prism3D`.** `ShadedPrism3D` has the two parents `Prism3D` and `ShadedBody` and no
coercion between them, so a shaded prism cannot be assembled from a prism and a shading without
this constructor. -/
def ofPrism3D (P : Prism3D δ b c δ_le_b b_le_c) (Y : Set (EuclideanSpace ℝ (Fin 3)))
    (hY : MeasurableSet Y) (hYP : Y ⊆ P.carrier) (hc1 : c ≤ 1) :
    ShadedPrism3D δ b c δ_le_b b_le_c hc1 where
  toPrism3D := P
  shade := Y
  measurableSet_shade := hY
  shade_subset := hYP

@[simp] theorem toPrism3D_ofPrism3D (P : Prism3D δ b c δ_le_b b_le_c)
    (Y : Set (EuclideanSpace ℝ (Fin 3))) (hY : MeasurableSet Y) (hYP : Y ⊆ P.carrier)
    (hc1 : c ≤ 1) : (ofPrism3D P Y hY hYP hc1).toPrism3D = P := rfl

@[simp] theorem shade_ofPrism3D (P : Prism3D δ b c δ_le_b b_le_c)
    (Y : Set (EuclideanSpace ℝ (Fin 3))) (hY : MeasurableSet Y) (hYP : Y ⊆ P.carrier)
    (hc1 : c ≤ 1) : (ofPrism3D P Y hY hYP hc1).shade = Y := rfl

@[simp] theorem carrier_ofPrism3D (P : Prism3D δ b c δ_le_b b_le_c)
    (Y : Set (EuclideanSpace ℝ (Fin 3))) (hY : MeasurableSet Y) (hYP : Y ⊆ P.carrier)
    (hc1 : c ≤ 1) :
    ((ofPrism3D P Y hY hYP hc1).carrier : Set (EuclideanSpace ℝ (Fin 3))) = P.carrier := rfl

instance : Nonempty (ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) :=
  ⟨ofPrism3D (Prism3D.std δ b c δ_le_b b_le_c) ∅ MeasurableSet.empty (Set.empty_subset _)
    c_le_one⟩

/-! ### The enclosing slab -/

/-- The **enclosing slab** of a shaded `δ × b × c` slab: the `δ × 1 × 1` slab with the same
centre, the same frame and the same shading. -/
def toShadedSlab (S : ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) :
    ShadedSlab δ (delta_le_one δ_le_b b_le_c c_le_one) where
  toPrism3D := S.toPrism3D.resize (delta_le_one δ_le_b b_le_c c_le_one) le_rfl
  shade := S.shade
  measurableSet_shade := S.measurableSet_shade
  shade_subset := S.shade_subset.trans
    (S.toPrism3D.carrier_subset_resize _ _ le_rfl (b_le_c.trans c_le_one) c_le_one)

/-- The enclosing slab family of a family of shaded `δ × b × c` slabs.

`Tri` and `Tri_θ` of the prism family are, by definition, those of this slab family. -/
abbrev slabs (V : ι → ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) :
    ι → ShadedSlab δ (delta_le_one δ_le_b b_le_c c_le_one) := fun i => (V i).toShadedSlab

/-- `Tri(𝒮, Y) = ∑_{i,j} |Y_i ∩ Y_j|`, read off the enclosing slab family. -/
abbrev tri (s : Finset ι) (V : ι → ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) : ENNReal :=
  ShadedSlab.tri s (slabs V)

/-- `Tri_θ(𝒮, Y)`, read off the enclosing slab family. -/
abbrev triAtAngle (s : Finset ι) (V : ι → ShadedPrism3D δ b c δ_le_b b_le_c c_le_one)
    (θ : ℝ) : ENNReal :=
  ShadedSlab.triAtAngle s (slabs V) θ

/-- A `δ × b × c` slab is contained in its enclosing `δ`-slab. -/
theorem carrier_subset_toShadedSlab (S : ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) :
    (S.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ S.toShadedSlab.carrier :=
  S.toPrism3D.carrier_subset_resize _ _ le_rfl (b_le_c.trans c_le_one) c_le_one

/-- The enclosing slab carries the same shading. -/
@[simp] theorem shade_toShadedSlab (S : ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) :
    S.toShadedSlab.shade = S.shade := rfl

/-- The enclosing slabs have the same pairwise angles as the prisms. -/
@[simp] theorem angle_toShadedSlab (S T : ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) :
    Slab.angle S.toShadedSlab.toPrism3D T.toShadedSlab.toPrism3D
      = Prism3D.angle S.toPrism3D T.toPrism3D := rfl

/-! ### Shading mass -/

/-- **Shading mass of a prism family.** `∑_{i ∈ r} |Y_i| = λ(𝒮, Y) · |r| · 8 δ b c`. -/
theorem sum_volume_shade_eq (s : Finset ι)
    (V : ι → ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) :
    ∑ i ∈ s, volume (V i).shade =
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) *
        ((s.card : ENNReal) * (8 * (δ : ENNReal) * b * c)) := by
  have hcarrier : ∑ i ∈ s, volume (V i).carrier =
      (s.card : ENNReal) * (8 * (δ : ENNReal) * b * c) := by
    rw [Finset.sum_congr rfl fun i _ => Prism3D.volume_carrier (V i).toPrism3D,
      Finset.sum_const, nsmul_eq_mul]
  rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul s (fun i => (V i).toShadedBody),
    hcarrier]

/-! ### Confining the nearly parallel neighbours -/

/-- **Spread along the short axis of a nearly parallel neighbour.** If `∠(S, T) ≤ 2θ` and
`x, y ∈ T`, then the displacement `y - x` has short-axis coordinate at most `2δ + 8θc` in the
frame of `S`. -/
theorem abs_inner_sub_shortAxis_le (S T : ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) {θ : ℝ}
    (hθ : 0 < θ) (hangle : Prism3D.angle S.toPrism3D T.toPrism3D ≤ 2 * θ)
    {x y : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ T.carrier) (hy : y ∈ T.carrier) :
    |inner ℝ (y - x) (S.basis 0)| ≤ 2 * (δ : ℝ) + 8 * θ * c := by
  let a : Fin 3 → ℝ := fun k => T.basis.repr (y - x) k
  have ht0 : (T.thicknesses 0 : ℝ) = (δ : ℝ) := by rw [T.thicknesses_eq]; rfl
  have ht1 : (T.thicknesses 1 : ℝ) = (b : ℝ) := by rw [T.thicknesses_eq]; rfl
  have ht2 : (T.thicknesses 2 : ℝ) = (c : ℝ) := by rw [T.thicknesses_eq]; rfl
  have hsum : inner ℝ (y - x) (S.basis 0) =
      a 0 * inner ℝ (T.basis 0) (S.basis 0) +
      a 1 * inner ℝ (T.basis 1) (S.basis 0) +
      a 2 * inner ℝ (T.basis 2) (S.basis 0) := by
    unfold a
    conv_lhs => rw [(T.basis.sum_repr (y - x)).symm]
    rw [sum_inner, Fin.sum_univ_three]
    simp only [inner_smul_left, RCLike.conj_to_real]
  have hcoords : ∀ k : Fin 3, |a k| ≤ 2 * (T.thicknesses k : ℝ) := by
    intro k
    have h := T.toPrism3D.abs_inner_vsub_basis_le hx hy k
    rw [vsub_eq_sub] at h
    change |T.basis.repr (y - x) k| ≤ 2 * (T.thicknesses k : ℝ)
    rw [T.basis.repr_apply_apply, real_inner_comm]
    exact h
  have hprod0 : |a 0 * inner ℝ (T.basis 0) (S.basis 0)| ≤ 2 * (δ : ℝ) := by
    calc
      |a 0 * inner ℝ (T.basis 0) (S.basis 0)| = |a 0| * |inner ℝ (T.basis 0) (S.basis 0)| := by
        rw [abs_mul]
      _ ≤ (2 * (T.thicknesses 0 : ℝ)) * 1 := by
        exact mul_le_mul (hcoords 0) (Prism3D.abs_inner_basis_le_one T.toPrism3D S.toPrism3D 0 0)
          (abs_nonneg _) (by positivity)
      _ = 2 * (δ : ℝ) := by rw [ht0]; ring
  have hprod1 : |a 1 * inner ℝ (T.basis 1) (S.basis 0)| ≤ 4 * θ * (b : ℝ) := by
    have hb : |a 1| ≤ 2 * (T.thicknesses 1 : ℝ) := hcoords 1
    have hA : |inner ℝ (T.basis 1) (S.basis 0)| ≤ S.toPrism3D.angle T.toPrism3D :=
      (Plank.abs_inner_basis_ne_zero_le_angle T.toPrism3D S.toPrism3D (j := 1) (by decide)).trans_eq
        (Prism3D.angle_comm T.toPrism3D S.toPrism3D)
    calc
      |a 1 * inner ℝ (T.basis 1) (S.basis 0)| ≤
          |a 1| * |inner ℝ (T.basis 1) (S.basis 0)| := by rw [abs_mul]
      _ ≤ (2 * (T.thicknesses 1 : ℝ)) * (S.toPrism3D.angle T.toPrism3D) := by
        exact mul_le_mul hb hA (abs_nonneg _) (by positivity)
      _ = (2 * (b : ℝ)) * (S.toPrism3D.angle T.toPrism3D) := by rw [ht1]
      _ ≤ (2 * (b : ℝ)) * (2 * θ) := by
        exact mul_le_mul_of_nonneg_left hangle (by positivity)
      _ = 4 * θ * (b : ℝ) := by ring
  have hprod2 : |a 2 * inner ℝ (T.basis 2) (S.basis 0)| ≤ 4 * θ * (c : ℝ) := by
    have hb : |a 2| ≤ 2 * (T.thicknesses 2 : ℝ) := hcoords 2
    have hA : |inner ℝ (T.basis 2) (S.basis 0)| ≤ S.toPrism3D.angle T.toPrism3D :=
      (Plank.abs_inner_basis_ne_zero_le_angle T.toPrism3D S.toPrism3D (j := 2) (by decide)).trans_eq
        (Prism3D.angle_comm T.toPrism3D S.toPrism3D)
    calc
      |a 2 * inner ℝ (T.basis 2) (S.basis 0)| ≤
          |a 2| * |inner ℝ (T.basis 2) (S.basis 0)| := by rw [abs_mul]
      _ ≤ (2 * (T.thicknesses 2 : ℝ)) * (S.toPrism3D.angle T.toPrism3D) := by
        exact mul_le_mul hb hA (abs_nonneg _) (by positivity)
      _ = (2 * (c : ℝ)) * (S.toPrism3D.angle T.toPrism3D) := by rw [ht2]
      _ ≤ (2 * (c : ℝ)) * (2 * θ) := by
        exact mul_le_mul_of_nonneg_left hangle (by positivity)
      _ = 4 * θ * (c : ℝ) := by ring
  have hbc : (b : ℝ) ≤ (c : ℝ) := by exact_mod_cast b_le_c
  rw [hsum]
  set t₀ : ℝ := a 0 * inner ℝ (T.basis 0) (S.basis 0) with ht₀
  set t₁ : ℝ := a 1 * inner ℝ (T.basis 1) (S.basis 0) with ht₁
  set t₂ : ℝ := a 2 * inner ℝ (T.basis 2) (S.basis 0) with ht₂
  calc
    |t₀ + t₁ + t₂|
        ≤ |t₀ + t₁| + |t₂| := by
        exact abs_add_le _ _
      _ ≤ |t₀| + |t₁| + |t₂| := by
        exact add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 2 * (δ : ℝ) + 4 * θ * (b : ℝ) + 4 * θ * (c : ℝ) := by
        exact add_le_add (add_le_add hprod0 hprod1) hprod2
      _ ≤ 2 * (δ : ℝ) + 8 * θ * c := by
        nlinarith [hθ, hbc]

/-- The **neighbour prism** `K_i(θ)`: the rectangular prism with the centre and frame of `S`
and half-widths `min (3δ + 8θc) (7c)`, `7c`, `7c`.

The truncation by `7c` keeps the half-widths in increasing order, which is part of the type
`Prism3D`; it costs nothing, because `Prism3D.norm_sub_le_of_mem'` bounds every coordinate of a
neighbour by `7c` anyway. -/
def neighbourPrism (S : ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) (θ : ℝ) :
    Prism3D (min (3 * δ + 8 * θ.toNNReal * c) (7 * c)) (7 * c) (7 * c)
      (min_le_right _ _) le_rfl :=
  S.toPrism3D.resize (min_le_right _ _) le_rfl

/-- **Nearly parallel neighbours are confined.** A prism that meets `S` and makes an angle at
most `2θ` with it is contained in the neighbour prism `K(θ)` of `S`. -/
theorem subset_neighbourPrism (S T : ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) {θ : ℝ}
    (hθ : 0 < θ)
    (hmeet : ((S.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ T.carrier).Nonempty)
    (hangle : Prism3D.angle S.toPrism3D T.toPrism3D ≤ 2 * θ) :
    (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ (S.neighbourPrism θ).carrier := by
  intro y hy
  obtain ⟨x, hxS, hxT⟩ := hmeet
  let w : Fin 3 → NNReal := ![min (3 * δ + 8 * θ.toNNReal * c) (7 * c), 7 * c, 7 * c]
  have hthick_le_c : ∀ i : Fin 3, (S.toPrism3D.thicknesses i : ℝ) ≤ (c : ℝ) := by
    intro i
    rw [S.toPrism3D.thicknesses_eq]
    fin_cases i
    · exact_mod_cast (δ_le_b.trans b_le_c)
    · exact_mod_cast b_le_c
    · rfl
  have hxCoord : ∀ i : Fin 3,
      |inner ℝ (x - S.toPrism3D.center) (S.toPrism3D.basis i)|
        ≤ (S.toPrism3D.thicknesses i : ℝ) := by
    intro i
    have h := (S.toPrism3D.mem_carrier_iff x).1 hxS i
    rw [S.toPrism3D.basis.repr_apply_apply, real_inner_comm] at h
    exact h
  have hnorm : ‖y - x‖ ≤ 6 * (c : ℝ) :=
    Prism3D.norm_sub_le_of_mem' T.toPrism3D hxT hy
  have hyCoord : ∀ i : Fin 3, |inner ℝ (y - x) (S.toPrism3D.basis i)| ≤ 6 * (c : ℝ) := by
    intro i
    calc
      |inner ℝ (y - x) (S.toPrism3D.basis i)| ≤ ‖y - x‖ * ‖S.toPrism3D.basis i‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖y - x‖ := by rw [S.toPrism3D.basis.norm_eq_one, mul_one]
      _ ≤ 6 * (c : ℝ) := hnorm
  have hsum : ∀ i : Fin 3,
      |inner ℝ (y - S.toPrism3D.center) (S.toPrism3D.basis i)| ≤ 7 * (c : ℝ) := by
    intro i
    calc
      |inner ℝ (y - S.toPrism3D.center) (S.toPrism3D.basis i)|
          = |inner ℝ ((y - x) + (x - S.toPrism3D.center)) (S.toPrism3D.basis i)| := by
              congr 1
              abel_nf
      _ ≤ |inner ℝ (y - x) (S.toPrism3D.basis i)|
            + |inner ℝ (x - S.toPrism3D.center) (S.toPrism3D.basis i)| := by
              rw [inner_add_left]
              exact abs_add_le _ _
      _ ≤ 6 * (c : ℝ) + (c : ℝ) := by
              exact add_le_add (hyCoord i) ((hxCoord i).trans (hthick_le_c i))
      _ = 7 * (c : ℝ) := by ring
  have hshort : |inner ℝ (y - x) (S.toPrism3D.basis 0)|
      ≤ 2 * (δ : ℝ) + 8 * θ * c :=
    ShadedPrism3D.abs_inner_sub_shortAxis_le S T hθ hangle hxT hy
  have hδ0 : |inner ℝ (x - S.toPrism3D.center) (S.toPrism3D.basis 0)| ≤ (δ : ℝ) := by
    have h := (S.toPrism3D.mem_carrier_iff x).1 hxS 0
    rw [S.toPrism3D.basis.repr_apply_apply, real_inner_comm] at h
    rw [S.toPrism3D.thicknesses_eq] at h
    simpa using h
  have hA : |inner ℝ (y - S.toPrism3D.center) (S.toPrism3D.basis 0)|
      ≤ 3 * (δ : ℝ) + 8 * θ * c := by
    calc
      |inner ℝ (y - S.toPrism3D.center) (S.toPrism3D.basis 0)|
          = |inner ℝ ((y - x) + (x - S.toPrism3D.center)) (S.toPrism3D.basis 0)| := by
              congr 1
              abel_nf
      _ ≤ |inner ℝ (y - x) (S.toPrism3D.basis 0)|
            + |inner ℝ (x - S.toPrism3D.center) (S.toPrism3D.basis 0)| := by
              rw [inner_add_left]
              exact abs_add_le _ _
      _ ≤ (2 * (δ : ℝ) + 8 * θ * c) + (δ : ℝ) := add_le_add hshort hδ0
      _ = 3 * (δ : ℝ) + 8 * θ * c := by ring
  have htoNN : (θ.toNNReal : ℝ) = θ := Real.coe_toNNReal θ hθ.le
  have hc0 : (3 * δ + 8 * θ.toNNReal * c : ℝ) = 3 * (δ : ℝ) + 8 * θ * (c : ℝ) := by
    rw [htoNN]
  have hc7 : (7 * c : ℝ) = 7 * (c : ℝ) := by
    rfl
  have hw0 : (w 0 : ℝ) = min (3 * (δ : ℝ) + 8 * θ * (c : ℝ)) (7 * (c : ℝ)) := by
    dsimp [w]
    change min (3 * (δ : ℝ) + 8 * (θ.toNNReal : ℝ) * (c : ℝ)) (7 * (c : ℝ))
        = min (3 * (δ : ℝ) + 8 * θ * (c : ℝ)) (7 * (c : ℝ))
    rw [htoNN]
  -- assemble the membership in the neighbour prism
  rw [ShadedPrism3D.neighbourPrism]
  rw [(S.toPrism3D.resize (min_le_right _ _) le_rfl).mem_carrier_iff]
  intro i
  change |S.toPrism3D.basis.repr (y - S.toPrism3D.center) i| ≤ (w i : ℝ)
  fin_cases i
  · rw [S.toPrism3D.basis.repr_apply_apply, real_inner_comm]
    exact (le_min hA (hsum 0)).trans_eq hw0.symm
  · rw [S.toPrism3D.basis.repr_apply_apply, real_inner_comm]
    simpa [w] using (hsum 1)
  · rw [S.toPrism3D.basis.repr_apply_apply, real_inner_comm]
    simpa [w] using (hsum 2)

/-- **Volume of the neighbour prism.** `|K(θ)| ≤ 392 c² (3δ + 8θc)`. -/
theorem volume_neighbourPrism_le (S : ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) (θ : ℝ) :
    volume (S.neighbourPrism θ).carrier ≤
      392 * (c : ENNReal) ^ 2 * (3 * (δ : ENNReal) + 8 * ENNReal.ofReal θ * c) := by
  rw [Prism3D.volume_carrier]
  let m : NNReal := min (3 * δ + 8 * θ.toNNReal * c) (7 * c)
  calc
    8 * (m : ENNReal) * (7 * c) * (7 * c)
        = 392 * (c : ENNReal) ^ 2 * (m : ENNReal) := by
      ring
    _ ≤ 392 * (c : ENNReal) ^ 2 * (3 * (δ : ENNReal) + 8 * ENNReal.ofReal θ * c) := by
      gcongr
      calc
        (m : ENNReal) ≤ ((3 * δ + 8 * θ.toNNReal * c : NNReal) : ENNReal) := by
          simp [m]
        _ = 3 * (δ : ENNReal) + 8 * ENNReal.ofReal θ * c := by
          simp [ENNReal.ofReal]

/-- **Volume of the neighbour prism at a scale above `δ`.** If `δ ≤ θ` then
`|K(θ)| ≤ 4312 c² θ`. -/
theorem volume_neighbourPrism_le' (S : ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) {θ : ℝ}
    (hδθ : (δ : ℝ) ≤ θ) :
    volume (S.neighbourPrism θ).carrier ≤ 4312 * (c : ENNReal) ^ 2 * ENNReal.ofReal θ := by
  rw [Prism3D.volume_carrier]
  let m : NNReal := min (3 * δ + 8 * θ.toNNReal * c) (7 * c)
  calc
    8 * (m : ENNReal) * (7 * c) * (7 * c)
        = 392 * (c : ENNReal) ^ 2 * (m : ENNReal) := by
      ring
    _ ≤ 392 * (c : ENNReal) ^ 2 * (3 * (δ : ENNReal) + 8 * ENNReal.ofReal θ * c) := by
      gcongr
      calc
        (m : ENNReal) ≤ ((3 * δ + 8 * θ.toNNReal * c : NNReal) : ENNReal) := by
          simp [m]
        _ = 3 * (δ : ENNReal) + 8 * ENNReal.ofReal θ * c := by
          simp [ENNReal.ofReal]
    _ ≤ 392 * (c : ENNReal) ^ 2 * (3 * ENNReal.ofReal θ + 8 * ENNReal.ofReal θ * 1) := by
      gcongr
      · simpa [ENNReal.ofReal] using (ENNReal.ofReal_le_ofReal hδθ :
          ENNReal.ofReal (δ : ℝ) ≤ ENNReal.ofReal θ)
      · exact_mod_cast c_le_one
    _ = 4312 * (c : ENNReal) ^ 2 * ENNReal.ofReal θ := by
      ring

open scoped Classical in
/-- The set of indices `j ∈ s` whose prism meets `V i` and makes an angle at most `2θ` with it.
Its cardinality is the quantity called `N_i(θ)` in the blueprint. -/
def neighbours (s : Finset ι) (V : ι → ShadedPrism3D δ b c δ_le_b b_le_c c_le_one)
    (i : ι) (θ : ℝ) : Finset ι :=
  {j ∈ s | ((V i).carrier ∩ (V j).carrier : Set (EuclideanSpace ℝ (Fin 3))).Nonempty ∧
    Prism3D.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 * θ}

/-- **Counting the neighbours.** `N_i(θ) · δ b ≤ 539 · Δ_max(𝒮) · θ`.

The conclusion is stated as a product rather than as the quotient
`N_i(θ) ≤ 539 Δ_max(𝒮) θ / (δ b)`, since all the quantities are `ENNReal`-valued. -/
theorem card_neighbours_mul_le_maxDensity (s : Finset ι)
    (V : ι → ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) (i : ι) {θ : ℝ}
    (hδ_pos : 0 < δ) (hδθ : (δ : ℝ) ≤ θ) :
    ((neighbours s V i θ).card : ENNReal) * ((δ : ENNReal) * b) ≤
      539 * Kakeya.maxDensity s (fun j => (V j).toConvexSpaceBody) * ENNReal.ofReal θ := by
  let t : Finset ι := neighbours s V i θ
  let K := (V i).neighbourPrism θ
  let KBody : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := K.toConvexSpaceBody
  let Δ : ENNReal := Kakeya.maxDensity s (fun j => (V j).toConvexSpaceBody)
  have hθ : 0 < θ := lt_of_lt_of_le (by exact_mod_cast hδ_pos) hδθ
  have hc_pos : 0 < (c : NNReal) := lt_of_lt_of_le hδ_pos (δ_le_b.trans b_le_c)
  have hc_ne_zero : (c : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hc_pos.ne'
  have hc_ne_top : (c : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h8c_ne_zero : (8 : ENNReal) * (c : ENNReal) ≠ 0 :=
    mul_ne_zero (by norm_num) hc_ne_zero
  have h8c_ne_top : (8 : ENNReal) * (c : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hc_ne_top
  have hc_le_one : (c : ENNReal) ≤ 1 := by exact_mod_cast c_le_one
  -- every neighbour is contained in the neighbour prism `K`
  have hsub : t ⊆ {j ∈ s | (V j).toConvexSpaceBody ≤ KBody} := by
    intro j hj
    rcases (by simpa [t, neighbours] using hj) with ⟨hjs, hmeet, hangle⟩
    refine Finset.mem_filter.mpr ⟨hjs, ?_⟩
    have hinc : (V j).toConvexSpaceBody ≤ KBody := by
      change (V j).carrier ⊆ K.carrier
      simpa [K] using (subset_neighbourPrism (V i) (V j) hθ hmeet hangle)
    exact hinc
  -- sum of the volumes of the neighbours is bounded by `Δ · |K|`
  have hsum : ∑ j ∈ t, volume (V j).carrier ≤ Δ * volume K.carrier := by
    calc
      ∑ j ∈ t, volume (V j).carrier
          ≤ ∑ j ∈ {j ∈ s | (V j).toConvexSpaceBody ≤ KBody}, volume (V j).carrier := by
            exact Finset.sum_le_sum_of_subset hsub
      _ ≤ Δ * volume K.carrier := by
        simpa [Δ, K, KBody] using
          (Kakeya.sum_volume_le_maxDensity_mul_volume s
            (fun j => (V j).toConvexSpaceBody) KBody)
  -- each neighbour has volume exactly `8 δ b c`
  have hmain : t.card * ((δ : ENNReal) * b) ≤ (539 * Δ * ENNReal.ofReal θ) * (c : ENNReal) := by
    have hcard : ∑ j ∈ t, volume (V j).carrier = t.card * (8 * (δ : ENNReal) * b * c) := by
      calc
        ∑ j ∈ t, volume (V j).carrier
            = ∑ j ∈ t, (8 * (δ : ENNReal) * b * c) := by
              exact Finset.sum_congr rfl
                (by intro j hj; simpa using (Prism3D.volume_carrier (V j).toPrism3D))
        _ = t.card * (8 * (δ : ENNReal) * b * c) := by simp
    have hvolK : volume K.carrier ≤ 4312 * (c : ENNReal) ^ 2 * ENNReal.ofReal θ := by
      simpa [K] using (volume_neighbourPrism_le' (V i) hδθ)
    have hineq : t.card * (8 * (δ : ENNReal) * b * c) ≤
        Δ * (4312 * (c : ENNReal) ^ 2 * ENNReal.ofReal θ) := by
      calc
        t.card * (8 * (δ : ENNReal) * b * c) = ∑ j ∈ t, volume (V j).carrier := hcard.symm
        _ ≤ Δ * volume K.carrier := hsum
        _ ≤ Δ * (4312 * (c : ENNReal) ^ 2 * ENNReal.ofReal θ) :=
          mul_le_mul_of_nonneg_left hvolK (by simp)
    have hfactor : (8 * (c : ENNReal)) * (t.card * ((δ : ENNReal) * b)) ≤
        (8 * (c : ENNReal)) * ((539 * Δ * ENNReal.ofReal θ) * (c : ENNReal)) := by
      have hL : (8 * (c : ENNReal)) * (t.card * ((δ : ENNReal) * b)) =
          t.card * (8 * (δ : ENNReal) * b * c) := by ring
      have hR : (8 * (c : ENNReal)) * ((539 * Δ * ENNReal.ofReal θ) * (c : ENNReal)) =
          Δ * (4312 * (c : ENNReal) ^ 2 * ENNReal.ofReal θ) := by ring
      rw [hL, hR]
      exact hineq
    have hcancel : t.card * ((δ : ENNReal) * b) ≤ (539 * Δ * ENNReal.ofReal θ) * (c : ENNReal) :=
      (ENNReal.mul_le_mul_iff_right h8c_ne_zero h8c_ne_top).mp hfactor
    simpa using hcancel
  have hfinal : t.card * ((δ : ENNReal) * b) ≤ 539 * Δ * ENNReal.ofReal θ := by
    calc
      t.card * ((δ : ENNReal) * b) ≤ (539 * Δ * ENNReal.ofReal θ) * (c : ENNReal) := hmain
      _ ≤ 539 * Δ * ENNReal.ofReal θ := by
        simpa using (mul_le_mul_of_nonneg_left hc_le_one
          (by simp : 0 ≤ (539 * Δ * ENNReal.ofReal θ : ENNReal)))
  simpa [t, Δ] using hfinal

/-- **The incidences at a single angle.** `Tri_θ(𝒮, Y) · b ≤ 21560 · |r| · Δ_max(𝒮) · δ`.

The factor `θ` cancels, which is what makes the argument uniform in the angle scale. -/
theorem triAtAngle_mul_le_maxDensity (s : Finset ι)
    (V : ι → ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) {θ : ℝ}
    (hδ_pos : 0 < δ) (hδθ : (δ : ℝ) ≤ θ) :
    triAtAngle s V θ * (b : ENNReal) ≤
      21560 * (s.card : ENNReal) *
        Kakeya.maxDensity s (fun j => (V j).toConvexSpaceBody) * (δ : ENNReal) := by
  classical
  have hθ_pos : 0 < θ := lt_of_lt_of_le (by exact_mod_cast hδ_pos) hδθ
  let B : ENNReal := 40 * (δ : ENNReal) ^ 2 / ENNReal.ofReal θ
  let Δn : ENNReal := Kakeya.maxDensity s (fun j => (V j).toConvexSpaceBody)
  let F : ι → Finset ι := fun i =>
    {j ∈ s | θ - δ ≤ Prism3D.angle (V i).toPrism3D (V j).toPrism3D ∧
      Prism3D.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 * θ}
  let N : ι → Finset ι := fun i => neighbours s V i θ
  have hpair : ∀ i j, θ - δ ≤ Prism3D.angle (V i).toPrism3D (V j).toPrism3D →
      volume ((V i).shade ∩ (V j).shade) ≤ B := by
    intro i j hangle
    have hangle' : θ - δ ≤
        Slab.angle (V i).toShadedSlab.toPrism3D (V j).toShadedSlab.toPrism3D := by
      simpa [angle_toShadedSlab] using hangle
    simpa [B, shade_toShadedSlab, ShadedSlab.triAtAngle_le_card_sq_theta.C] using
      (ShadedSlab.volume_shade_inter_le
        (V i).toShadedSlab (V j).toShadedSlab hδ_pos hδθ hangle')
  have htri : triAtAngle s V θ =
      ∑ i ∈ s, ∑ j ∈ F i, volume ((V i).shade ∩ (V j).shade) := by
    simp [triAtAngle, ShadedSlab.triAtAngle_def, slabs, F, angle_toShadedSlab,
      shade_toShadedSlab]
  have hper : ∀ i, (∑ j ∈ F i, volume ((V i).shade ∩ (V j).shade)) * (b : ENNReal) ≤
      21560 * Δn * (δ : ENNReal) := by
    intro i
    have h_eq : (∑ j ∈ F i, volume ((V i).shade ∩ (V j).shade)) =
        ∑ j ∈ F i ∩ N i, volume ((V i).shade ∩ (V j).shade) := by
      refine (Finset.sum_subset ?hsubset ?hvan).symm
      · exact Finset.inter_subset_left
      · intro x hx hxn
        have hxf : x ∈ F i := hx
        have hxN : x ∉ N i := by
          intro hiN
          exact hxn (Finset.mem_inter.mpr ⟨hxf, hiN⟩)
        have memF : x ∈ s ∧
            (θ - δ ≤ Prism3D.angle (V i).toPrism3D (V x).toPrism3D ∧
              Prism3D.angle (V i).toPrism3D (V x).toPrism3D ≤ 2 * θ) :=
          Finset.mem_filter.mp hxf
        have hne : ¬ ((V i).carrier ∩ (V x).carrier : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
          intro H
          have hxN' : x ∉ neighbours s V i θ := by simpa [N] using hxN
          exact hxN' (by
            rw [neighbours]
            exact Finset.mem_filter.mpr ⟨memF.1, ⟨H, memF.2.2⟩⟩)
        have hsubset2 : (V i).shade ∩ (V x).shade ⊆ (V i).carrier ∩ (V x).carrier :=
          Set.inter_subset_inter (V i).shade_subset (V x).shade_subset
        have hcar : (V i).carrier ∩ (V x).carrier = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro y hy
          exact hne ⟨y, hy⟩
        have hh : (((V i).shade ∩ (V x).shade) : Set (EuclideanSpace ℝ (Fin 3))) ⊆
            (∅ : Set (EuclideanSpace ℝ (Fin 3))) := by
          simpa [hcar] using hsubset2
        have hvol : volume ((V i).shade ∩ (V x).shade) = 0 := by
          have hmono : volume ((V i).shade ∩ (V x).shade) ≤
              volume (∅ : Set (EuclideanSpace ℝ (Fin 3))) := measure_mono hh
          simpa using hmono
        exact hvol
    have hle_bounded : (∑ j ∈ F i, volume ((V i).shade ∩ (V j).shade)) ≤ (N i).card * B := by
      rw [h_eq]
      calc
        ∑ j ∈ F i ∩ N i, volume ((V i).shade ∩ (V j).shade)
            ≤ ∑ j ∈ F i ∩ N i, B := by
              refine Finset.sum_le_sum fun j hj => hpair i j
                (Finset.mem_filter.mp (Finset.mem_inter.mp hj).1).2.1
        _ = (F i ∩ N i).card * B := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (N i).card * B := by
              have hcard : ((F i ∩ N i).card : ENNReal) ≤ ((N i).card : ENNReal) := by
                exact_mod_cast (Finset.card_le_card
                  (Finset.inter_subset_right : F i ∩ N i ⊆ N i))
              exact mul_le_mul' hcard (le_refl B)
    calc
      (∑ j ∈ F i, volume ((V i).shade ∩ (V j).shade)) * (b : ENNReal)
          ≤ ((N i).card * B) * (b : ENNReal) := by
            exact mul_le_mul' hle_bounded (le_refl (b : ENNReal))
      _ = ((N i).card * ((δ : ENNReal) * b)) * (40 * (δ : ENNReal) / ENNReal.ofReal θ) := by
            simp [B, ENNReal.div_eq_inv_mul]
            ring
      _ ≤ (539 * Δn * ENNReal.ofReal θ) * (40 * (δ : ENNReal) / ENNReal.ofReal θ) := by
            have hnb := card_neighbours_mul_le_maxDensity s V i hδ_pos hδθ
            simpa [N, Δn] using
              (mul_le_mul' hnb (le_refl (40 * (δ : ENNReal) / ENNReal.ofReal θ)))
      _ = 21560 * Δn * (δ : ENNReal) := by
            have hθ_ne0 : ENNReal.ofReal θ ≠ 0 := (ENNReal.ofReal_pos.mpr hθ_pos).ne'
            have hθ_ne_top : ENNReal.ofReal θ ≠ ⊤ := ENNReal.ofReal_ne_top
            have hcancel : ENNReal.ofReal θ * (40 * (δ : ENNReal) / ENNReal.ofReal θ) =
                40 * (δ : ENNReal) := by
              rw [ENNReal.div_eq_inv_mul]
              exact ENNReal.mul_inv_cancel_left hθ_ne0 hθ_ne_top
            calc
              (539 * Δn * ENNReal.ofReal θ) * (40 * (δ : ENNReal) / ENNReal.ofReal θ)
                  = 539 * Δn * (ENNReal.ofReal θ * (40 * (δ : ENNReal) / ENNReal.ofReal θ)) := by
                        ring
              _ = 539 * Δn * (40 * (δ : ENNReal)) := by rw [hcancel]
              _ = 21560 * Δn * (δ : ENNReal) := by ring
  calc
    triAtAngle s V θ * (b : ENNReal)
        = (∑ i ∈ s, (∑ j ∈ F i, volume ((V i).shade ∩ (V j).shade)) * (b : ENNReal)) := by
          rw [htri]
          rw [Finset.sum_mul]
    _ ≤ (s.card : ENNReal) * (21560 * Δn * (δ : ENNReal)) := by
          calc
            ∑ i ∈ s, (∑ j ∈ F i, volume ((V i).shade ∩ (V j).shade)) * (b : ENNReal)
                ≤ ∑ i ∈ s, (21560 * Δn * (δ : ENNReal)) := by
                  refine Finset.sum_le_sum fun i hi => hper i
            _ = (s.card : ENNReal) * (21560 * Δn * (δ : ENNReal)) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
    _ = 21560 * (s.card : ENNReal) * Δn * (δ : ENNReal) := by ring

/-! ### Choosing the angle scale -/

/-- The dyadic angle scale `θ_k = 2^k δ`. -/
def angleScale (δ : NNReal) (k : ℕ) : ℝ := 2 ^ k * (δ : ℝ)

/-- The top index `K(δ) = ⌈log₂ (π / (4δ))⌉₊` of the dyadic angle scales.

The natural ceiling `Nat.ceil` is `0` on negative arguments, which happens exactly when
`δ > π / 4`; then there is a single scale `θ₀ = δ`. -/
def maxAngleScaleIndex (δ : NNReal) : ℕ := ⌈Real.logb 2 (Real.pi / (4 * δ))⌉₊

/-- The number `M(δ) = K(δ) + 1` of dyadic angle scales. -/
def numAngleScales (δ : NNReal) : ℕ := maxAngleScaleIndex δ + 1

/-- **Number of scales.** `M(δ) ≤ log₂ (δ⁻¹) + 2`. -/
theorem numAngleScales_le {δ : NNReal} (hδ_pos : 0 < δ) (hδ1 : δ < 1) :
    (numAngleScales δ : ℝ) ≤ Real.logb 2 ((δ : ℝ)⁻¹) + 2 := by
  let L : ℝ := Real.logb 2 ((δ : ℝ)⁻¹)
  let x : ℝ := Real.logb 2 (Real.pi / (4 * δ))
  have hδℝ : 0 < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hδℝ_ne : (δ : ℝ) ≠ 0 := ne_of_gt hδℝ
  have hδ1ℝ : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hδinv_gt : 1 < (δ : ℝ)⁻¹ := (one_lt_inv₀ hδℝ).2 hδ1ℝ
  have hL_pos : 0 < L := by
    unfold L
    exact Real.logb_pos (by norm_num : 1 < (2 : ℝ)) hδinv_gt
  have hdecomp : Real.pi / (4 * δ) = (δ : ℝ)⁻¹ * (Real.pi / 4) := by
    field_simp [hδℝ_ne]
  have hlog_decomp : x = L + Real.logb 2 (Real.pi / 4) := by
    unfold x L
    rw [hdecomp]
    rw [Real.logb_mul (inv_ne_zero hδℝ_ne) (ne_of_gt (by positivity : 0 < Real.pi / 4))]
  have hpi4_le_one : Real.pi / 4 ≤ 1 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    simpa using Real.pi_le_four
  have hlog4_nonpos : Real.logb 2 (Real.pi / 4) ≤ 0 :=
    Real.logb_nonpos (by norm_num : 1 < (2 : ℝ)) (by positivity : 0 ≤ Real.pi / 4) hpi4_le_one
  have hx_le_L : x ≤ L := by
    rw [hlog_decomp]
    nlinarith [hlog4_nonpos]
  by_cases hxneg : x < 0
  · have hIdx0 : maxAngleScaleIndex δ = 0 := by
      unfold maxAngleScaleIndex
      rw [Nat.ceil_eq_zero]
      simpa [x] using (le_of_lt hxneg)
    rw [show (numAngleScales δ : ℝ) = 1 by
        unfold numAngleScales
        rw [hIdx0]
        norm_num]
    change (1 : ℝ) ≤ L + 2
    linarith
  · have hx_nonneg : 0 ≤ x := le_of_not_gt hxneg
    have hIdx : maxAngleScaleIndex δ = ⌈x⌉₊ := by
      unfold maxAngleScaleIndex
      rfl
    have hceil_lt : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx_nonneg
    have hinter : (⌈x⌉₊ : ℝ) + 1 ≤ L + 2 := by
      linarith [hceil_lt, hx_le_L]
    unfold numAngleScales
    rw [hIdx]
    push_cast
    exact hinter

/-- **The top scale reaches `π / 2`.** -/
theorem pi_div_two_le_angleScale {δ : NNReal} (hδ_pos : 0 < δ) :
    Real.pi / 2 ≤ 2 * angleScale δ (maxAngleScaleIndex δ) := by
  let K := maxAngleScaleIndex δ
  let x := Real.logb 2 (Real.pi / (4 * (δ : ℝ)))
  have hK : x ≤ (K : ℝ) := by
    dsimp [x, K]
    exact Nat.le_ceil _
  have hxpow : (2 : ℝ) ^ x = Real.pi / (4 * (δ : ℝ)) := by
    dsimp [x]
    exact Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
      (by positivity : 0 < Real.pi / (4 * (δ : ℝ)))
  have hpow : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ (K : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hK
  have hdiv : Real.pi / (4 * (δ : ℝ)) ≤ (2 : ℝ) ^ (K : ℝ) := by
    simpa [hxpow] using hpow
  have h2K : (2 : ℝ) ^ (K : ℝ) = (2 : ℝ) ^ K :=
    Real.rpow_natCast (2 : ℝ) K
  have hπ : Real.pi ≤ 4 * ((2 : ℝ) ^ K) * (δ : ℝ) := by
    have hmul : Real.pi ≤ (2 : ℝ) ^ (K : ℝ) * (4 * (δ : ℝ)) := by
      exact (div_le_iff₀ (by positivity : 0 < 4 * (δ : ℝ))).mp hdiv
    calc
      Real.pi ≤ (2 : ℝ) ^ (K : ℝ) * (4 * (δ : ℝ)) := hmul
      _ = (4 * (2 : ℝ) ^ (K : ℝ)) * (δ : ℝ) := by ring
      _ = 4 * ((2 : ℝ) ^ K) * (δ : ℝ) := by rw [h2K]
  have hfinal : Real.pi / 2 ≤ 2 * (2 ^ K * (δ : ℝ)) := by
    nlinarith [hπ]
  simpa [angleScale, K] using hfinal

/-- **The angle windows cover `[0, π/2]`.** -/
theorem exists_angleScale_window {δ : NNReal} (hδ_pos : 0 < δ) {φ : ℝ}
    (hφ₀ : 0 ≤ φ) (hφ : φ ≤ Real.pi / 2) :
    ∃ k ≤ maxAngleScaleIndex δ, angleScale δ k - δ ≤ φ ∧ φ ≤ 2 * angleScale δ k := by
  classical
  let p : ℕ → Prop := fun k => φ ≤ 2 * angleScale δ k
  have hp_max : p (maxAngleScaleIndex δ) := by
    exact hφ.trans (pi_div_two_le_angleScale hδ_pos)
  let H : ∃ n, p n := ⟨maxAngleScaleIndex δ, hp_max⟩
  have hk_le : Nat.find H ≤ maxAngleScaleIndex δ := Nat.find_le (h := H) hp_max
  have hpk : p (Nat.find H) := Nat.find_spec H
  refine ⟨Nat.find H, hk_le, ?_, hpk⟩
  cases hk : Nat.find H with
  | zero =>
      have : angleScale δ 0 - δ = 0 := by simp [angleScale]
      simpa [this] using hφ₀
  | succ m =>
      have hmin : ¬ p m := by
        have hlt : m < Nat.find H := by
          rw [hk]
          exact Nat.lt_succ_self m
        exact Nat.find_min H hlt
      have hgr : 2 * angleScale δ m < φ := lt_of_not_ge hmin
      have hstep : 2 * angleScale δ m = angleScale δ (m + 1) := by
        simp [angleScale]
        ring
      have hlt : angleScale δ (m + 1) < φ := by
        simpa [hstep] using hgr
      have hdif : angleScale δ (m + 1) - δ ≤ angleScale δ (m + 1) := by
        have hδ_nonneg : 0 ≤ (δ : ℝ) := by exact_mod_cast (le_of_lt hδ_pos)
        linarith
      exact le_trans hdif (le_of_lt hlt)

/-- **The windows exhaust the incidences.**
`Tri(𝒮, Y) ≤ ∑_{k ≤ K(δ)} Tri_{θ_k}(𝒮, Y)`. -/
theorem tri_le_sum_triAtAngle (s : Finset ι)
    (V : ι → ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) (hδ_pos : 0 < δ) :
    tri s V ≤ ∑ k ∈ Finset.range (numAngleScales δ), triAtAngle s V (angleScale δ k) := by
  let M := numAngleScales δ
  let φ : ι → ι → ℝ := fun i j => Prism3D.angle (V i).toPrism3D (V j).toPrism3D
  let p : ℕ → ι → ι → Prop := fun k i j => angleScale δ k ≤ φ i j + ↑δ ∧ φ i j ≤ 2 * angleScale δ k
  let f : ι → ι → ENNReal := fun i j => volume ((V i).shade ∩ (V j).shade)
  have htri : tri s V = ∑ i ∈ s, ∑ j ∈ s, f i j := by
    simp [tri, ShadedSlab.tri_def, slabs, f, shade_toShadedSlab]
  have htriAt : ∑ k ∈ Finset.range M, triAtAngle s V (angleScale δ k)
      = ∑ k ∈ Finset.range M, ∑ i ∈ s, ∑ j ∈ s with p k i j, f i j := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [triAtAngle, ShadedSlab.triAtAngle_def, slabs, φ, p, f, angle_toShadedSlab,
      shade_toShadedSlab]
  calc
    tri s V = ∑ i ∈ s, ∑ j ∈ s, f i j := htri
    _ ≤ ∑ i ∈ s, ∑ k ∈ Finset.range M, ∑ j ∈ s, if p k i j then f i j else 0 := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun j _ => ?_
      obtain ⟨k, hk_le, hpk⟩ := exists_angleScale_window hδ_pos
        (Prism3D.angle_nonneg (V i).toPrism3D (V j).toPrism3D)
        (Prism3D.angle_le_pi_div_two (V i).toPrism3D (V j).toPrism3D)
      have hpk₁ : angleScale δ k ≤ φ i j + δ := sub_le_iff_le_add.mp hpk.1
      have hk_mem : k ∈ Finset.range M := by
        simpa [M, numAngleScales] using Nat.lt_succ_of_le hk_le
      have hnonneg : ∀ x ∈ Finset.range M,
          0 ≤ (fun x => if p x i j then f i j else 0) x := by
        intro x hx
        simp [p, φ]
      have hsingle := Finset.single_le_sum (s := Finset.range M)
        (f := fun x => if p x i j then f i j else 0) hnonneg hk_mem
      simpa [p, φ, hpk.2, hpk₁] using hsingle
    _ = ∑ i ∈ s, ∑ k ∈ Finset.range M, ∑ j ∈ s with p k i j, f i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_filter]
    _ = ∑ k ∈ Finset.range M, ∑ i ∈ s, ∑ j ∈ s with p k i j, f i j := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range M, triAtAngle s V (angleScale δ k) := htriAt.symm

/-- **Existence of a typical angle for prisms.** Some dyadic scale `θ_k ≥ δ` is an
`M(δ)`-typical intersection angle. -/
theorem exists_isTypicalIntersectionAngle (s : Finset ι)
    (V : ι → ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) (hδ_pos : 0 < δ) :
    ∃ k ≤ maxAngleScaleIndex δ,
      ShadedSlab.IsTypicalIntersectionAngle s (slabs V) (angleScale δ k)
        (numAngleScales δ : ENNReal) ∧ (δ : ℝ) ≤ angleScale δ k := by
  let M : ℕ := numAngleScales δ
  let a : ℕ → ENNReal := fun k => triAtAngle s V (angleScale δ k)
  have hM_pos : 0 < M := by
    dsimp [M, numAngleScales]
    exact Nat.succ_pos (maxAngleScaleIndex δ)
  have hrange : (Finset.range M).Nonempty := Finset.nonempty_range_iff.mpr (ne_of_gt hM_pos)
  obtain ⟨k₀, hk₀_mem, hk₀_max⟩ := Finset.exists_max_image (Finset.range M) a hrange
  have hk₀_lt : k₀ < M := by simpa using hk₀_mem
  have hk₀le : k₀ ≤ maxAngleScaleIndex δ := by
    have h : k₀ < maxAngleScaleIndex δ + 1 := by simpa [M, numAngleScales] using hk₀_lt
    exact Nat.lt_succ_iff.mp h
  have hsum : (∑ k ∈ Finset.range M, a k) ≤ (M : ENNReal) * a k₀ := by
    have h := Finset.sum_le_card_nsmul (s := Finset.range M) (f := a) (n := a k₀) (by
      intro x hx
      exact hk₀_max x hx)
    rwa [Finset.card_range, nsmul_eq_mul] at h
  have htri : tri s V ≤ (M : ENNReal) * a k₀ := by
    calc
      tri s V ≤ ∑ k ∈ Finset.range M, a k := by
        simpa [a, M] using (tri_le_sum_triAtAngle s V hδ_pos)
      _ ≤ (M : ENNReal) * a k₀ := hsum
  refine ⟨k₀, hk₀le, ?_, ?_⟩
  · change ShadedSlab.tri s (slabs V) ≤
      (numAngleScales δ : ENNReal) * ShadedSlab.triAtAngle s (slabs V) (angleScale δ k₀)
    simpa [a, M] using htri
  · dsimp [angleScale]
    exact le_mul_of_one_le_left (by exact_mod_cast (le_of_lt hδ_pos))
      (by exact_mod_cast (Nat.one_le_two_pow))

/-! ### From the incidence count to the multiplicity -/

/-- **Multiplicity is controlled by the incidences at a typical angle.**
`μ(𝒮, Y) ∑_{i ∈ r} |Y_i| ≤ M · Tri_θ(𝒮, Y)`.

The product form removes the nondegeneracy hypothesis `∑_{i ∈ r} |Y_i| > 0` that the
quotient form would need. -/
theorem multiplicity_mul_sum_shade_le_triAtAngle (s : Finset ι)
    (V : ι → ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) {θ : ℝ} {M : ENNReal}
    (h_typ : ShadedSlab.IsTypicalIntersectionAngle s (slabs V) θ M) :
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody) *
        (∑ i ∈ s, volume (V i).shade) ≤ M * triAtAngle s V θ := by
  classical
  set μ : ENNReal := ShadedBody.multiplicity s (fun i => (V i).toShadedBody) with hμ
  set S : ENNReal := ∑ i ∈ s, volume (V i).shade with hS
  set U : ENNReal := volume (⋃ i ∈ s, (V i).shade) with hUdef
  -- the total shade mass is the multiplicity times the union volume
  have hmu : μ * U = S := by
    rw [hμ, hUdef, hS]
    exact ShadedBody.multiplicity_mul_union s (fun i => (V i).toShadedBody)
  -- Cauchy-Schwarz at the typical angle, read off the enclosing slab family
  have hcs : S ^ 2 ≤ M * U * triAtAngle s V θ := by
    rw [hS, hUdef]
    simpa using (ShadedSlab.sum_shade_sq_le_union_mul_triAtAngle s (slabs V) θ M h_typ)
  by_cases hU0 : U = 0
  · -- degenerate case: empty union, so no shade mass
    rw [hUdef] at hU0
    have hS0 : S = 0 := by
      rw [hS]
      exact Finset.sum_eq_zero
        (fun i hi => measure_mono_null (fun x hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩) hU0)
    rw [hS0, mul_zero]
    exact zero_le
  · -- nondegenerate case: cancel the (nonzero, finite) union volume
    have hUtop : U ≠ ⊤ := by
      rw [hUdef]
      exact ShadedBody.volume_iUnion_shade_ne_top s (fun i => (V i).toShadedBody)
    have hbound : U * (μ * S) ≤ U * (M * triAtAngle s V θ) := by
      calc
        U * (μ * S) = S * (μ * U) := by ring
        _ = S * S := by rw [hmu]
        _ = S ^ 2 := by ring
        _ ≤ M * U * triAtAngle s V θ := hcs
        _ = U * (M * triAtAngle s V θ) := by ring
    exact (ENNReal.mul_le_mul_iff_right (a := U) hU0 hUtop).mp hbound

/-- **Master multiplicity estimate for prisms.**
`μ(𝒮, Y) λ(𝒮, Y) b² c ≤ 2695 M(δ) Δ_max(𝒮)`.

The multiplicative form needs no lower bound on `λ(𝒮, Y)`. -/
theorem multiplicity_mul_le_maxDensity (s : Finset ι)
    (V : ι → ShadedPrism3D δ b c δ_le_b b_le_c c_le_one)
    (hδ_pos : 0 < δ) (hs : s.Nonempty) :
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody) *
        (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) *
          ((b : ENNReal) ^ 2 * c) ≤
      2695 * (numAngleScales δ : ENNReal) *
        Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody) := by
  let μ : ENNReal := ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
  let lam : ENNReal := (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal)
  let Δ : ENNReal := Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody)
  let δe : ENNReal := (δ : ENNReal)
  let be : ENNReal := (b : ENNReal)
  let ce : ENNReal := (c : ENNReal)
  let n : ENNReal := (s.card : ENNReal)
  let M : ENNReal := (numAngleScales δ : ENNReal)
  obtain ⟨k, hk_le, h_typ, hδθ⟩ := exists_isTypicalIntersectionAngle s V hδ_pos
  let θ : ℝ := angleScale δ k
  have hstep : μ * lam * (be ^ 2 * ce) * (8 * n * δe) ≤ 2695 * M * Δ * (8 * n * δe) := by
    calc
      μ * lam * (be ^ 2 * ce) * (8 * n * δe)
          = (μ * (∑ i ∈ s, volume (V i).shade)) * be := by
              rw [sum_volume_shade_eq s V]
              ring
      _ ≤ (M * triAtAngle s V θ) * be := by
              exact mul_le_mul_left (multiplicity_mul_sum_shade_le_triAtAngle s V h_typ) be
      _ = M * (triAtAngle s V θ * be) := by
              ring
      _ ≤ M * (21560 * n * Δ * δe) := by
              exact mul_le_mul_right (triAtAngle_mul_le_maxDensity s V hδ_pos hδθ) M
      _ = 2695 * M * Δ * (8 * n * δe) := by
              ring
  have hQ_ne_zero : 8 * n * δe ≠ 0 := by
    change 8 * (s.card : ENNReal) * δe ≠ 0
    exact mul_ne_zero (mul_ne_zero (by norm_num : (8 : ENNReal) ≠ 0)
        (by exact_mod_cast hs.card_pos.ne'))
      (ENNReal.coe_ne_zero.mpr hδ_pos.ne')
  have hQ_ne_top : 8 * n * δe ≠ ⊤ := by
    change 8 * (s.card : ENNReal) * δe ≠ ⊤
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num : (8 : ENNReal) ≠ ⊤)
        (ENNReal.natCast_ne_top _)) ENNReal.coe_ne_top
  exact (ENNReal.mul_le_mul_iff_left hQ_ne_zero hQ_ne_top).mp hstep

/-- **GWZ Lemma 6.9, multiplicity form: the logarithmic form.**

This is what the argument actually establishes; the form stated by GWZ
(`ShadedPrism3D.multiplicity_le_rpow`) is deduced from it by absorbing the logarithm into two
of the remaining powers of `δ^{-η}`. -/
theorem multiplicity_le_log_form (s : Finset ι)
    (V : ι → ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) {η : ℝ}
    (hη : 0 < η) (hδ_pos : 0 < δ) (hδ1 : δ < 1) (hs : s.Nonempty)
    (hlam : (δ : ENNReal) ^ η ≤
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal))
    (hb : (δ : ENNReal) ^ η ≤ (b : ENNReal))
    (hc : (δ : ENNReal) ^ η ≤ (c : ENNReal))
    (hΔ : Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η)) :
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
      2695 * ENNReal.ofReal (Real.logb 2 ((δ : ℝ)⁻¹) + 2) * (δ : ENNReal) ^ (-6 * η) := by
  let μ : ENNReal := ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
  let lam : ENNReal := (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal)
  let Δ : ENNReal := Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody)
  let d : ENNReal := (δ : ENNReal)
  let be : ENNReal := (b : ENNReal)
  let ce : ENNReal := (c : ENNReal)
  let M : ENNReal := (numAngleScales δ : ENNReal)
  have hd_ne_zero : d ≠ 0 := ENNReal.coe_ne_zero.mpr hδ_pos.ne'
  have hd_ne_top : d ≠ ⊤ := ENNReal.coe_ne_top
  have hd_le_one : d ≤ 1 := by
    change (δ : ENNReal) ≤ 1
    exact_mod_cast hδ1.le
  -- Step 1: d^(4η) ≤ λ (b² c)
  have htwo : d ^ (η * (2 : ℝ)) = (d ^ η) ^ 2 := by
    rw [ENNReal.rpow_mul d η (2 : ℝ)]
    exact ENNReal.rpow_natCast (d ^ η) 2
  have hpow4 : d ^ (4 * η) = (d ^ η) * ((d ^ η) ^ 2 * d ^ η) := by
    calc
      d ^ (4 * η) = d ^ ((η + η * (2 : ℝ)) + η) := by congr 1; ring
      _ = d ^ (η + η * (2 : ℝ)) * d ^ η := by
        rw [ENNReal.rpow_add (η + η * (2 : ℝ)) η hd_ne_zero hd_ne_top]
      _ = (d ^ η * d ^ (η * (2 : ℝ))) * d ^ η := by
        rw [ENNReal.rpow_add η (η * (2 : ℝ)) hd_ne_zero hd_ne_top]
      _ = d ^ η * (d ^ (η * (2 : ℝ)) * d ^ η) := by ring
      _ = d ^ η * ((d ^ η) ^ 2 * d ^ η) := by rw [htwo]
  have hb2le : (d ^ η) ^ 2 ≤ be ^ 2 := by
    calc
      (d ^ η) ^ 2 = (d ^ η) * (d ^ η) := by ring
      _ ≤ (d ^ η) * be := by
        exact mul_le_mul' (le_refl (d ^ η)) hb
      _ ≤ be * be := by
        exact mul_le_mul' hb (le_refl be)
      _ = be ^ 2 := by ring
  have hprod : (d ^ η) * ((d ^ η) ^ 2 * d ^ η) ≤ lam * (be ^ 2 * ce) := by
    exact mul_le_mul' hlam (mul_le_mul' hb2le hc)
  have hd4_le : d ^ (4 * η) ≤ lam * (be ^ 2 * ce) := by
    rw [hpow4]
    exact hprod
  -- Step 2: μ d^(4η) ≤ 2695 M Δ ≤ 2695 M d^(-η)
  have hmain : μ * d ^ (4 * η) ≤ 2695 * M * d ^ (-η) := by
    calc
      μ * d ^ (4 * η) ≤ μ * (lam * (be ^ 2 * ce)) := by
        exact mul_le_mul' (le_refl μ) hd4_le
      _ = μ * lam * (be ^ 2 * ce) := by ring
      _ ≤ 2695 * M * Δ := by
        simpa [μ, lam, be, ce, M, Δ] using (multiplicity_mul_le_maxDensity s V hδ_pos hs)
      _ ≤ 2695 * M * d ^ (-η) := by
        simpa [Δ, d] using (mul_le_mul' (le_refl (2695 * M)) hΔ)
  -- Step 3: cancel d^(4η)
  have hexp_0 : (4 * η) + (-4 * η) = 0 := by ring
  have hexp_54 : (-η) + (-4 * η) = -5 * η := by ring
  have hleft : μ * (d ^ (4 * η)) * d ^ (-4 * η) = μ := by
    calc
      μ * (d ^ (4 * η)) * d ^ (-4 * η) = μ * (d ^ (4 * η) * d ^ (-4 * η)) := by ring
      _ = μ * d ^ ((4 * η) + (-4 * η)) := by
        rw [ENNReal.rpow_add (4 * η) (-4 * η) hd_ne_zero hd_ne_top]
      _ = μ := by rw [hexp_0]; simp
  have hright : 2695 * M * d ^ (-η) * d ^ (-4 * η) = 2695 * M * d ^ (-5 * η) := by
    calc
      2695 * M * d ^ (-η) * d ^ (-4 * η) = (2695 * M) * (d ^ (-η) * d ^ (-4 * η)) := by ring
      _ = (2695 * M) * d ^ ((-η) + (-4 * η)) := by
        rw [ENNReal.rpow_add (-η) (-4 * η) hd_ne_zero hd_ne_top]
      _ = 2695 * M * d ^ (-5 * η) := by rw [hexp_54]
  have hdiv : μ ≤ 2695 * M * d ^ (-5 * η) := by
    have hmul' : μ * (d ^ (4 * η)) * d ^ (-4 * η) ≤ 2695 * M * d ^ (-η) * d ^ (-4 * η) :=
      mul_le_mul' hmain (le_refl _)
    calc
      μ = μ * (d ^ (4 * η)) * d ^ (-4 * η) := hleft.symm
      _ ≤ 2695 * M * d ^ (-η) * d ^ (-4 * η) := hmul'
      _ = 2695 * M * d ^ (-5 * η) := hright
  -- Step 4: d^(-5η) ≤ d^(-6η)
  have hdneg5_le : d ^ (-5 * η) ≤ d ^ (-6 * η) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hd_le_one (by linarith : (-6 * η) ≤ (-5 * η))
  have hstep4 : 2695 * M * d ^ (-5 * η) ≤ 2695 * M * d ^ (-6 * η) := by
    exact mul_le_mul' (le_refl (2695 * M)) hdneg5_le
  -- Step 5: M ≤ log₂(δ⁻¹) + 2
  have hM_cast : M = ENNReal.ofReal (numAngleScales δ : ℝ) := by
    change (numAngleScales δ : ENNReal) = ENNReal.ofReal (numAngleScales δ : ℝ)
    rw [← ENNReal.ofReal_natCast (numAngleScales δ)]
  have hM_le : M ≤ ENNReal.ofReal (Real.logb 2 ((δ : ℝ)⁻¹) + 2) := by
    rw [hM_cast]
    exact ENNReal.ofReal_le_ofReal (numAngleScales_le hδ_pos hδ1)
  have hstep5 : 2695 * M * d ^ (-6 * η) ≤
      2695 * ENNReal.ofReal (Real.logb 2 ((δ : ℝ)⁻¹) + 2) * d ^ (-6 * η) := by
    have hM' : 2695 * M ≤ 2695 * ENNReal.ofReal (Real.logb 2 ((δ : ℝ)⁻¹) + 2) :=
      mul_le_mul' (le_refl (2695 : ENNReal)) hM_le
    exact mul_le_mul' hM' (le_refl (d ^ (-6 * η)))
  have hconcl : μ ≤ 2695 * ENNReal.ofReal (Real.logb 2 ((δ : ℝ)⁻¹) + 2) * d ^ (-6 * η) := by
    calc
      μ ≤ 2695 * M * d ^ (-5 * η) := hdiv
      _ ≤ 2695 * M * d ^ (-6 * η) := hstep4
      _ ≤ 2695 * ENNReal.ofReal (Real.logb 2 ((δ : ℝ)⁻¹) + 2) * d ^ (-6 * η) := hstep5
  simpa [μ, d] using hconcl

/-! ### The form stated by GWZ -/

/-- **Absorbing a logarithm into a power.** `δ^{2η} log₂(δ⁻¹) ≤ 1 / (2η log 2)`.

The bound is not sharp — the supremum of the left-hand side is `(2eη)⁻¹` — but it has a
one-line proof and the same dependence on `η`. -/
theorem rpow_mul_logb_le {η : ℝ} (hη : 0 < η) {δ : ℝ} (hδ_pos : 0 < δ) (hδ1 : δ < 1) :
    δ ^ (2 * η) * Real.logb 2 δ⁻¹ ≤ 1 / (2 * η * Real.log 2) := by
  have hδpow : 0 < δ ^ (2 * η) := Real.rpow_pos_of_pos hδ_pos _
  have hδpow' : 0 < δ ^ (-(2 * η)) := Real.rpow_pos_of_pos hδ_pos _
  have h2η : 0 < 2 * η := by positivity
  -- 2η · log(δ⁻¹) ≤ δ^(-2η)
  have hmain : 2 * η * Real.log δ⁻¹ ≤ δ ^ (-(2 * η)) := by
    calc
      2 * η * Real.log δ⁻¹ = 2 * η * (-Real.log δ) := by rw [Real.log_inv]
      _ = (-(2 * η)) * Real.log δ := by ring
      _ = Real.log (δ ^ (-(2 * η))) := by rw [Real.log_rpow hδ_pos]
      _ ≤ δ ^ (-(2 * η)) := by
        calc
          Real.log (δ ^ (-(2 * η))) ≤ δ ^ (-(2 * η)) - 1 := Real.log_le_sub_one_of_pos hδpow'
          _ ≤ δ ^ (-(2 * η)) := by linarith
  -- δ^(2η) · log δ⁻¹ ≤ 1/(2η)
  have hdiv : δ ^ (2 * η) * Real.log δ⁻¹ ≤ 1 / (2 * η) := by
    have hmul : 2 * η * (δ ^ (2 * η) * Real.log δ⁻¹) ≤ 2 * η * (1 / (2 * η)) := by
      calc
        2 * η * (δ ^ (2 * η) * Real.log δ⁻¹) = δ ^ (2 * η) * (2 * η * Real.log δ⁻¹) := by ring
        _ ≤ δ ^ (2 * η) * δ ^ (-(2 * η)) := mul_le_mul_of_nonneg_left hmain (le_of_lt hδpow)
        _ = 1 := by
          rw [← Real.rpow_add hδ_pos (2 * η) (-(2 * η))]
          rw [show (2 * η + -(2 * η)) = 0 by ring, Real.rpow_zero]
        _ = 2 * η * (1 / (2 * η)) := by field_simp [ne_of_gt h2η]
    exact (mul_le_mul_iff_of_pos_left h2η).mp hmul
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    δ ^ (2 * η) * Real.logb 2 δ⁻¹ = δ ^ (2 * η) * (Real.log δ⁻¹ / Real.log 2) := rfl
    _ = (δ ^ (2 * η) * Real.log δ⁻¹) / Real.log 2 := by ring
    _ ≤ (1 / (2 * η)) / Real.log 2 := div_le_div_of_nonneg_right hdiv (le_of_lt hlog2)
    _ = 1 / (2 * η * Real.log 2) := by ring

/-- The constant `C_{6.9}(η) = 2695 (2 + 1 / (2 η log 2))` in
`ShadedPrism3D.multiplicity_le_rpow`.

It depends only on `η`, not on `δ`, on `b`, on `c` or on the family. It is decreasing in `η`
and blows up as `η → 0`; that is the price of `ShadedPrism3D.rpow_mul_logb_le`. -/
@[nolint defsWithUnderscore]
def multiplicity_le_rpow.C (η : ℝ) : NNReal :=
  Real.toNNReal (2695 * (2 + 1 / (2 * η * Real.log 2)))

/-- **(GWZ Lemma 6.9) Multiplicity of a family of `δ × b × c` slabs.**

If `λ(𝒮, Y) ≥ δ^η`, `b, c ≥ δ^η` and `Δ_max(𝒮) ≤ δ^{-η}`, then
`μ(𝒮, Y) ≤ C_{6.9}(η) δ^{-8η}`.

GWZ additionally assume that the slabs lie in the unit ball `B₁`; that hypothesis is not used,
all the containment information needed being carried by `Δ_max(𝒮)`, so it is omitted. -/
theorem multiplicity_le_rpow (s : Finset ι)
    (V : ι → ShadedPrism3D δ b c δ_le_b b_le_c c_le_one) {η : ℝ}
    (hη : 0 < η) (hδ_pos : 0 < δ) (hδ1 : δ < 1) (hs : s.Nonempty)
    (hlam : (δ : ENNReal) ^ η ≤
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal))
    (hb : (δ : ENNReal) ^ η ≤ (b : ENNReal))
    (hc : (δ : ENNReal) ^ η ≤ (c : ENNReal))
    (hΔ : Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η)) :
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
      (multiplicity_le_rpow.C η : ENNReal) * (δ : ENNReal) ^ (-8 * η) := by
  let d : ENNReal := (δ : ENNReal)
  let L : ℝ := Real.logb 2 ((δ : ℝ)⁻¹)
  have hd_ne_zero : d ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt hδ_pos)
  have hd_ne_top : d ≠ ⊤ := ENNReal.coe_ne_top
  have hδ_real_pos : 0 < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hδ_real_nonneg : 0 ≤ (δ : ℝ) := le_of_lt hδ_real_pos
  have hδ_real_le : (δ : ℝ) ≤ 1 := by exact_mod_cast (le_of_lt hδ1)
  have hδ_real_lt : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have h2η_nonneg : 0 ≤ 2 * η := by positivity
  have hq_nonneg : 0 ≤ (δ : ℝ) ^ (2 * η) := Real.rpow_nonneg hδ_real_nonneg _
  have hδp2_le_one : (δ : ℝ) ^ (2 * η) ≤ 1 :=
    Real.rpow_le_one hδ_real_nonneg hδ_real_le h2η_nonneg
  have hsplit : d ^ (2 * η) * d ^ (-8 * η) = d ^ (-6 * η) := by
    rw [← ENNReal.rpow_add (2 * η) (-8 * η) hd_ne_zero hd_ne_top]
    congr 1
    ring
  have hpow2 : d ^ (2 * η) = ENNReal.ofReal ((δ : ℝ) ^ (2 * η)) := by
    dsimp [d]
    rw [← ENNReal.ofReal_coe_nnreal]
    rw [ENNReal.ofReal_rpow_of_nonneg hδ_real_nonneg h2η_nonneg]
  have hterm1 : (δ : ℝ) ^ (2 * η) * L ≤ 1 / (2 * η * Real.log 2) := by
    dsimp [L]
    exact rpow_mul_logb_le hη hδ_real_pos hδ_real_lt
  have hterm2 : 2 * (δ : ℝ) ^ (2 * η) ≤ 2 := by
    nlinarith [hδp2_le_one, hq_nonneg]
  have hreal : (L + 2) * (δ : ℝ) ^ (2 * η) ≤ 2 + 1 / (2 * η * Real.log 2) := by
    calc
      (L + 2) * (δ : ℝ) ^ (2 * η)
          = (δ : ℝ) ^ (2 * η) * L + 2 * (δ : ℝ) ^ (2 * η) := by ring
      _ ≤ 1 / (2 * η * Real.log 2) + 2 := add_le_add hterm1 hterm2
      _ = 2 + 1 / (2 * η * Real.log 2) := by ring
  have hstep : 2695 * ENNReal.ofReal (L + 2) * ENNReal.ofReal ((δ : ℝ) ^ (2 * η)) =
      2695 * ENNReal.ofReal ((L + 2) * (δ : ℝ) ^ (2 * η)) := by
    calc
      2695 * ENNReal.ofReal (L + 2) * ENNReal.ofReal ((δ : ℝ) ^ (2 * η))
          = 2695 * (ENNReal.ofReal ((δ : ℝ) ^ (2 * η)) * ENNReal.ofReal (L + 2)) := by ring
      _ = 2695 * ENNReal.ofReal ((δ : ℝ) ^ (2 * η) * (L + 2)) := by
            rw [← ENNReal.ofReal_mul hq_nonneg]
      _ = 2695 * ENNReal.ofReal ((L + 2) * (δ : ℝ) ^ (2 * η)) := by
            congr 1
            ring_nf
  have hC_def : (multiplicity_le_rpow.C η : ENNReal) =
      2695 * ENNReal.ofReal (2 + 1 / (2 * η * Real.log 2)) := by
    change ENNReal.ofReal (2695 * (2 + 1 / (2 * η * Real.log 2))) =
        2695 * ENNReal.ofReal (2 + 1 / (2 * η * Real.log 2))
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (2695 : ℝ))]
    rw [← ENNReal.ofReal_ofNat]
  calc
    (ShadedBody.multiplicity s (fun i => (V i).toShadedBody))
        ≤ 2695 * ENNReal.ofReal (L + 2) * d ^ (-6 * η) := by
          simpa [L, d] using
            (multiplicity_le_log_form s V hη hδ_pos hδ1 hs hlam hb hc hΔ)
    _ = 2695 * ENNReal.ofReal (L + 2) * (d ^ (2 * η) * d ^ (-8 * η)) := by
          rw [← hsplit]
    _ = 2695 * ENNReal.ofReal (L + 2) * ENNReal.ofReal ((δ : ℝ) ^ (2 * η)) * d ^ (-8 * η) := by
          rw [hpow2]
          ring
    _ = 2695 * ENNReal.ofReal ((L + 2) * (δ : ℝ) ^ (2 * η)) * d ^ (-8 * η) := by
          rw [hstep]
    _ ≤ 2695 * ENNReal.ofReal (2 + 1 / (2 * η * Real.log 2)) * d ^ (-8 * η) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hreal)
              (by positivity : (0 : ENNReal) ≤ 2695))
            (by positivity : (0 : ENNReal) ≤ d ^ (-8 * η))
    _ = (multiplicity_le_rpow.C η : ENNReal) * d ^ (-8 * η) := by
          rw [← hC_def]
    _ = (multiplicity_le_rpow.C η : ENNReal) * (δ : ENNReal) ^ (-8 * η) := by
          simp [d]

end ShadedPrism3D

/-! ## Enclosing a convex body in an exact prism

`ShadedPrism3D.multiplicity_le_rpow` is stated for prisms of *exact* half-widths, whereas the
bodies it is applied to are convex bodies whose affine thicknesses are only comparable to a
prescribed triple. This section quantifies the loss incurred when each body is replaced by the
box aligned with its John ellipsoid: the volume grows by at most a constant depending on the
comparison constant alone, and the three ratios `μ`, `λ` and `Δ_max` therefore change by at most
that constant.
-/

open scoped NNReal in
/-- **Constant in `Prism3D.volume_carrier_le_of_hasThicknesses`** (blueprint
`def:prism3DEnclosureVolumeConstant`).

`C_{lem:prism3DEnclosureVolume}(C₀) = 48 C₀⁶`. The two factors of `C₀³` compare the half-widths
of the enclosing box with the affine thicknesses of the body in both directions, and the `48` is
`8 · 3!`: the `8` converts half-widths into the volume of a box in `ℝ³` and the `3! = 6` is the
constant `Metric.lt_volume_convexHull.c 3` of the inscribed-simplex lower bound
`Convex.ethickness_prod_le_volume`. -/
def Prism3D.enclosureVolumeConstant (C₀ : ℝ≥0) : ℝ≥0 := 48 * C₀ ^ 6

open MeasureTheory in
/-- **A convex body of prescribed affine thicknesses has volume at least
`t₀ t₁ t₂ / (6 C₀³)`.**

This is the inscribed-simplex bound `Convex.ethickness_prod_le_volume`, whose constant in
dimension three is `Metric.lt_volume_convexHull.c 3 = 1/3! = 1/6`, combined with the lower half
of `Kakeya.HasThicknesses`. It is the lower half of the comparison recorded in
`Kakeya.VeryNotSticky.thickBodyVol`, stated for an abstract thickness triple. -/
theorem Kakeya.HasThicknesses.le_volume {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    {t₀ t₁ t₂ : ℝ} (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (ht : Kakeya.HasThicknesses (K.carrier) C₀ ![t₀, t₁, t₂]) :
    ENNReal.ofReal (t₀ * t₁ * t₂ / (6 * (C₀ : ℝ) ^ 3))
      ≤ volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  let s := K.carrier
  have hconv : Convex ℝ s := K.convex
  have hbdd : Bornology.IsBounded s := K.isCompact.isBounded
  have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hthick : HasThicknesses s C₀ ![t₀, t₁, t₂] := ht
  let t : Fin 3 → ℝ := ![t₀, t₁, t₂]
  have ht_nonneg : ∀ k : Fin 3, 0 ≤ t k := by
    intro k; fin_cases k <;> simp [t, ht₀, ht₁, ht₂]
  have hC0pos : 0 < (C₀ : ℝ) := by
    have hC0_one : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
    linarith
  have hthick_vals : ∀ k : Fin 3,
      (C₀ : ℝ)⁻¹ * t k ≤ Metric.thickness ℝ s (k : ℕ) ∧
      Metric.thickness ℝ s (k : ℕ) ≤ (C₀ : ℝ) * t k :=
    hthick
  let hi0 : Fin 3 := 0
  let hi1 : Fin 3 := 1
  let hi2 : Fin 3 := 2
  rcases hthick_vals hi0 with ⟨h0_low, h0_up⟩
  rcases hthick_vals hi1 with ⟨h1_low, h1_up⟩
  rcases hthick_vals hi2 with ⟨h2_low, h2_up⟩
  have h0val : (hi0 : ℕ) = 0 := rfl
  have h1val : (hi1 : ℕ) = 1 := rfl
  have h2val : (hi2 : ℕ) = 2 := rfl
  have h0t : t hi0 = t₀ := by simp [t, hi0]
  have h1t : t hi1 = t₁ := by simp [t, hi1]
  have h2t : t hi2 = t₂ := by simp [t, hi2]
  have h_lower : ENNReal.ofReal (t₀ * t₁ * t₂ / (6 * (C₀ : ℝ) ^ 3)) ≤ volume s := by
    have hvol_lower := hconv.ethickness_prod_le_volume
    rw [hfinrank] at hvol_lower
    have hc3_val : (Metric.lt_volume_convexHull.c 3 : ENNReal) = ((6 : NNReal)⁻¹ : ENNReal) := by
      simp [Metric.lt_volume_convexHull.c]; norm_num
    rw [hc3_val] at hvol_lower
    have hprod : ∏ i ∈ Finset.range 3, Metric.ethickness ℝ s i =
        Metric.ethickness ℝ s 0 * Metric.ethickness ℝ s 1 * Metric.ethickness ℝ s 2 := by
      simp [Finset.prod_range_succ]
    rw [hprod] at hvol_lower
    have he0 : Metric.ethickness ℝ s 0 = ENNReal.ofReal (Metric.thickness ℝ s 0) :=
      Metric.ethickness_thickness' hbdd 0
    have he1 : Metric.ethickness ℝ s 1 = ENNReal.ofReal (Metric.thickness ℝ s 1) :=
      Metric.ethickness_thickness' hbdd 1
    have he2 : Metric.ethickness ℝ s 2 = ENNReal.ofReal (Metric.thickness ℝ s 2) :=
      Metric.ethickness_thickness' hbdd 2
    rw [he0, he1, he2] at hvol_lower
    have hlow0 :
        ENNReal.ofReal (((C₀ : ℝ)⁻¹ * t hi0)) ≤
          ENNReal.ofReal (Metric.thickness ℝ s 0) := by
      have htemp : ((C₀ : ℝ)⁻¹ * t hi0) ≤ Metric.thickness ℝ s 0 := by
        simpa [h0val, h0t] using h0_low
      exact ENNReal.ofReal_le_ofReal htemp
    have hlow1 :
        ENNReal.ofReal (((C₀ : ℝ)⁻¹ * t hi1)) ≤
          ENNReal.ofReal (Metric.thickness ℝ s 1) := by
      have htemp : ((C₀ : ℝ)⁻¹ * t hi1) ≤ Metric.thickness ℝ s 1 := by
        simpa [h1val, h1t] using h1_low
      exact ENNReal.ofReal_le_ofReal htemp
    have hlow2 :
        ENNReal.ofReal (((C₀ : ℝ)⁻¹ * t hi2)) ≤
          ENNReal.ofReal (Metric.thickness ℝ s 2) := by
      have htemp : ((C₀ : ℝ)⁻¹ * t hi2) ≤ Metric.thickness ℝ s 2 := by
        simpa [h2val, h2t] using h2_low
      exact ENNReal.ofReal_le_ofReal htemp
    have h_mid : ((6 : NNReal)⁻¹ : ENNReal) *
        (ENNReal.ofReal (((C₀ : ℝ)⁻¹ * t hi0)) * ENNReal.ofReal (((C₀ : ℝ)⁻¹ * t hi1)) *
          ENNReal.ofReal (((C₀ : ℝ)⁻¹ * t hi2))) ≤ volume s := by
      calc
        ((6 : NNReal)⁻¹ : ENNReal) * (ENNReal.ofReal (((C₀ : ℝ)⁻¹ * t hi0)) *
            ENNReal.ofReal (((C₀ : ℝ)⁻¹ * t hi1)) * ENNReal.ofReal (((C₀ : ℝ)⁻¹ * t hi2)))
            ≤ ((6 : NNReal)⁻¹ : ENNReal) * (ENNReal.ofReal (Metric.thickness ℝ s 0) *
                ENNReal.ofReal (Metric.thickness ℝ s 1) *
                  ENNReal.ofReal (Metric.thickness ℝ s 2)) := by
              gcongr
        _ ≤ volume s := hvol_lower
    have h_eq : ENNReal.ofReal (t₀ * t₁ * t₂ / (6 * (C₀ : ℝ) ^ 3)) =
        ((6 : NNReal)⁻¹ : ENNReal) * (ENNReal.ofReal (((C₀ : ℝ)⁻¹ * t hi0)) *
          ENNReal.ofReal (((C₀ : ℝ)⁻¹ * t hi1)) * ENNReal.ofReal (((C₀ : ℝ)⁻¹ * t hi2))) := by
      have hC0_ne : (C₀ : ℝ) ≠ 0 := ne_of_gt hC0pos
      have hC0inv_nonneg : 0 ≤ (C₀ : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hC0pos)
      have hreal : t₀ * t₁ * t₂ / (6 * (C₀ : ℝ) ^ 3) =
          (1 / 6) * ((C₀ : ℝ)⁻¹ * t hi0 *
            ((C₀ : ℝ)⁻¹ * t hi1 * ((C₀ : ℝ)⁻¹ * t hi2))) := by
        simp [t, hi0, hi1, hi2]
        field_simp [hC0_ne]
      have h0nn : 0 ≤ ((C₀ : ℝ)⁻¹ * t hi0) := mul_nonneg hC0inv_nonneg (ht_nonneg hi0)
      have h1nn : 0 ≤ ((C₀ : ℝ)⁻¹ * t hi1) := mul_nonneg hC0inv_nonneg (ht_nonneg hi1)
      have hsix : ENNReal.ofReal (1 / 6 : ℝ) = ((6 : NNReal)⁻¹ : ENNReal) := by
        rw [show (1 / 6 : ℝ) = (6 : ℝ)⁻¹ by norm_num]
        rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 6)]
        simp
      calc
        ENNReal.ofReal (t₀ * t₁ * t₂ / (6 * (C₀ : ℝ) ^ 3))
            = ENNReal.ofReal ((1 / 6) * ((C₀ : ℝ)⁻¹ * t hi0 *
                ((C₀ : ℝ)⁻¹ * t hi1 * ((C₀ : ℝ)⁻¹ * t hi2)))) := by
                rw [hreal]
        _ = ENNReal.ofReal (1 / 6) * ENNReal.ofReal ((C₀ : ℝ)⁻¹ * t hi0 *
              ((C₀ : ℝ)⁻¹ * t hi1 * ((C₀ : ℝ)⁻¹ * t hi2))) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 6)]
        _ = ENNReal.ofReal (1 / 6) * (ENNReal.ofReal ((C₀ : ℝ)⁻¹ * t hi0) *
            ENNReal.ofReal ((C₀ : ℝ)⁻¹ * t hi1 * ((C₀ : ℝ)⁻¹ * t hi2))) := by
            rw [ENNReal.ofReal_mul h0nn]
        _ = ENNReal.ofReal (1 / 6) * (ENNReal.ofReal ((C₀ : ℝ)⁻¹ * t hi0) *
            (ENNReal.ofReal ((C₀ : ℝ)⁻¹ * t hi1) * ENNReal.ofReal ((C₀ : ℝ)⁻¹ * t hi2))) := by
            rw [ENNReal.ofReal_mul h1nn]
        _ = ((6 : NNReal)⁻¹ : ENNReal) * (ENNReal.ofReal ((C₀ : ℝ)⁻¹ * t hi0) *
            (ENNReal.ofReal ((C₀ : ℝ)⁻¹ * t hi1) * ENNReal.ofReal ((C₀ : ℝ)⁻¹ * t hi2))) := by
            rw [hsix]
        _ = ((6 : NNReal)⁻¹ : ENNReal) * (ENNReal.ofReal ((C₀ : ℝ)⁻¹ * t hi0) *
            ENNReal.ofReal ((C₀ : ℝ)⁻¹ * t hi1) * ENNReal.ofReal ((C₀ : ℝ)⁻¹ * t hi2)) := by
            ring
    exact h_eq ▸ h_mid
  simpa [s] using h_lower

namespace Prism3D

open Metric MeasureTheory

variable {A B C C₀ : NNReal} {hAB : A ≤ B} {hBC : B ≤ C}

/-- **The volume of a prism whose half-widths are prescribed multiples of a thickness triple.**
The elementary half of `Prism3D.volume_carrier_le_of_hasThicknesses`: it is
`Prism3D.volume_carrier` with the half-widths substituted. -/
theorem volume_carrier_eq_of_thicknesses (P : Prism3D A B C hAB hBC)
    {t₀ t₁ t₂ : ℝ} (hA : (A : ℝ) = C₀ * t₂) (hB : (B : ℝ) = C₀ * t₁) (hC : (C : ℝ) = C₀ * t₀) :
    volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ENNReal.ofReal (8 * (C₀ : ℝ) ^ 3 * (t₀ * t₁ * t₂)) := by
  rw [Prism3D.volume_carrier]
  have hA_nonneg : 0 ≤ (C₀ : ℝ) * t₂ := by
    rw [← hA]
    positivity
  have hB_nonneg : 0 ≤ (C₀ : ℝ) * t₁ := by
    rw [← hB]
    positivity
  have hA8_nonneg : 0 ≤ (8 : ℝ) * ((C₀ : ℝ) * t₂) :=
    mul_nonneg (by norm_num) hA_nonneg
  have hA81_nonneg : 0 ≤ ((8 : ℝ) * ((C₀ : ℝ) * t₂)) * ((C₀ : ℝ) * t₁) :=
    mul_nonneg hA8_nonneg hB_nonneg
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal]
  rw [show (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) by norm_num]
  rw [hA, hB, hC]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
  rw [← ENNReal.ofReal_mul hA8_nonneg]
  rw [← ENNReal.ofReal_mul hA81_nonneg]
  congr 1
  ring

/-- **A box aligned with a body is comparable to it in volume** (blueprint
`lem:prism3DEnclosureVolume`).

If the affine thicknesses of the convex body `K` are comparable to `(t₀, t₁, t₂)` with constant
`C₀`, and the half-widths of the prism `P` are exactly `C₀ t₂ ≤ C₀ t₁ ≤ C₀ t₀`, then
`|P| ≤ C_{lem:prism3DEnclosureVolume}(C₀) |K|`. No containment between `P` and `K` is assumed:
the statement compares two volumes computed from the same thickness data.

Beware the index conventions: `Kakeya.HasThicknesses K C₀ ![t₀, t₁, t₂]` is antitone in the
index while `Prism3D A B C` is monotone, so `A` is matched against `t₂` and `C` against `t₀`. -/
theorem volume_carrier_le_of_hasThicknesses (hC₀ : 1 ≤ C₀) (P : Prism3D A B C hAB hBC)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    {t₀ t₁ t₂ : ℝ} (ht : Kakeya.HasThicknesses (K.carrier) C₀ ![t₀, t₁, t₂])
    (hA : (A : ℝ) = C₀ * t₂) (hB : (B : ℝ) = C₀ * t₁) (hC : (C : ℝ) = C₀ * t₀) :
    volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ (Prism3D.enclosureVolumeConstant C₀ : ENNReal)
          * volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  have hC₀_pos : 0 < (C₀ : ℝ) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (by exact_mod_cast hC₀)
  have hC₀_ne : (C₀ : ℝ) ≠ 0 := ne_of_gt hC₀_pos
  have ht₀ : 0 ≤ t₀ := by
    have h : 0 ≤ (C₀ : ℝ) * t₀ := by
      rw [← hC]
      exact NNReal.coe_nonneg C
    exact (mul_nonneg_iff_right_nonneg_of_pos hC₀_pos).mp h
  have ht₁ : 0 ≤ t₁ := by
    have h : 0 ≤ (C₀ : ℝ) * t₁ := by
      rw [← hB]
      exact NNReal.coe_nonneg B
    exact (mul_nonneg_iff_right_nonneg_of_pos hC₀_pos).mp h
  have ht₂ : 0 ≤ t₂ := by
    have h : 0 ≤ (C₀ : ℝ) * t₂ := by
      rw [← hA]
      exact NNReal.coe_nonneg A
    exact (mul_nonneg_iff_right_nonneg_of_pos hC₀_pos).mp h
  have hvol : volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ENNReal.ofReal (8 * (C₀ : ℝ) ^ 3 * (t₀ * t₁ * t₂)) :=
    volume_carrier_eq_of_thicknesses P hA hB hC
  have hle : ENNReal.ofReal (t₀ * t₁ * t₂ / (6 * (C₀ : ℝ) ^ 3))
      ≤ volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    Kakeya.HasThicknesses.le_volume hC₀ K ht₀ ht₁ ht₂ ht
  have harith : (8 * (C₀ : ℝ) ^ 3 * (t₀ * t₁ * t₂)) =
      (48 * (C₀ : ℝ) ^ 6) * (t₀ * t₁ * t₂ / (6 * (C₀ : ℝ) ^ 3)) := by
    field_simp [hC₀_ne]
    ring
  have hnonneg : 0 ≤ (48 * (C₀ : ℝ) ^ 6 : ℝ) :=
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 48) (pow_nonneg (NNReal.coe_nonneg C₀) 6)
  calc
    volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = ENNReal.ofReal (8 * (C₀ : ℝ) ^ 3 * (t₀ * t₁ * t₂)) := hvol
    _ = ENNReal.ofReal ((48 * (C₀ : ℝ) ^ 6) * (t₀ * t₁ * t₂ / (6 * (C₀ : ℝ) ^ 3))) := by
        rw [harith]
    _ = ENNReal.ofReal (48 * (C₀ : ℝ) ^ 6) *
          ENNReal.ofReal (t₀ * t₁ * t₂ / (6 * (C₀ : ℝ) ^ 3)) := by
        rw [ENNReal.ofReal_mul hnonneg]
    _ ≤ ENNReal.ofReal (48 * (C₀ : ℝ) ^ 6) *
          volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
        exact mul_le_mul' le_rfl hle
    _ = (Prism3D.enclosureVolumeConstant C₀ : ENNReal) *
          volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
        have hcoef : ENNReal.ofReal (48 * (C₀ : ℝ) ^ 6) =
            (Prism3D.enclosureVolumeConstant C₀ : ENNReal) := by
          unfold Prism3D.enclosureVolumeConstant
          rw [← ENNReal.ofReal_coe_nnreal]
          congr 1
        rw [hcoef]

/-- **The enclosing box of a convex body** (blueprint `lem:prism3DEnclosure`).

The combination of `Prism3D.exists_superset_of_hasThicknesses` and
`Prism3D.volume_carrier_le_of_hasThicknesses`: a convex body whose affine thicknesses are
comparable to `(t₀, t₁, t₂)` with constant `C₀` sits inside a prism of exact half-widths
`C₀ t₂ × C₀ t₁ × C₀ t₀`, whose volume exceeds that of the body by at most
`C_{lem:prism3DEnclosureVolume}(C₀)`. -/
theorem exists_superset_volume_le_of_hasThicknesses (hC₀ : 1 ≤ C₀)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    {t₀ t₁ t₂ : ℝ} (ht : Kakeya.HasThicknesses (K.carrier) C₀ ![t₀, t₁, t₂])
    (hA : (A : ℝ) = C₀ * t₂) (hB : (B : ℝ) = C₀ * t₁) (hC : (C : ℝ) = C₀ * t₀) :
    ∃ P : Prism3D A B C hAB hBC,
      (K.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ P.carrier ∧
        volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ≤ (Prism3D.enclosureVolumeConstant C₀ : ENNReal) * volume (K.carrier : Set _) := by
  have hleA : (C₀ : ℝ) * t₂ ≤ (A : ℝ) := by rw [hA]
  have hleB : (C₀ : ℝ) * t₁ ≤ (B : ℝ) := by rw [hB]
  have hleC : (C₀ : ℝ) * t₀ ≤ (C : ℝ) := by rw [hC]
  obtain ⟨P, hsub⟩ :=
    Prism3D.exists_superset_of_hasThicknesses hC₀ K.isCompact K.nonempty ht hAB hBC
      hleA hleB hleC
  refine ⟨P, hsub, ?_⟩
  exact Prism3D.volume_carrier_le_of_hasThicknesses hC₀ P K ht hA hB hC

end Prism3D

/-! ## Comparing a family with an enclosing family

The three ratios `μ`, `λ` and `Δ_max` of a shaded family under the replacement of every body by
a larger one carrying the same shading. These statements are about `ShadedBody` and
`ConvexSpaceBody` alone; they are collected here because the enclosure lemma
`Kakeya.VeryNotSticky.slabPrismEnclosure` is their only consumer so far.
-/

section Comparison

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

namespace ShadedBody

/-- **Multiplicity depends on the shadings alone.** Neither the bodies nor the values of the
family off `s` enter `ShadedBody.multiplicity`.

**Name note (do not rename back).** This was called `ShadedBody.multiplicity_congr`, which
*collided* with the declaration of that name in `Kakeya/DimensionThree/Plank/SlabTube.lean`. The two statements are
identical as `Expr`s (that is forced: `Lean.Environment.finalizeImport` rejects the import
otherwise), only the proofs differ, so nothing was ever proved from the wrong lemma -- but an edit
to either copy would have been silently invisible. The twin still carries the old name. -/
theorem multiplicity_eq_of_forall_shade_eq (s : Finset ι) (V V' : ι → ShadedBody E)
    (h : ∀ i ∈ s, (V i).shade = (V' i).shade) : multiplicity s V = multiplicity s V' := by
  unfold multiplicity
  have h_sums :
      (∑ i ∈ s, volume (V i).shade) = (∑ i ∈ s, volume (V' i).shade) :=
    Finset.sum_congr rfl fun i hi => by rw [h i hi]
  have h_unions :
      (⋃ i ∈ s, (V i).shade) = (⋃ i ∈ s, (V' i).shade) :=
    Set.iUnion₂_congr fun i hi => by rw [h i hi]
  rw [h_sums, h_unions]

-- **`ShadedBody.fullness_homothety` moved.**  It now lives in `Kakeya/Homothety.lean`, beside
-- `ConvexSpaceBody.IsKatzTao.homothety`, because the Section-6 flat-prism development needs it
-- below this file.  The statement is unchanged; only its home moved, so that there is exactly
-- one copy.

/-- **Enlarging the bodies loses at most the volume-comparison factor in the fullness.**

If `V'` carries the same shadings as `V` and its bodies are larger by at most the factor `c` in
volume, then `λ(V) ≤ c λ(V')`. The inequality is stated in this cleared form, rather than as
`λ(V') ≥ c⁻¹ λ(V)`, so that no positivity or finiteness side condition on the volumes is
needed. -/
theorem fullness_le_of_volume_carrier_le (s : Finset ι) (V V' : ι → ShadedBody E) {c : NNReal}
    (hc : 0 < c) (hshade : ∀ i ∈ s, (V i).shade = (V' i).shade)
    (hvol : ∀ i ∈ s, volume (V' i).carrier ≤ (c : ENNReal) * volume (V i).carrier) :
    fullness s V ≤ c * fullness s V' := by
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ShadedBody.coe_fullness, ShadedBody.coe_fullness]
  change (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier) ≤
    (c : ENNReal) * ((∑ i ∈ s, volume (V' i).shade) / (∑ i ∈ s, volume (V' i).carrier))
  have hshade' : (∑ i ∈ s, volume (V' i).shade) = ∑ i ∈ s, volume (V i).shade := by
    exact Finset.sum_congr rfl (fun i hi => by rw [hshade i hi])
  rw [hshade']
  have hD : (∑ i ∈ s, volume (V' i).carrier) ≤ (c : ENNReal) * ∑ i ∈ s, volume (V i).carrier := by
    calc
      (∑ i ∈ s, volume (V' i).carrier) ≤ ∑ i ∈ s, (c : ENNReal) * volume (V i).carrier :=
        Finset.sum_le_sum hvol
      _ = (c : ENNReal) * ∑ i ∈ s, volume (V i).carrier := by
        rw [Finset.mul_sum]
  have hc0 : (c : ENNReal) ≠ 0 := (ENNReal.coe_ne_zero).mpr hc.ne'
  have hctop : (c : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc
    (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier)
        = ((c : ENNReal) * ∑ i ∈ s, volume (V i).shade) /
            ((c : ENNReal) * ∑ i ∈ s, volume (V i).carrier) := by
          exact (ENNReal.mul_div_mul_left (∑ i ∈ s, volume (V i).shade)
            (∑ i ∈ s, volume (V i).carrier) hc0 hctop).symm
    _ ≤ ((c : ENNReal) * ∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V' i).carrier) := by
          exact ENNReal.div_le_div le_rfl hD
    _ = (c : ENNReal) * ((∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V' i).carrier)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring

end ShadedBody

namespace Kakeya

/-- **Enlarging the bodies raises `Δ_max` by at most the volume-comparison factor.**

If every `W i` is contained in `V i` and `|V i| ≤ c |W i|`, then `Δ_max(V) ≤ c Δ_max(W)`: for a
test body `K`, containment `V i ≤ K` forces `W i ≤ K`, so the sum over the enclosing bodies
contained in `K` is at most `c` times the sum over the enclosed bodies contained in `K`. -/
theorem maxDensity_le_of_carrier_subset (s : Finset ι) (W V : ι → ConvexSpaceBody E) {c : NNReal}
    (hsub : ∀ i ∈ s, W i ≤ V i)
    (hvol : ∀ i ∈ s, volume (V i).carrier ≤ (c : ENNReal) * volume (W i).carrier) :
    maxDensity s V ≤ (c : ENNReal) * maxDensity s W := by
  rw [maxDensity_le_iff]
  intro K
  have hVK : densityIn s V K ≤ (c : ENNReal) * densityIn s W K := by
    rw [densityIn_le_iff s V K]
    calc
      ∑ i ∈ s with V i ≤ K, volume (V i).carrier
          ≤ ∑ i ∈ s with V i ≤ K, (c : ENNReal) * volume (W i).carrier := by
            refine Finset.sum_le_sum fun i hi => ?_
            exact hvol i (Finset.mem_filter.mp hi).1
      _ = (c : ENNReal) * ∑ i ∈ s with V i ≤ K, volume (W i).carrier := by
            rw [Finset.mul_sum]
      _ ≤ (c : ENNReal) * ∑ i ∈ s with W i ≤ K, volume (W i).carrier := by
            have hsubK : (s.filter fun i => V i ≤ K) ⊆ (s.filter fun i => W i ≤ K) := by
              intro i hi
              rw [Finset.mem_filter] at hi ⊢
              exact ⟨hi.1, (hsub i hi.1).trans hi.2⟩
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset hsubK)
              (by positivity : (0 : ENNReal) ≤ (c : ENNReal))
      _ = ((c : ENNReal) * densityIn s W K) * volume K.carrier := by
            rw [sum_volume_eq_densityIn_mul_volume s W K]
            ring
  exact hVK.trans (mul_le_mul_of_nonneg_left (le_maxDensity s W K)
    (by positivity : (0 : ENNReal) ≤ (c : ENNReal)))

end Kakeya

end Comparison

end

end
