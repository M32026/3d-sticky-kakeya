/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.AngleDef
public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.Mathlib.Analysis.EuclideanFrame
public import Kakeya.Mathlib.Analysis.InnerProductSpace
public import Kakeya.Mathlib.Analysis.ProjectiveNormal
public import Kakeya.Mathlib.Analysis.Trigonometric

/-!
# Slab-box geometry: basics, pose, and equal-scale thickening

The slab-box layer of GWZ Lemma 6.13, in three sections.

1. **Basics.**  Thickened-representative fibre pigeonholing, projective-normal geometry, normal
   confinement, and the first slab-assignment helpers.  These declarations are elaborated under a
   raised heartbeat budget, which is `section`-scoped so that it does not leak into the two
   sections below.
2. **Pose.**  Reference-coordinate comparison and fixed-scale slab geometry.  These lemmas encode
   both frame and centre displacement, which is necessary for honest overlap bounds for translated
   slabs.
3. **Equal-scale thickening.**  Anisotropic intersection estimates and scale-aware two-sided
   dilation comparability for equal-scale thickened planks.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}

section SlabBoxBasic

/-! ## Slab-box basics

Thickened-representative fibre pigeonholing, projective-normal geometry, normal confinement,
and the first slab-assignment helpers used by the Lemma 6.13 reduction.
-/

/-! ### Thickened representatives and fibres -/

open Classical in
/-- **Thickened representative fibre** (`def:thickenedRepresentativeFibreAPI`): the fibre over an
active representative prism `Q`, i.e. the planks `i ∈ s` mapped to `Q` by `repr`. This is
`s.filter (fun i => R.repr i = Q)`. -/
def ThickenedRepr.fibre {s : Finset ι} {V : ι → Plank a b hab hb1} {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    {cThk : ℝ≥0} (R : ThickenedRepr s V θ hθ1 cThk) (Q : ThickenedPlank θ b hθ1 hb1) :
    Finset ι :=
  s.filter (fun i => R.repr i = Q)

open Classical in
/-- Every representative fibre is a subfinset of the original family. This elementary bound is
sufficient for dyadic pigeonholing because `plankReduction` already assumes a polynomial bound on
the family cardinality. -/
theorem ThickenedRepr.phi_le_card
    {s : Finset ι} {V : ι → Plank a b hab hb1} {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    {cThk : ℝ≥0} (R : ThickenedRepr s V θ hθ1 cThk) (i : ι) :
    R.phi i ≤ s.card := by
  classical
  simpa [ThickenedRepr.phi] using Finset.card_filter_le s (fun j => R.repr j = R.repr i)

open Classical in
/-- Pigeonhole a common thickened multiplicity using only the family-cardinality bound on each
fibre. It produces a refinement and an integer `N ≥ 1` such that every active fibre has cardinality
comparable to `N`, with a strictly positive retained-mass constant `0 < cGood` (the concrete dyadic
value `((Nat.log 2 s.card : ℝ≥0) + 1)⁻¹ > 0`, needed downstream to keep the final refinement
constant positive). It reuses the quantitative lower bound of `pigeonholeThickenedMultiplicity`
rather than re-running the heavy-level argument. -/
theorem ThickenedRepr.pigeonholeThickenedMultiplicity_of_card
    {s : Finset ι} {V : ι → Plank a b hab hb1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk : ℝ≥0}
    (R : ThickenedRepr s V θ hθ1 cThk)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    ∃ (s₂ : Finset ι) (N : ℕ) (cGood cN : ℝ≥0),
      s₂ ⊆ s ∧ 1 ≤ N ∧ 1 ≤ cN ∧ cN ≤ 2 ∧ 0 < cGood ∧
      ShadedBody.IsCRefinement s₂ Y s Y cGood ∧
      (∀ Q ∈ R.indexSet, (s₂.filter (fun i => R.repr i = Q)).Nonempty →
        (N : ℝ) / (cN : ℝ) ≤ ((s₂.filter (fun i => R.repr i = Q)).card : ℝ) ∧
          ((s₂.filter (fun i => R.repr i = Q)).card : ℝ) ≤ (cN : ℝ) * (N : ℝ)) := by
  obtain ⟨s₂, N, cGood, cN, hsub, hN, hcN, hcN2, hcGood_lb, href, hfibre⟩ :=
    R.pigeonholeThickenedMultiplicity Y s.card fun i _ ↦ R.phi_le_card i
  have hpos : 0 < cGood := lt_of_lt_of_le (by positivity) hcGood_lb
  exact ⟨s₂, N, cGood, cN, hsub, hN, hcN, hcN2, hpos, href, hfibre⟩

/-! ### Slab mass decomposition -/

/-! #### Normal confinement for the slab-mass overlap bound

Prism-level consequences of the projective (sign-blind) distance on unit normals, whose generic
API — `projNormalDist`, `orientedNormal`, and their basic lemmas — lives in
`Kakeya.Mathlib.Analysis.ProjectiveNormal`.  Here the projective chord is compared with the
(projective) plane angle, which is what `usedSlab_normals_confined_cap` needs. -/

/-- The plane angle of two planks is at most `2` times their effective plank angle (using
`π/2 < 2`): when the effective angle is not capped it dominates the raw angle, and when it is
capped at `1` the raw angle `≤ π/2 < 2 = 2·1`. -/
theorem angle_le_two_mul_effectivePlankAngle {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P Q : Plank a b hab hb1) :
    Prism3D.angle P Q ≤ 2 * (Kakeya.effectivePlankAngle P Q : ℝ) := by
  set φ : ℝ := Prism3D.angle P Q with hφdef
  have hφ0 : 0 ≤ φ := Prism3D.angle_nonneg P Q
  have hφ2 : φ ≤ 2 := by
    have h1 : φ ≤ Real.pi / 2 := Prism3D.angle_le_pi_div_two P Q
    have h2 : Real.pi ≤ 4 := Real.pi_le_four
    linarith
  have hpaeq : ((P.planeAngleNN Q : ℝ≥0) : ℝ) = φ := by
    rw [Prism3D.planeAngleNN]
    rw [Real.coe_toNNReal _ (by exact Prism3D.planeAngle_nonneg P Q)]
    rfl
  have hecoe : (Kakeya.effectivePlankAngle P Q : ℝ) = min 1 (max ((a / b : ℝ≥0) : ℝ) φ) := by
    rw [Kakeya.effectivePlankAngle, NNReal.coe_min, NNReal.coe_max, NNReal.coe_one, hpaeq]
  rw [hecoe]
  rcases le_total (max ((a / b : ℝ≥0) : ℝ) φ) 1 with hcase | hcase
  · rw [min_eq_right hcase]
    nlinarith [le_max_left ((a / b : ℝ≥0) : ℝ) φ, le_max_right ((a / b : ℝ≥0) : ℝ) φ, hφ0]
  · rw [min_eq_left hcase]; linarith

/-- **Two planks of one shade fibre are within `2·C·θ` in the plane angle.**  This is the standard
chain behind every pointwise angular-confinement bound: `Kakeya.angularClustering` puts the two
planks within `C·θ` in the *effective* angle, and `angle_le_two_mul_effectivePlankAngle` converts
that to the plane angle at the absolute cost `2`. -/
theorem angle_le_two_mul_of_mem_shadeFibre {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
    {C θ : ℝ≥0} {s : Finset ι} {V : ι → Plank a b hab hb1}
    {Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {x : EuclideanSpace ℝ (Fin 3)}
    (hmax : Kakeya.HasMaxPlankAngleBound s Y V θ C) (hxU : x ∈ ⋃ i ∈ s, (Y i).shade)
    {i j : ι} (hi : i ∈ Kakeya.shadeFibre s Y x) (hj : j ∈ Kakeya.shadeFibre s Y x) :
    Prism3D.angle (V i) (V j) ≤ 2 * (C : ℝ) * (θ : ℝ) := by
  have hcluster : Kakeya.effectivePlankAngle (V i) (V j) ≤ C * θ :=
    Kakeya.angularClustering (hmax x hxU) hi hj
  have h' : (Kakeya.effectivePlankAngle (V i) (V j) : ℝ) ≤ ((C * θ : ℝ≥0) : ℝ) := by
    exact_mod_cast hcluster
  have h'' := angle_le_two_mul_effectivePlankAngle (V i) (V j)
  push_cast at h'
  linarith

/-- **Two slabs seen at a common point have nearby normals.**  If the planks `V i₀`, `V i` both
shade `x` — so the typical-angle bound `htyp` and `angularClustering` control the angle between
them — and each is `Cang·θ`-aligned with its slab `S₀`, `S`, then the short normals of `S` and
`S₀` are within `(2·Cang + 2·C)·θ` in the projective chord metric. -/
private lemma projNormalDist_slab_basis0_le_of_shade -- (extracted by Fuse golfer)
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*} {C Cang θ : ℝ≥0} {hθ1 : θ ≤ 1}
    {s : Finset ι} {V : ι → Plank a b hab hb1} {Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {x : EuclideanSpace ℝ (Fin 3)} (S₀ S : Slab θ hθ1)
    (htyp : Kakeya.HasMaxPlankAngleBound s Y V θ C)
    {i₀ i : ι} (hi₀ : i₀ ∈ s) (hxi₀ : x ∈ (Y i₀).shade) (hi : i ∈ s) (hxi : x ∈ (Y i).shade)
    (hang₀ : Prism3D.angle (V i₀) S₀ ≤ (Cang : ℝ) * (θ : ℝ))
    (hang : Prism3D.angle (V i) S ≤ (Cang : ℝ) * (θ : ℝ)) :
    projNormalDist (S.basis 0) (S₀.basis 0) ≤ ((2 * Cang + 2 * C : ℝ≥0) : ℝ) * (θ : ℝ) := by
  have hmid : Prism3D.angle (V i) (V i₀) ≤ 2 * (C : ℝ) * (θ : ℝ) :=
    angle_le_two_mul_of_mem_shadeFibre htyp (Set.mem_iUnion₂.mpr ⟨i₀, hi₀, hxi₀⟩)
      ((Kakeya.mem_shadeFibre s Y x i).mpr ⟨hi, hxi⟩)
      ((Kakeya.mem_shadeFibre s Y x i₀).mpr ⟨hi₀, hxi₀⟩)
  have h1 : projNormalDist (S.basis 0) ((V i).basis 0) ≤ (Cang : ℝ) * (θ : ℝ) :=
    (Prism3D.projNormalDist_basis0_le_angle S (V i)).trans (by rw [Prism3D.angle_comm]; exact hang)
  have h2 : projNormalDist ((V i).basis 0) ((V i₀).basis 0) ≤ 2 * (C : ℝ) * (θ : ℝ) :=
    (Prism3D.projNormalDist_basis0_le_angle (V i) (V i₀)).trans hmid
  have h3 : projNormalDist ((V i₀).basis 0) (S₀.basis 0) ≤ (Cang : ℝ) * (θ : ℝ) :=
    (Prism3D.projNormalDist_basis0_le_angle (V i₀) S₀).trans hang₀
  have t1 := projNormalDist_triangle (S.basis 0) ((V i).basis 0) (S₀.basis 0)
  have t2 := projNormalDist_triangle ((V i).basis 0) ((V i₀).basis 0) (S₀.basis 0)
  push_cast
  linarith

open Classical in
/-- **Used-slab normals at a point are confined to a fixed cap** (`lem:slabMassNormalsConfined`).
Fix a typical plank angle `θ > 0`, a `SlabAssignment` `SA`, and a point `x`.  Let the *pointwise
overlap family* at `x` be the used slabs `S` such that `x` lies in the shading union of the planks
assigned to `S`:
`x ∈ ⋃ i ∈ s.filter (SA.slabOf (repr i) = S), (Y i).shade`.  Each such `S` has a witnessing plank
`i` through `x` with `Prism3D.angle (V i) S ≤ θ`, and any two witnesses lie in one `O(θ)` angular
cap (typical angle + `angularClustering`).  Hence, for the reference slab `S₀` and its oriented
normal `r = S₀.basis 0`, the rescaled oriented offsets `θ⁻¹ • (orientedNormal r (S.basis 0) - r)`
lie in a fixed ball `closedBall 0 C₀` with `C₀ = 2 * Cang + 2C` (`C` the typical-angle constant,
`Cang` the controlled slab-family angle constant), quantified before the configuration. -/
theorem usedSlab_normals_confined_cap (C Cset Cang : ℝ≥0) (hCang : 1 ≤ Cang) :
    ∃ C₀ : ℝ≥0, 1 ≤ C₀ ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (θ : ℝ≥0) (hθ1 : θ ≤ 1) (repr : ι → ThickenedPlank θ b hθ1 hb1)
        (SA : SlabAssignment s V θ hθ1 repr Cset Cang) (x : EuclideanSpace ℝ (Fin 3))
        (S₀ : Slab θ hθ1),
        0 < θ → Kakeya.HasMaxPlankAngleBound s Y V θ C →
        S₀ ∈ SA.used →
        x ∈ (⋃ i ∈ s.filter (fun i => SA.slabOf (repr i) = S₀), (Y i).shade) →
        ∀ S ∈ SA.used,
          x ∈ (⋃ i ∈ s.filter (fun i => SA.slabOf (repr i) = S), (Y i).shade) →
          ((θ : ℝ)⁻¹ • (orientedNormal (S₀.basis 0) (S.basis 0) - S₀.basis 0))
            ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (C₀ : ℝ) := by
  refine ⟨2 * Cang + 2 * C,
    hCang.trans ((le_mul_of_one_le_left (zero_le : (0 : ℝ≥0) ≤ Cang) one_le_two).trans
      le_self_add), ?_⟩
  intro a b hab hb1 ι s V Y θ hθ1 repr SA x S₀ hθ0 htyp hS₀used hS₀x S hSused hSx
  -- Witnessing planks through `x` for `S` and for `S₀`.
  obtain ⟨iS, hiS, hxiS⟩ := Set.mem_iUnion₂.mp hSx
  obtain ⟨hiSs, hiSslab⟩ := Finset.mem_filter.mp hiS
  obtain ⟨i0, hi0, hxi0⟩ := Set.mem_iUnion₂.mp hS₀x
  obtain ⟨hi0s, hi0slab⟩ := Finset.mem_filter.mp hi0
  have hangS : Prism3D.angle (V iS) S ≤ (Cang : ℝ) * (θ : ℝ) := by
    have h := SA.mem_inSlabFamily iS hiSs
    rw [hiSslab] at h
    exact (Plank.mem_inSlabFamilyC.mp h).2.2
  have hangS0 : Prism3D.angle (V i0) S₀ ≤ (Cang : ℝ) * (θ : ℝ) := by
    have h := SA.mem_inSlabFamily i0 hi0s
    rw [hi0slab] at h
    exact (Plank.mem_inSlabFamilyC.mp h).2.2
  have hchain :=
    projNormalDist_slab_basis0_le_of_shade S₀ S htyp hi0s hxi0 hiSs hxiS hangS0 hangS
  have hθpos : (0 : ℝ) < θ := by exact_mod_cast hθ0
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hθpos),
    orientedNormal_sub_norm_eq_projNormalDist _ _ (S.basis.norm_eq_one 0)
      (S₀.basis.norm_eq_one 0)]
  calc (θ : ℝ)⁻¹ * projNormalDist (S.basis 0) (S₀.basis 0)
      ≤ (θ : ℝ)⁻¹ * (((2 * Cang + 2 * C : ℝ≥0) : ℝ) * (θ : ℝ)) := by gcongr
    _ = ((2 * Cang + 2 * C : ℝ≥0) : ℝ) := by field_simp

/-- **Normal and centre confinement for the `inSlabFamilyC`-indexed family**
(`lem:slabMassCapSeparation`).  If two slabs `S₀`, `S` each contain a plank from the *controlled*
slab subfamily `inSlabFamilyC Cset Cang s V ·` whose shade contains the point `x`, then:
1. their short normals lie within a `(2·Cang + 2·C)·θ` projective cap; and
2. their centres lie within `2·Cset` of `x`. -/
lemma inSlabFamilyC_normal_and_center_confined
    (C Cset Cang : ℝ≥0) (_hCang : 1 ≤ Cang) :
    ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
      (s : Finset ι) (V : ι → Plank a b hab hb1)
      (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      {θ : ℝ≥0} (hθ1 : θ ≤ 1) (repr : ι → ThickenedPlank θ b hθ1 hb1)
      (_SA : SlabAssignment s V θ hθ1 repr Cset Cang) (x : EuclideanSpace ℝ (Fin 3))
      (S₀ S : Slab θ hθ1),
      0 < θ → Kakeya.HasMaxPlankAngleBound s Y V θ C →
      (∀ i ∈ s, (Y i).shade ⊆ (V i).carrier) →
      (∃ i ∈ inSlabFamilyC Cset Cang s V S₀, x ∈ (Y i).shade) →
      (∃ i ∈ inSlabFamilyC Cset Cang s V S, x ∈ (Y i).shade) →
      projNormalDist (S.basis 0) (S₀.basis 0) ≤ ((2 * Cang + 2 * C : ℝ≥0) : ℝ) * (θ : ℝ) ∧
        ‖S.center -ᵥ x‖ ≤ 2 * (Cset : ℝ) ∧
        |inner ℝ (S.basis 0) (x -ᵥ S.center)| ≤ (Cset : ℝ) * (θ : ℝ) := by
  intro a b hab hb1 ι s V Y θ hθ1 repr SA x S₀ S hθ0 htyp hshade_sub hi0 hiS
  rcases hi0 with ⟨i0, hi0_mem, hxi0⟩
  rcases hiS with ⟨iS, hiS_mem, hxiS⟩
  obtain ⟨hi0_s, -, hi0_angle⟩ := Plank.mem_inSlabFamilyC.mp hi0_mem
  obtain ⟨hiS_s, hiS_carrier, hiS_angle⟩ := Plank.mem_inSlabFamilyC.mp hiS_mem
  -- Part 2: `x` lies in the `Cset`-dilation of `S`, bounding its coordinates in `S`'s frame.
  have hxS : x ∈ (S.dilation Cset).carrier := hiS_carrier (hshade_sub iS hiS_s hxiS)
  have h_thick_eq : S.thicknesses = ![θ, 1, 1] := Prism3D.thicknesses_eq S
  have h_inner_bound (i : Fin 3) :
      |inner ℝ (S.basis i) (x -ᵥ S.center)| ≤ (Cset : ℝ) * ((S.thicknesses i : ℝ≥0) : ℝ) := by
    have h_i := ((S.dilation Cset).mem_carrier_iff x).mp hxS i
    simp only [PrismNDim.dilation_basis, PrismNDim.dilation_center, vsub_eq_sub,
      map_sub, PiLp.sub_apply, OrthonormalBasis.repr_apply_apply, PrismNDim.dilation_thicknesses,
      NNReal.coe_mul] at h_i
    rw [vsub_eq_sub, inner_sub_right]
    exact h_i
  have hCset : (0 : ℝ) ≤ Cset := Cset.coe_nonneg
  have h_thin_bound : |inner ℝ (S.basis 0) (x -ᵥ S.center)| ≤ (Cset : ℝ) * (θ : ℝ) := by
    simpa [h_thick_eq] using h_inner_bound 0
  have hb0 : |inner ℝ (S.basis 0) (x -ᵥ S.center)| ≤ (Cset : ℝ) := by
    have hθ1' : (θ : ℝ) ≤ 1 := mod_cast hθ1
    nlinarith [θ.coe_nonneg]
  have hb1' : |inner ℝ (S.basis 1) (x -ᵥ S.center)| ≤ (Cset : ℝ) := by
    simpa [h_thick_eq] using h_inner_bound 1
  have hb2 : |inner ℝ (S.basis 2) (x -ᵥ S.center)| ≤ (Cset : ℝ) := by
    simpa [h_thick_eq] using h_inner_bound 2
  have h_norm_sq : ‖x -ᵥ S.center‖ ^ 2 ≤ (2 * (Cset : ℝ)) ^ 2 := by
    rw [← S.basis.sum_sq_inner_right (x -ᵥ S.center), Fin.sum_univ_three]
    have s0 := sq_le_sq' (abs_le.mp hb0).1 (abs_le.mp hb0).2
    have s1 := sq_le_sq' (abs_le.mp hb1').1 (abs_le.mp hb1').2
    have s2 := sq_le_sq' (abs_le.mp hb2).1 (abs_le.mp hb2).2
    nlinarith [sq_nonneg (Cset : ℝ)]
  refine ⟨projNormalDist_slab_basis0_le_of_shade S₀ S htyp hi0_s hxi0 hiS_s hxiS hi0_angle
    hiS_angle, ?_, h_thin_bound⟩
  rw [← neg_vsub_eq_vsub_rev x S.center, norm_neg]
  nlinarith [norm_nonneg (x -ᵥ S.center)]


/-- **Confinement in an aligned dilated thickening bounds the plank angle.** If plank `P`'s carrier
lies in the `c`-dilation of the thickening `P'_θ` (a prism with `P'`'s centre and axes and
thicknesses `c·(θb, b, 1)`), then the plane angle between `P` and `P'` is at most `3cθ`.

Proof idea: the points `P.center ± b·(P.basis 1)` and `P.center ± (P.basis 2)` lie in `P`, hence in
the confining prism, so their `P'.basis 0`-coordinates are bounded by the thin half-width `c·θb`;
dividing gives `|⟪P.basis 1, P'.basis 0⟫| ≤ cθ` and `|⟪P.basis 2, P'.basis 0⟫| ≤ cθb ≤ cθ`. By
Parseval in `P`'s frame the remaining coordinate satisfies `⟪P.basis 0, P'.basis 0⟫² ≥ 1 - 2(cθ)²`,
so `sin(angle) ≤ √2·cθ` and, using `x ≤ (π/2) sin x` on `[0, π/2]`, `angle ≤ 3cθ`.

`0 < b` is necessary: for `b = 0` a plank degenerates to a segment and the confinement constrains
only its long axis, leaving the frame angle about `basis 0` unconstrained. -/
theorem angle_le_of_carrier_subset_thickened_dilation {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P P' : Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1) (c : ℝ≥0) (hb0 : 0 < b)
    (hsub : ((P.carrier : Set (EuclideanSpace ℝ (Fin 3)))) ⊆
      ((P'.thickened θ hθ1).toPrismNDim.dilation c).carrier) :
    Prism3D.angle P P' ≤ 3 * (c : ℝ) * (θ : ℝ) := by
  have hb_pos : (0 : ℝ) < b := mod_cast hb0
  have hb_le : (b : ℝ) ≤ 1 := mod_cast hb1
  have hcθ : 0 ≤ (c : ℝ) * (θ : ℝ) := by positivity
  -- Step 1: the probe points `P.center ± t • P.basis j` lie in `P.carrier`.
  have h_mem_basis (j : Fin 3) (t : ℝ) (ht : |t| ≤ (P.thicknesses j : ℝ)) :
      P.center + t • (P.basis j) ∈ P.carrier := by
    rw [P.mem_carrier_iff]
    intro i
    rw [P.basis.repr_apply_apply, vsub_eq_sub, add_sub_cancel_left, inner_smul_right]
    by_cases h_eq : i = j
    · subst h_eq
      rw [real_inner_self_eq_norm_sq, P.basis.norm_eq_one i]
      simpa using ht
    · rw [P.basis.inner_eq_zero h_eq, mul_zero, abs_zero]
      exact NNReal.coe_nonneg _
  have h_mem_basis_minus (j : Fin 3) (t : ℝ) (ht : |t| ≤ (P.thicknesses j : ℝ)) :
      P.center - t • (P.basis j) ∈ P.carrier := by
    simpa [sub_eq_add_neg] using h_mem_basis j (-t) (by simpa [abs_neg] using ht)
  have h_thick_eq : P.thicknesses = ![a, b, 1] := Prism3D.thicknesses_eq P
  have h_thick1 : (P.thicknesses 1 : ℝ) = (b : ℝ) := by simp [h_thick_eq]
  have h_thick2 : (P.thicknesses 2 : ℝ) = (1 : ℝ) := by simp [h_thick_eq]
  have hmem1 := h_mem_basis 1 (b : ℝ) (by rw [abs_of_nonneg hb_pos.le, h_thick1])
  have hmem1' := h_mem_basis_minus 1 (b : ℝ) (by rw [abs_of_nonneg hb_pos.le, h_thick1])
  have hmem2 := h_mem_basis 2 (1 : ℝ) (by rw [abs_one, h_thick2])
  have hmem2' := h_mem_basis_minus 2 (1 : ℝ) (by rw [abs_one, h_thick2])
  -- Step 2: `hsub` bounds the `P'.basis 0`-coordinate of every point of `P` by `cθb`.
  set Q := (P'.thickened θ hθ1).toPrismNDim.dilation c with hQ_def
  have hth0 : (((P'.thickened θ hθ1).thicknesses 0 : ℝ≥0) : ℝ) = (θ : ℝ) * (b : ℝ) := by
    simp [Plank.thickened, PrismNDim.thicknesses_mk']
  have hQmem (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ P.carrier) :
      |inner ℝ (P'.basis 0) (y -ᵥ P'.center)| ≤ (c : ℝ) * (θ : ℝ) * (b : ℝ) := by
    have h0 := (Q.mem_carrier_iff y).mp (hsub hy) 0
    simp only [Fin.isValue, hQ_def, PrismNDim.dilation_basis, Plank.thickened_basis,
      PrismNDim.dilation_center, Plank.thickened_center, vsub_eq_sub, map_sub, PiLp.sub_apply,
      OrthonormalBasis.repr_apply_apply, PrismNDim.dilation_thicknesses, NNReal.coe_mul] at h0
    rw [hth0] at h0
    simpa [vsub_eq_sub, inner_sub_right, mul_assoc] using h0
  -- Step 3: the probe-difference trick on each of the two transverse axes.
  have h_inner1 : |inner ℝ (P.basis 1) (P'.basis 0)| ≤ (c : ℝ) * (θ : ℝ) := by
    rw [real_inner_comm]
    calc |inner ℝ (P'.basis 0) (P.basis 1)| ≤ (c : ℝ) * (θ : ℝ) * (b : ℝ) / (b : ℝ) :=
          abs_inner_le_of_probes hb_pos (hQmem _ hmem1) (hQmem _ hmem1')
      _ = (c : ℝ) * (θ : ℝ) := by field_simp
  have h_inner2 : |inner ℝ (P.basis 2) (P'.basis 0)| ≤ (c : ℝ) * (θ : ℝ) := by
    rw [real_inner_comm]
    have h : |inner ℝ (P'.basis 0) (P.basis 2)| ≤ (c : ℝ) * (θ : ℝ) * (b : ℝ) / 1 :=
      abs_inner_le_of_probes one_pos (hQmem _ hmem2) (hQmem _ hmem2')
    rw [div_one] at h
    nlinarith
  -- Step 4: Parseval in `P`'s frame pins the remaining coordinate, then compare arc and chord.
  have hpar : ∑ j : Fin 3, (inner ℝ (P.basis j) (P'.basis 0)) ^ 2 = 1 := by
    rw [P.basis.sum_sq_inner_right, P'.basis.norm_eq_one 0, one_pow]
  rw [Fin.sum_univ_three] at hpar
  rw [Prism3D.angle_def, mul_assoc]
  refine arccos_abs_le_three_mul hcθ ?_ ?_
  · have h := abs_real_inner_le_norm (P.basis 0) (P'.basis 0)
    rwa [P.basis.norm_eq_one 0, P'.basis.norm_eq_one 0, mul_one] at h
  · linarith [sq_le_sq' (abs_le.mp h_inner1).1 (abs_le.mp h_inner1).2,
      sq_le_sq' (abs_le.mp h_inner2).1 (abs_le.mp h_inner2).2]


open Classical in
/-- **Slab assignment with trimmed used set** (`lem:slabMassAssignmentTrimmed`), controlled form.
From the controlled fibre coherence `hcoh`, `SlabAssignment.ofFibreRep` yields a
`SlabAssignment s V θ hθ1 R.repr Cset Cang` whose slab map is `Q ↦ (V (rep Q)).toSlab θ hθ1` and
whose used finset is trimmed to the active representatives; nonempty when `s` is. -/
theorem slabAssignment_ofFibreRep_trimmed {s : Finset ι} {V : ι → Plank a b hab hb1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk Cset Cang : ℝ≥0}
    (R : ThickenedRepr s V θ hθ1 cThk) (rep : ThickenedPlank θ b hθ1 hb1 → ι)
    (hcoh : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V ((V (rep (R.repr i))).toSlab θ hθ1)) :
    ∃ SA : SlabAssignment s V θ hθ1 R.repr Cset Cang,
      (∀ Q, SA.slabOf Q = (V (rep Q)).toSlab θ hθ1) ∧
      SA.used = s.image (fun i => (V (rep (R.repr i))).toSlab θ hθ1) ∧
      (s.Nonempty → SA.used.Nonempty) := by
  refine ⟨Plank.SlabAssignment.ofFibreRep hθ1 rep Cset Cang hcoh, ?_, ?_, ?_⟩
  · intro Q; rfl
  · rfl
  · intro hne
    obtain ⟨i, hi⟩ := hne
    refine ⟨(V (rep (R.repr i))).toSlab θ hθ1, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

end SlabBoxBasic

/-! ## Translation-aware slab pose geometry

Reference-coordinate comparison and fixed-scale slab geometry. These lemmas encode both frame
and centre displacement, which is necessary for honest overlap bounds for translated slabs.
-/

/-! ### Slab-mass pointwise overlap (``lem:slabMass*`` continued)

The ``pointwise overlap family`` of used slabs at a point ``x`` is taken (as in
``usedSlab_normals_confined_cap``) to be the used slabs ``S`` whose *assigned shading union*
``⋃ i ∈ s.filter (slabOf (repr i) = S), (Y i).shade`` contains ``x``. The bounded-overlap
pointwise bound used by ``slabMassDecomposition`` comes from a higher-dimensional pose
argument (not from normal separation alone, which is false because parallel translated slabs
share a normal). The ``usedSlabShadeFibre`` and ``usedNormalOffset`` definitions below are
kept available for that argument. -/

open Classical in
/-- The **pointwise overlap family** of used slabs at a point `x`: the used slabs whose assigned
shading union contains `x`.  This is the finite set `T_x` of `lem:slabMassCapSeparation`. -/
noncomputable def usedSlabShadeFibre {s : Finset ι} {V : ι → Plank a b hab hb1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {repr : ι → ThickenedPlank θ b hθ1 hb1} {Cset Cang : ℝ≥0}
    (SA : SlabAssignment s V θ hθ1 repr Cset Cang) (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) : Finset (Slab θ hθ1) :=
  SA.used.filter (fun S => x ∈ ⋃ i ∈ s.filter (fun i => SA.slabOf (repr i) = S), (Y i).shade)

/-- The **rescaled oriented normal offset** `Φ(S) = θ⁻¹ (n(S) - n(S₀))` used by
`lem:slabMassNormalsSeparated`, with `n(·) = orientedNormal (S₀.basis 0) (·.basis 0)` the short
normal oriented toward the reference slab `S₀`. -/
noncomputable def usedNormalOffset {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S₀ S : Slab θ hθ1) :
    EuclideanSpace ℝ (Fin 3) :=
  (θ : ℝ)⁻¹ • (orientedNormal (S₀.basis 0) (S.basis 0) - S₀.basis 0)

/-- **Generic cross-frame coordinate bound.**  Bounds `dⱼ` on the `b`-frame coordinates of `w`
bound *every* `b'`-frame coordinate of `w` by `d₀ + d₁ + d₂`, since all cross entries are `≤ 1`. -/
private lemma abs_inner_basis_le_of_frame_bounds -- (extracted by Fuse golfer)
    (b b' : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (w : EuclideanSpace ℝ (Fin 3)) {d₀ d₁ d₂ : ℝ}
    (h₀ : |(inner ℝ (b 0) w : ℝ)| ≤ d₀) (h₁ : |(inner ℝ (b 1) w : ℝ)| ≤ d₁)
    (h₂ : |(inner ℝ (b 2) w : ℝ)| ≤ d₂) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (k : Fin 3) : |(inner ℝ (b' k) w : ℝ)| ≤ d₀ + d₁ + d₂ :=
  (abs_inner_le_of_frame_bounds b (b' k) w h₀ h₁ h₂ (abs_inner_basis_le_one _ _ k 0)
    (abs_inner_basis_le_one _ _ k 1) (abs_inner_basis_le_one _ _ k 2)
    hd₀ hd₁ hd₂).trans (le_of_eq (by ring))

/-- **Thin-direction cross-frame coordinate bound.**  Same as `abs_inner_basis_le_of_frame_bounds`
for `k = 0`, but sharpened: the off-diagonal entries `⟪b' 0, b j⟫` (`j ≠ 0`) are bounded by `e`
rather than by `1`, giving `⟪b' 0, w⟫ ≤ d₀ + (d₁ + d₂) · e`. -/
private lemma abs_inner_basis_zero_le_of_cross_bounds -- (extracted by Fuse golfer)
    (b b' : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (w : EuclideanSpace ℝ (Fin 3)) {d₀ d₁ d₂ e : ℝ}
    (h₀ : |(inner ℝ (b 0) w : ℝ)| ≤ d₀) (h₁ : |(inner ℝ (b 1) w : ℝ)| ≤ d₁)
    (h₂ : |(inner ℝ (b 2) w : ℝ)| ≤ d₂) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (he : ∀ j : Fin 3, j ≠ 0 → |(inner ℝ (b' 0) (b j) : ℝ)| ≤ e) :
    |(inner ℝ (b' 0) w : ℝ)| ≤ d₀ + (d₁ + d₂) * e :=
  (abs_inner_le_of_frame_bounds b (b' 0) w h₀ h₁ h₂ (abs_inner_basis_le_one _ _ 0 0)
    (he 1 (by decide)) (he 2 (by decide)) hd₀ hd₁ hd₂).trans (le_of_eq (by ring))

/-- **Off-diagonal cross-frame entry from reference-frame data.**  For `j ≠ k` the entry
`⟪b j, b' k⟫` equals `⟪b j, b' k - b k⟫`, whose `b₀`-frame coordinates are exactly the frame
differences `⟪b k, b₀ m⟫ - ⟪b' k, b₀ m⟫`; so `abs_inner_le_of_frame_bounds` applies. -/
private lemma abs_inner_basis_le_of_ref_frame_diff -- (extracted by Fuse golfer)
    (b₀ b b' : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) {j k : Fin 3} (hjk : j ≠ k)
    {d₀ d₁ d₂ c₀ c₁ c₂ : ℝ}
    (h₀ : |(inner ℝ (b k) (b₀ 0) : ℝ) - inner ℝ (b' k) (b₀ 0)| ≤ d₀)
    (h₁ : |(inner ℝ (b k) (b₀ 1) : ℝ) - inner ℝ (b' k) (b₀ 1)| ≤ d₁)
    (h₂ : |(inner ℝ (b k) (b₀ 2) : ℝ) - inner ℝ (b' k) (b₀ 2)| ≤ d₂)
    (k₀ : |(inner ℝ (b j) (b₀ 0) : ℝ)| ≤ c₀) (k₁ : |(inner ℝ (b j) (b₀ 1) : ℝ)| ≤ c₁)
    (k₂ : |(inner ℝ (b j) (b₀ 2) : ℝ)| ≤ c₂) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) :
    |(inner ℝ (b j) (b' k) : ℝ)| ≤ d₀ * c₀ + d₁ * c₁ + d₂ * c₂ := by
  have hdiff (m : Fin 3) : |(inner ℝ (b₀ m) (b' k - b k) : ℝ)|
      = |(inner ℝ (b k) (b₀ m) : ℝ) - inner ℝ (b' k) (b₀ m)| := by
    rw [inner_sub_right, real_inner_comm (b₀ m) (b' k), real_inner_comm (b₀ m) (b k), abs_sub_comm]
  rw [show (inner ℝ (b j) (b' k) : ℝ) = inner ℝ (b j) (b' k - b k) by
    rw [inner_sub_right, b.inner_eq_zero hjk, sub_zero]]
  exact abs_inner_le_of_frame_bounds b₀ (b j) (b' k - b k) ((hdiff 0).le.trans h₀)
    ((hdiff 1).le.trans h₁) ((hdiff 2).le.trans h₂) k₀ k₁ k₂ hd₀ hd₁ hd₂

/-- **Frame-and-centre closeness.**  If `v` has `b'`-frame coordinates at most `(7/8)·(θ, 1, 1)`,
the cross-frame entries between `b` and `b'` are at most `θ/64` in the thin direction and `1/64`
off-diagonal in-plane, and the offset `z` has `b`-frame coordinates at most `θ/64` resp. `1/64`,
then `v + z` has `b`-frame coordinates at most `(θ, 1, 1)`. -/
private lemma abs_inner_le_of_frames_close -- (extracted by Fuse golfer)
    (b b' : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (v z : EuclideanSpace ℝ (Fin 3))
    (hv0 : |inner ℝ (b' 0) v| ≤ 7 / 8 * θ) (hv1 : |inner ℝ (b' 1) v| ≤ 7 / 8 * 1)
    (hv2 : |inner ℝ (b' 2) v| ≤ 7 / 8 * 1)
    (hang0 : ∀ k : Fin 3, k ≠ 0 → |inner ℝ (b 0) (b' k)| ≤ θ / 64)
    (hang1 : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (b j) (b' 0)| ≤ θ / 64)
    (hplane : ∀ j k : Fin 3, j ≠ 0 → k ≠ 0 → j ≠ k → |inner ℝ (b j) (b' k)| ≤ 1 / 64)
    (hcen0 : |inner ℝ (b 0) z| ≤ θ / 64)
    (hcen1 : ∀ k : Fin 3, k ≠ 0 → |inner ℝ (b k) z| ≤ 1 / 64) :
    |inner ℝ (b 0) (v + z)| ≤ θ ∧ |inner ℝ (b 1) (v + z)| ≤ 1 ∧
      |inner ℝ (b 2) (v + z)| ≤ 1 := by
  have h78 : (0 : ℝ) ≤ 7 / 8 * θ := mul_nonneg (by norm_num) hθ0.le
  have h78' : (0 : ℝ) ≤ 7 / 8 * 1 := by norm_num
  have hθθ : θ * θ ≤ 1 := mul_le_one₀ hθ1 hθ0.le hθ1
  -- Expand in the `b'` frame, then add the centre offset.
  have hk (k : Fin 3) {c₀ c₁ c₂ t : ℝ} (k₀ : |inner ℝ (b k) (b' 0)| ≤ c₀)
      (k₁ : |inner ℝ (b k) (b' 1)| ≤ c₁) (k₂ : |inner ℝ (b k) (b' 2)| ≤ c₂)
      (hc : |inner ℝ (b k) z| ≤ t) :
      |inner ℝ (b k) (v + z)| ≤ 7 / 8 * θ * c₀ + 7 / 8 * 1 * c₁ + 7 / 8 * 1 * c₂ + t := by
    rw [inner_add_right]
    exact (abs_add_le _ _).trans (add_le_add
      (abs_inner_le_of_frame_bounds b' (b k) v hv0 hv1 hv2 k₀ k₁ k₂ h78 h78' h78') hc)
  have h1 : (1 : Fin 3) ≠ 0 := by decide
  have h2 : (2 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  exact ⟨(hk 0 (abs_inner_basis_le_one b b' 0 0) (hang0 1 h1) (hang0 2 h2) hcen0).trans
      (by linarith only [hθ0]),
    (hk 1 (hang1 1 h1) (abs_inner_basis_le_one b b' 1 1) (hplane 1 2 h1 h2 h12)
      (hcen1 1 h1)).trans (by linarith only [hθθ]),
    (hk 2 (hang1 2 h2) (hplane 2 1 h2 h1 h12.symm) (abs_inner_basis_le_one b b' 2 2)
      (hcen1 2 h2)).trans (by linarith only [hθθ])⟩

/-- Essential distinctness of two `θ × 1 × 1` slabs, unfolded: both have volume `8θ`, so the
threshold `(1/2)·max` is exactly `4θ`. -/
private lemma essentiallyDistinct_slab_iff -- (extracted by Fuse golfer)
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S S' : Slab θ hθ1) :
    PrismNDim.IsEssentiallyDistinct S.toPrismNDim S'.toPrismNDim ↔
      volume ((S.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ S'.carrier) ≤ 4 * (θ : ENNReal) := by
  have h8 : (1 / 2 : ENNReal) * (8 * (θ : ENNReal)) = 4 * (θ : ENNReal) := by
    rw [← mul_assoc, one_div, show (8 : ENNReal) = 2 * 4 by norm_num, ← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  change volume ((S.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ S'.carrier) ≤
      (1 / 2 : ENNReal) * max (volume S.carrier) (volume S'.carrier) ↔ _
  rw [Slab.volume_carrier S, Slab.volume_carrier S', max_self, h8]

/-- If two equal-scale `θ × 1 × 1` slabs have nearly-equal orthonormal frames AND nearly-equal
centres (with the normal-direction quantities measured at scale `θ` and the in-plane quantities
at scale `1`), then they are NOT essentially distinct.  The explicit shrunken sub-prism
`B := S'.dilation (7/8)` lies
inside both, giving a positive-volume lower bound on the intersection that exceeds the
`(1/2)*vol` threshold required for essential distinctness. -/
private theorem not_essentiallyDistinct_of_frame_center_close
    {θ : ℝ≥0} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (S S' : Slab θ hθ1)
    (hang0 : ∀ k : Fin 3, k ≠ 0 → |inner ℝ (S.basis 0) (S'.basis k)| ≤ (θ : ℝ) / 64)
    (hang1 : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (S.basis j) (S'.basis 0)| ≤ (θ : ℝ) / 64)
    (hplane : ∀ j k : Fin 3, j ≠ 0 → k ≠ 0 → j ≠ k →
      |inner ℝ (S.basis j) (S'.basis k)| ≤ 1 / 64)
    (hcen0 : |inner ℝ (S.basis 0) (S'.center -ᵥ S.center)| ≤ (θ : ℝ) / 64)
    (hcen1 : ∀ k : Fin 3, k ≠ 0 →
      |inner ℝ (S.basis k) (S'.center -ᵥ S.center)| ≤ 1 / 64) :
    ¬ PrismNDim.IsEssentiallyDistinct S.toPrismNDim S'.toPrismNDim := by
  have hθpos_real : 0 < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1r : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ1
  have hS_thick : S.thicknesses = ![θ, 1, 1] := Prism3D.thicknesses_eq S
  have hS'_thick : S'.thicknesses = ![θ, 1, 1] := Prism3D.thicknesses_eq S'
  -- STEP 1 — define B := S'.dilation (7/8)
  set B := S'.toPrismNDim.dilation (7/8 : ℝ≥0) with hB_def
  have hBS' : (B.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ S'.carrier := by
    intro y hy
    rw [PrismNDim.mem_carrier_iff] at hy ⊢
    exact fun i => (hy i).trans (by
      rw [hB_def, PrismNDim.dilation_thicknesses]
      push_cast
      linarith only [NNReal.coe_nonneg (S'.thicknesses i)])
  have hBS : (B.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ S.carrier := by
    intro y hy
    rw [PrismNDim.mem_carrier_iff] at hy ⊢
    -- hy : ∀ i : Fin 3, |(S'.basis).repr (y -ᵥ S'.center) i| ≤ B.thicknesses i
    have hw (j : Fin 3) : |inner ℝ (S'.basis j) (y -ᵥ S'.center)|
        ≤ (7/8 : ℝ) * ((![θ, 1, 1] j : ℝ≥0) : ℝ) := by
      have hyj := hy j
      rwa [hB_def, PrismNDim.dilation_thicknesses, OrthonormalBasis.repr_apply_apply,
        hS'_thick] at hyj
    -- Triangle inequality through the centre of `S'`, then the frame expansion in the `S'` frame.
    obtain ⟨hk0, hk1, hk2⟩ := abs_inner_le_of_frames_close S.basis S'.basis hθpos_real hθ1r
      (y -ᵥ S'.center) (S'.center -ᵥ S.center) (hw 0) (hw 1) (hw 2) hang0 hang1 hplane hcen0 hcen1
    -- Combine the three bounds, matching the shape of `mem_carrier_iff`
    intro k
    rw [OrthonormalBasis.repr_apply_apply, hS_thick,
      show (y -ᵥ S.center : EuclideanSpace ℝ (Fin 3))
        = (y -ᵥ S'.center) + (S'.center -ᵥ S.center) from (vsub_add_vsub_cancel _ _ _).symm]
    exact match k with
      | 0 => hk0
      | 1 => hk1
      | 2 => hk2
  -- STEP 3 — volume of B, computed in `ℝ≥0` and coerced
  have hvolB : volume (B.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (((343/64 : ℝ≥0) * θ : ℝ≥0) : ENNReal) := by
    rw [PrismNDim.volume_carrier B, finrank_euclideanSpace_fin, ← ENNReal.ofNNReal_finsetProd,
      show (2 : ENNReal) ^ 3 = ((8 : ℝ≥0) : ENNReal) by norm_num, ← ENNReal.coe_mul]
    congr 1
    simp only [hB_def, PrismNDim.dilation_thicknesses, hS'_thick, Fin.prod_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, mul_one]
    ring
  -- STEP 4 — conclude by contradiction: `B ⊆ S ∩ S'` has volume `(343/64)·θ > 4·θ`
  intro hED
  have h_contra : ((343/64 : ℝ≥0) * θ : ℝ≥0) ≤ ((4 : ℝ≥0) * θ : ℝ≥0) := by
    rw [← ENNReal.coe_le_coe, ← hvolB, ENNReal.coe_mul, ENNReal.coe_ofNat]
    exact (measure_mono (fun x hx => ⟨hBS hx, hBS' hx⟩ :
      (B.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ S.carrier ∩ S'.carrier)).trans
      ((essentiallyDistinct_slab_iff S S').mp hED)
  rw [← NNReal.coe_le_coe] at h_contra
  push_cast at h_contra
  linarith

/-- Transfer the hypotheses of `not_essentiallyDistinct_of_frame_center_close` from PAIRWISE data
(between `S` and `S'`) to REFERENCE-RELATIVE data (each of `S`, `S'` compared to a reference slab
`S₀`).  This is the step that lets a later packing argument work with a single pose map.  It is pure
orthonormal-frame algebra — no measure theory.

Each of the five cases is one application of `abs_inner_le_of_frame_bounds` in the reference frame
`S₀`, using that an off-diagonal entry `⟪eⱼ, e'ₖ⟫` (`j ≠ k`) equals `⟪eⱼ, e'ₖ - eₖ⟫`. -/
lemma not_essentiallyDistinct_of_ref_coords_close
    {θ : ℝ≥0} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (S₀ S S' : Slab θ hθ1)
    {K δ : ℝ} (hK : 1 ≤ K) (hδ : 0 ≤ δ)
    -- CONFINEMENT: the mixed frame entries of both slabs are O(θ)
    (hcS : ∀ j k : Fin 3, (j = 0 ∧ k ≠ 0) ∨ (j ≠ 0 ∧ k = 0) →
      |inner ℝ (S.basis j) (S₀.basis k)| ≤ K * (θ : ℝ))
    (_hcS' : ∀ j k : Fin 3, (j = 0 ∧ k ≠ 0) ∨ (j ≠ 0 ∧ k = 0) →
      |inner ℝ (S'.basis j) (S₀.basis k)| ≤ K * (θ : ℝ))
    -- CLOSENESS of the frame coordinates in S₀'s basis, at the two scales
    (hfrm : ∀ j k : Fin 3, (j = 0 ∧ k ≠ 0) ∨ (j ≠ 0 ∧ k = 0) →
      |inner ℝ (S.basis j) (S₀.basis k) - inner ℝ (S'.basis j) (S₀.basis k)| ≤ (θ : ℝ) * δ)
    (hfrm' : ∀ j k : Fin 3, ¬((j = 0 ∧ k ≠ 0) ∨ (j ≠ 0 ∧ k = 0)) →
      |inner ℝ (S.basis j) (S₀.basis k) - inner ℝ (S'.basis j) (S₀.basis k)| ≤ δ)
    -- CLOSENESS of the centres in S₀'s basis, at the two scales
    (hcen0 : |inner ℝ (S₀.basis 0) (S'.center -ᵥ S.center)| ≤ (θ : ℝ) * δ)
    (hcen1 : ∀ k : Fin 3, k ≠ 0 →
      |inner ℝ (S₀.basis k) (S'.center -ᵥ S.center)| ≤ δ)
    (hsmall : δ ≤ 1 / (1024 * K)) :
    ¬ PrismNDim.IsEssentiallyDistinct S.toPrismNDim S'.toPrismNDim := by
  -- Preliminary numeric facts
  have hθpos_real : 0 < (θ : ℝ) := NNReal.coe_pos.mpr hθ0
  have hθ1r : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ1
  have hK_pos : (0 : ℝ) < K := by linarith only [hK]
  have hθsq : (θ : ℝ) ^ 2 ≤ 1 := pow_le_one₀ hθpos_real.le hθ1r
  have hθδ_nonneg : 0 ≤ (θ : ℝ) * δ := mul_nonneg hθpos_real.le hδ
  have hne1 : (1 : Fin 3) ≠ 0 := by decide
  have hne2 : (2 : Fin 3) ≠ 0 := by decide
  -- The off-diagonal side condition of `hfrm'`, for `k ≠ 0` and `m ≠ 0`.
  have hoff (k m : Fin 3) (hk : k ≠ 0) (hm : m ≠ 0) :
      ¬((k = 0 ∧ m ≠ 0) ∨ (k ≠ 0 ∧ m = 0)) :=
    fun h => h.elim (fun p => hk p.1) (fun p => hm p.2)
  -- The single numeric consequence of `hsmall` that all five cases need.
  have hKδ : 3 * K * δ ≤ 1 / 64 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1024 * K)] at hsmall
    linarith only [hsmall]
  -- Two hint bundles for the final linear arithmetic, one per scale.
  have hyp_θ : 0 ≤ (θ : ℝ) * δ * (K - 1) :=
    mul_nonneg hθδ_nonneg (by linarith only [hK])
  have hyp_θ' : (θ : ℝ) * (3 * K * δ) ≤ (θ : ℝ) * (1 / 64) :=
    mul_le_mul_of_nonneg_left hKδ hθpos_real.le
  -- The five cases, in the order `not_essentiallyDistinct_of_frame_center_close` expects them:
  -- (A) `⟪e₀, e'ₖ⟫ ≤ θ/64` (`k ≠ 0`), (B) `⟪eⱼ, e'₀⟫ ≤ θ/64` (`j ≠ 0`), (C) `⟪eⱼ, e'ₖ⟫ ≤ 1/64`
  -- (`j ≠ k`, both nonzero), (D) `⟪e₀, c' - c⟫ ≤ θ/64`, (E) `⟪eₖ, c' - c⟫ ≤ 1/64` (`k ≠ 0`).
  exact not_essentiallyDistinct_of_frame_center_close hθ0 hθ1 S S'
    (fun k hk => (abs_inner_basis_le_of_ref_frame_diff S₀.basis S.basis S'.basis (Ne.symm hk)
      (hfrm k 0 (Or.inr ⟨hk, rfl⟩)) (hfrm' k 1 (hoff k 1 hk hne1))
      (hfrm' k 2 (hoff k 2 hk hne2)) (abs_inner_basis_le_one _ _ 0 0)
      (hcS 0 1 (Or.inl ⟨rfl, hne1⟩)) (hcS 0 2 (Or.inl ⟨rfl, hne2⟩))
      hθδ_nonneg hδ hδ).trans (by linarith only [hyp_θ, hyp_θ']))
    (fun j hj => (abs_inner_basis_le_of_ref_frame_diff S₀.basis S.basis S'.basis hj
      (hfrm' 0 0 (fun h => h.elim (fun p => p.2 rfl) (fun p => p.1 rfl)))
      (hfrm 0 1 (Or.inl ⟨rfl, hne1⟩)) (hfrm 0 2 (Or.inl ⟨rfl, hne2⟩))
      (hcS j 0 (Or.inr ⟨hj, rfl⟩)) (abs_inner_basis_le_one _ _ j 1)
      (abs_inner_basis_le_one _ _ j 2) hδ hθδ_nonneg
      hθδ_nonneg).trans (by linarith only [hyp_θ, hyp_θ']))
    (fun j k _ hk hjk => (abs_inner_basis_le_of_ref_frame_diff S₀.basis S.basis S'.basis hjk
      (hfrm k 0 (Or.inr ⟨hk, rfl⟩)) (hfrm' k 1 (hoff k 1 hk hne1))
      (hfrm' k 2 (hoff k 2 hk hne2)) (abs_inner_basis_le_one _ _ j 0)
      (abs_inner_basis_le_one _ _ j 1) (abs_inner_basis_le_one _ _ j 2)
      hθδ_nonneg hδ hδ).trans (by
        linarith only [hKδ, mul_nonneg hδ (sub_nonneg.mpr hK),
          mul_nonneg hδ (sub_nonneg.mpr hθ1r)]))
    ((abs_inner_le_of_frame_bounds S₀.basis (S.basis 0) (S'.center -ᵥ S.center)
      hcen0 (hcen1 1 hne1) (hcen1 2 hne2) (abs_inner_basis_le_one _ _ 0 0)
      (hcS 0 1 (Or.inl ⟨rfl, hne1⟩)) (hcS 0 2 (Or.inl ⟨rfl, hne2⟩))
      hθδ_nonneg hδ hδ).trans (by linarith only [hyp_θ, hyp_θ']))
    (fun k hk => (abs_inner_le_of_frame_bounds S₀.basis (S.basis k) (S'.center -ᵥ S.center)
      hcen0 (hcen1 1 hne1) (hcen1 2 hne2) (hcS k 0 (Or.inr ⟨hk, rfl⟩))
      (abs_inner_basis_le_one _ _ k 1) (abs_inner_basis_le_one _ _ k 2)
      hθδ_nonneg hδ hδ).trans (by
        linarith only [hKδ, mul_nonneg hδ (sub_nonneg.mpr hK),
          mul_nonneg (mul_nonneg hK_pos.le hδ) (sub_nonneg.mpr hθsq)]))

/-- **Overlap forces a small slab angle** (`lem:thickenedReprCentreAngleBound`, frame half). Two
`θ × 1 × 1` slabs with `θ > 0` that are *not* essentially distinct make angle `< 8 · θ`: each has
volume `8θ`, so non-distinctness forces `|S ∩ S'| > 4θ`, while `Slab.volume_inter_le` bounds
`|S ∩ S'| ≤ 32 θ² / angle`; combining gives `angle < 8θ`. -/
theorem slab_angle_lt_of_not_essentiallyDistinct {θ : ℝ≥0} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (S S' : Slab θ hθ1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct S.toPrismNDim S'.toPrismNDim) :
    Prism3D.angle S S' < 8 * (θ : ℝ) := by
  have hθpos_real : 0 < (θ : ℝ) := by exact_mod_cast hθ0
  set φ := Prism3D.angle S S' with hφdef
  have hφ_nonneg : 0 ≤ φ := Prism3D.angle_nonneg S S'
  rcases hφ_nonneg.eq_or_lt with hφ0 | hφ_pos
  · -- φ = 0: the goal is `0 < 8 * θ`
    rw [← hφ0]; positivity
  -- Non-distinctness plus `Slab.volume_inter_le` pins the intersection volume from both sides.
  have h_gt : 4 * (θ : ENNReal) <
      volume ((S.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ S'.carrier) :=
    not_le.mp fun h => hnd ((essentiallyDistinct_slab_iff S S').mpr h)
  have h_le : volume ((S.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ S'.carrier) ≤
      32 * (θ : ENNReal) ^ 2 / ENNReal.ofReal φ := by
    simpa [Slab.volume_inter_le.C] using
      Slab.volume_inter_le S S' hφ_pos le_rfl
  -- Transfer to ℝ through `ENNReal.ofReal`.
  have h4 : ENNReal.ofReal (4 * (θ : ℝ)) = 4 * (θ : ENNReal) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_coe_nnreal]; norm_num
  have h32 : ENNReal.ofReal (32 * (θ : ℝ) ^ 2 / φ)
      = 32 * (θ : ENNReal) ^ 2 / ENNReal.ofReal φ := by
    rw [ENNReal.ofReal_div_of_pos hφ_pos, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32),
      ENNReal.ofReal_pow hθpos_real.le, ENNReal.ofReal_coe_nnreal]; norm_num
  have h_real : 4 * (θ : ℝ) < 32 * (θ : ℝ) ^ 2 / φ :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp (by rw [h4, h32]; exact h_gt.trans_le h_le)
  rw [lt_div_iff₀ hφ_pos] at h_real
  nlinarith

/-- **Off-diagonal frame inner product bounded by the plane angle.** For `j ≠ 0`,
`|⟪P.basis j, Q.basis 0⟫| ≤ Prism3D.angle P Q`.  Since `⟪P.basis j, P.basis 0⟫ = 0`,
`|⟪P.basis j, Q.basis 0⟫| = |⟪P.basis j, Q.basis 0 - s • P.basis 0⟫|` for either sign `s = ±1`,
so it is at most `min ‖Q.basis 0 - P.basis 0‖ ‖Q.basis 0 + P.basis 0‖ = projNormalDist` of the
short normals, bounded by the angle (`Prism3D.projNormalDist_basis0_le_angle`). -/
theorem abs_inner_basis_ne_zero_le_angle
    {a₁ b₁ c₁ a₂ b₂ c₂ : ℝ≥0} {h₁ : a₁ ≤ b₁} {h₁' : b₁ ≤ c₁} {h₂ : a₂ ≤ b₂} {h₂' : b₂ ≤ c₂}
    (P : Prism3D a₁ b₁ c₁ h₁ h₁') (Q : Prism3D a₂ b₂ c₂ h₂ h₂') {j : Fin 3} (hj : j ≠ 0) :
    |inner ℝ (P.basis j) (Q.basis 0)| ≤ Prism3D.angle P Q := by
  -- Since `j ≠ 0`, `⟪P.basis j, P.basis 0⟫ = 0`, so subtracting `s • P.basis 0` is free;
  -- Cauchy–Schwarz with `‖P.basis j‖ = 1` then bounds the entry by `‖Q.basis 0 - s • P.basis 0‖`.
  have hcs (s : ℝ) : |(inner ℝ (P.basis j) (Q.basis 0) : ℝ)| ≤ ‖Q.basis 0 - s • P.basis 0‖ := by
    rw [show (inner ℝ (P.basis j) (Q.basis 0) : ℝ)
          = inner ℝ (P.basis j) (Q.basis 0 - s • P.basis 0) by
        rw [inner_sub_right, real_inner_smul_right, P.basis.inner_eq_zero hj, mul_zero, sub_zero]]
    exact (abs_real_inner_le_norm _ _).trans_eq (by rw [P.basis.norm_eq_one j, one_mul])
  have h1 := hcs 1
  have h2 := hcs (-1)
  rw [one_smul] at h1
  rw [neg_smul, one_smul, sub_neg_eq_add] at h2
  -- The minimum of the two norms is `projNormalDist`, bounded by the angle.
  exact (le_min h1 h2).trans
    ((Prism3D.projNormalDist_basis0_le_angle Q P).trans_eq (Prism3D.angle_comm Q P))

/-- **Cross-frame coordinate bound.** If `w` has `S`-frame coordinates bounded by `S.thicknesses`
(`= ![θ,1,1]`) and the slab angle is `< 8θ`, then each `S'`-frame coordinate of `w` is bounded by
`17 · S'.thicknesses k`.  Expand `⟪e'ₖ, w⟫ = ∑ⱼ ⟪eⱼ, w⟫·⟪e'ₖ, eⱼ⟫` (`inner_eq_sum_frame`); for the
thin `k=0` the off-diagonal `⟪eⱼ, e'₀⟫` (`j≠0`) are `≤ 8θ` (`abs_inner_basis_ne_zero_le_angle`), the
rest use unit widths. -/
theorem abs_inner_basis'_le_of_frame_bounds {θ : ℝ≥0} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (S S' : Slab θ hθ1) (hang : Prism3D.angle S S' < 8 * (θ : ℝ))
    (w : EuclideanSpace ℝ (Fin 3))
    (hw : ∀ j : Fin 3, |inner ℝ (S.basis j) w| ≤ ((S.thicknesses j : ℝ≥0) : ℝ)) :
    ∀ k : Fin 3, |inner ℝ (S'.basis k) w| ≤ 17 * ((S'.thicknesses k : ℝ≥0) : ℝ) := by
  have hθ1r : (θ : ℝ) ≤ 1 := NNReal.coe_le_coe.mpr hθ1
  have hθ0r : (0 : ℝ) ≤ (θ : ℝ) := (NNReal.coe_pos.mpr hθ0).le
  -- extract the three hw bounds using the explicit thicknesses
  rw [Prism3D.thicknesses_eq S] at hw
  have hw0 : |inner ℝ (S.basis 0) w| ≤ (θ : ℝ) := hw 0
  have hw1 : |inner ℝ (S.basis 1) w| ≤ (1 : ℝ) := hw 1
  have hw2 : |inner ℝ (S.basis 2) w| ≤ (1 : ℝ) := hw 2
  -- for k = 0, j ≠ 0, better bound via the slab angle: |c_j0| ≤ 8θ
  have hc_j0 (j : Fin 3) (hj : j ≠ 0) : |inner ℝ (S'.basis 0) (S.basis j)| ≤ 8 * (θ : ℝ) := by
    rw [real_inner_comm]
    exact (abs_inner_basis_ne_zero_le_angle S S' hj).trans hang.le
  -- prove the three concrete bounds
  have h0 : |inner ℝ (S'.basis 0) w| ≤ 17 * (θ : ℝ) :=
    (abs_inner_basis_zero_le_of_cross_bounds S.basis S'.basis w hw0 hw1 hw2
      hθ0r zero_le_one zero_le_one hc_j0).trans (le_of_eq (by ring))
  have hk (k : Fin 3) : |inner ℝ (S'.basis k) w| ≤ 17 * (1 : ℝ) :=
    (abs_inner_basis_le_of_frame_bounds S.basis S'.basis w hw0 hw1 hw2
      hθ0r zero_le_one zero_le_one k).trans (by linarith only [hθ1r])
  intro k
  rw [Prism3D.thicknesses_eq S']
  exact match k with
    | 0 => h0
    | 1 => hk 1
    | 2 => hk 2

/-- Membership in a prism carrier, read off as inner-product bounds in the prism frame. -/
private lemma abs_inner_le_of_mem_carrier -- (extracted by Fuse golfer)
    (P : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (i : Fin 3) : |inner ℝ (P.basis i) (x -ᵥ P.center)| ≤ ((P.thicknesses i : ℝ≥0) : ℝ) := by
  have h := (P.mem_carrier_iff x).mp hx i
  rwa [OrthonormalBasis.repr_apply_apply] at h

/-- Membership in a dilated prism carrier, read off as inner-product bounds in the prism frame. -/
private lemma abs_inner_le_of_mem_dilation -- (extracted by Fuse golfer)
    (P : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))) (c : ℝ≥0)
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ((P.dilation c).carrier : Set (EuclideanSpace ℝ (Fin 3)))) (i : Fin 3) :
    |inner ℝ (P.basis i) (x -ᵥ P.center)| ≤ (c : ℝ) * ((P.thicknesses i : ℝ≥0) : ℝ) := by
  have h := ((P.dilation c).mem_carrier_iff x).mp hx i
  rwa [PrismNDim.dilation_center, PrismNDim.dilation_basis, PrismNDim.dilation_thicknesses,
    OrthonormalBasis.repr_apply_apply, NNReal.coe_mul] at h

/-- Rescaling an inner-product bound: testing against `r⁻¹ • v` at scale `c` is the same as testing
against `v` at scale `r * c`. -/
private lemma abs_inner_inv_smul_le_iff -- (extracted by Fuse golfer)
    {r : ℝ} (hr : 0 < r) (e v : EuclideanSpace ℝ (Fin 3)) (c : ℝ) :
    |inner ℝ e (r⁻¹ • v)| ≤ c ↔ |inner ℝ e v| ≤ r * c := by
  rw [real_inner_smul_right, abs_mul, abs_inv, abs_of_nonneg hr.le, inv_mul_le_iff₀ hr]

/-- Inner-product bounds in the prism frame give membership in a dilated prism carrier. -/
private lemma mem_dilation_of_abs_inner_le -- (extracted by Fuse golfer)
    (P : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))) (c : ℝ≥0)
    {x : EuclideanSpace ℝ (Fin 3)}
    (h : ∀ i : Fin 3,
      |inner ℝ (P.basis i) (x -ᵥ P.center)| ≤ (c : ℝ) * ((P.thicknesses i : ℝ≥0) : ℝ)) :
    x ∈ ((P.dilation c).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  rw [(P.dilation c).mem_carrier_iff]
  intro i
  rw [PrismNDim.dilation_center, PrismNDim.dilation_basis, PrismNDim.dilation_thicknesses,
    OrthonormalBasis.repr_apply_apply, NNReal.coe_mul]
  exact h i

/-- **Scale-aware slab containment.** The `∀ r ≥ 1` form of `slab_subset_dilation_of_angle_lt`.
Scale-awareness is not a convenience: for non-concentric prisms `A ⊆ B` never implies
`A.dilation c ⊆ B.dilation c`, so a fixed-scale containment cannot be chained through the later
dilations that the slab assignment needs. The frame mismatch contributes `O(r)` half-widths while
the centre offset (measured at the shared point `p`) contributes only `O(1)`. -/
theorem slab_dilation_subset_of_angle_lt {θ : ℝ≥0} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (S S' : Slab θ hθ1) (hang : Prism3D.angle S S' < 8 * (θ : ℝ))
    {p : EuclideanSpace ℝ (Fin 3)}
    (hpS : p ∈ (S.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hpS' : p ∈ (S'.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    {r : ℝ≥0} (hr : 1 ≤ r) :
    ((S.toPrismNDim.dilation r).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (S'.toPrismNDim.dilation (64 * r)).carrier := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le one_pos hr1
  -- The frame coordinates of `p` relative to both centres.
  have hp_frame := abs_inner_basis'_le_of_frame_bounds hθ0 hθ1 S S' hang (p -ᵥ S.center)
    (abs_inner_le_of_mem_carrier S.toPrismNDim hpS)
  have hpw' := abs_inner_le_of_mem_carrier S'.toPrismNDim hpS'
  intro x hxS
  refine mem_dilation_of_abs_inner_le S'.toPrismNDim _ fun k => ?_
  -- Rescaling trick: apply `abs_inner_basis'_le_of_frame_bounds` to `r⁻¹ • (x -ᵥ S.center)`.
  have hx_frame := (abs_inner_inv_smul_le_iff hrpos _ _ _).1
    (abs_inner_basis'_le_of_frame_bounds hθ0 hθ1 S S' hang ((r : ℝ)⁻¹ • (x -ᵥ S.center))
      (fun j => (abs_inner_inv_smul_le_iff hrpos _ _ _).2
        (abs_inner_le_of_mem_dilation S.toPrismNDim r hxS j)) k)
  -- Triangle inequality through `p`, in the `S'`-frame coordinate `k`.
  have ht : (0 : ℝ) ≤ ((S'.thicknesses k : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  rw [show x -ᵥ S'.center = (x -ᵥ S.center) - (p -ᵥ S.center) + (p -ᵥ S'.center) by
      rw [vsub_sub_vsub_cancel_right, vsub_add_vsub_cancel],
    inner_add_right, inner_sub_right]
  refine (abs_add_le _ _).trans ?_
  have hsub := abs_sub (inner ℝ (S'.basis k) (x -ᵥ S.center))
    (inner ℝ (S'.basis k) (p -ᵥ S.center))
  push_cast
  linarith only [hsub, hx_frame, hp_frame k, hpw' k, ht, mul_nonneg (sub_nonneg.mpr hr1) ht]

/-- **Single-inclusion crux for slab comparability.** If two `θ × 1 × 1` slabs (`θ > 0`) make angle
`< 8θ` and share a point `p`, then `S` lies in the `64`-dilation of `S'`.  This is the `r = 1` case
of `slab_dilation_subset_of_angle_lt`. -/
theorem slab_subset_dilation_of_angle_lt {θ : ℝ≥0} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (S S' : Slab θ hθ1) (hang : Prism3D.angle S S' < 8 * (θ : ℝ))
    {p : EuclideanSpace ℝ (Fin 3)}
    (hpS : p ∈ (S.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hpS' : p ∈ (S'.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    (S.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ (S'.toPrismNDim.dilation 64).carrier := by
  have h := slab_dilation_subset_of_angle_lt hθ0 hθ1 S S' hang hpS hpS' (r := 1) le_rfl
  rw [mul_one] at h
  exact fun x hx => h (PrismNDim.self_subset_dilation S.toPrismNDim le_rfl hx)

/-! ### The plank analogue: a plank against a dilated slab -/

/-- **Cross-frame coordinate bound, plank against slab** (extra69,
`rem:absInnerSlabBasisLeOfPlankFrameBounds`).  If `w` has `V`-frame coordinates bounded by twice the
plank thicknesses `![a, b, 1]`, the plank satisfies `a ≤ θ·b`, and its plane angle with the slab `S`
is at most `K·θ`, then every `S`-frame coordinate of `w` is at most `(4·K + 8) · S.thicknesses k`.

Expand `⟪e_k, w⟫ = ∑ⱼ ⟪u_j, w⟫ · ⟪e_k, u_j⟫` (`Plank.inner_eq_sum_frame`).  For the thin `k = 0` the
off-diagonal entries `⟪u_j, e₀⟫` (`j ≠ 0`) are at most the angle
(`Plank.abs_inner_basis_ne_zero_le_angle`), giving `2a + 2b·Kθ + 2·Kθ ≤ (4K + 2)·θ` from
`a ≤ θb ≤ θ` and `b ≤ 1`; for `k ≠ 0` the unit widths give `2a + 2b + 2 ≤ 6`.  Neither `0 < θ`
nor `1 ≤ K` is used. -/
theorem abs_inner_slabBasis_le_of_plank_frame_bounds
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (V : Plank a b hab hb1) (S : Slab θ hθ1) (K : ℝ≥0)
    (haθb : a ≤ θ * b) (hang : Prism3D.angle V S ≤ (K : ℝ) * (θ : ℝ))
    (w : EuclideanSpace ℝ (Fin 3))
    (hw : ∀ j : Fin 3, |inner ℝ (V.basis j) w| ≤ 2 * ((V.thicknesses j : ℝ≥0) : ℝ)) :
    ∀ k : Fin 3, |inner ℝ (S.basis k) w| ≤ (4 * (K : ℝ) + 8) * ((S.thicknesses k : ℝ≥0) : ℝ) := by
  have haθb_real : (a : ℝ) ≤ (θ : ℝ) * (b : ℝ) :=
    (NNReal.coe_le_coe.mpr haθb).trans_eq (NNReal.coe_mul θ b)
  have hab_real : (a : ℝ) ≤ (b : ℝ) := NNReal.coe_le_coe.mpr hab
  have hb1_real : (b : ℝ) ≤ 1 := NNReal.coe_le_coe.mpr hb1
  have hθ_nonneg : 0 ≤ (θ : ℝ) := NNReal.coe_nonneg _
  have hK_nonneg : 0 ≤ (K : ℝ) := NNReal.coe_nonneg _
  have hd₀ : (0 : ℝ) ≤ 2 * (a : ℝ) := mul_nonneg zero_le_two (NNReal.coe_nonneg a)
  have hd₁ : (0 : ℝ) ≤ 2 * (b : ℝ) := mul_nonneg zero_le_two (NNReal.coe_nonneg b)
  have hd₂ : (0 : ℝ) ≤ 2 * (1 : ℝ) := mul_nonneg zero_le_two zero_le_one
  -- Extract three hw bounds using explicit thicknesses
  rw [Prism3D.thicknesses_eq V] at hw
  have hw0 : |inner ℝ (V.basis 0) w| ≤ 2 * (a : ℝ) := hw 0
  have hw1 : |inner ℝ (V.basis 1) w| ≤ 2 * (b : ℝ) := hw 1
  have hw2 : |inner ℝ (V.basis 2) w| ≤ 2 * (1 : ℝ) := hw 2
  -- For k = 0, j ≠ 0 the entry is bounded by the angle: |⟪S.basis 0, V.basis j⟫| ≤ angle V S ≤ K*θ
  have hc_j0 (j : Fin 3) (hj : j ≠ 0) : |inner ℝ (S.basis 0) (V.basis j)| ≤ (K : ℝ) * (θ : ℝ) := by
    rw [real_inner_comm]
    exact (abs_inner_basis_ne_zero_le_angle V S hj).trans hang
  -- Prove the three concrete bounds
  have h0 : |inner ℝ (S.basis 0) w| ≤ (4 * (K : ℝ) + 8) * (θ : ℝ) :=
    (abs_inner_basis_zero_le_of_cross_bounds V.basis S.basis w hw0 hw1 hw2
      hd₀ hd₁ hd₂ hc_j0).trans <| by
      linarith only [haθb_real, hθ_nonneg, mul_nonneg hθ_nonneg (sub_nonneg.mpr hb1_real),
        mul_nonneg (mul_nonneg hK_nonneg hθ_nonneg) (sub_nonneg.mpr hb1_real),
        mul_nonneg hK_nonneg hθ_nonneg]
  have hk (k : Fin 3) : |inner ℝ (S.basis k) w| ≤ (4 * (K : ℝ) + 8) * (1 : ℝ) :=
    (abs_inner_basis_le_of_frame_bounds V.basis S.basis w hw0 hw1 hw2 hd₀ hd₁ hd₂ k).trans
      (by linarith only [hab_real, hb1_real, hK_nonneg])
  intro k
  rw [Prism3D.thicknesses_eq S]
  exact match k with
    | 0 => h0
    | 1 => hk 1
    | 2 => hk 2

/-- **A plank meeting a dilated slab lies in a slightly larger dilation** (extra69,
`rem:plankSubsetDilationOfAngleLe`).  For an `a × b × 1` plank `V` with `a ≤ θ·b` making plane angle
at most `K·θ` with the `θ × 1 × 1` slab `S`, any point `p` lying both in `V` and in the dilation
`S^(Cset)` forces `V ⊆ S^(Cset + 4·K + 8)`.

For `x ∈ V` the difference `x - p` has `V`-frame coordinates at most twice the thicknesses, so
`Plank.abs_inner_slabBasis_le_of_plank_frame_bounds` bounds its `S`-frame coordinates by `4K + 8`
half-widths, and the offset of `p` from the centre of `S` adds a further `Cset`.  Unlike the
two-slab `Plank.slab_subset_dilation_of_angle_lt` this needs no positivity of `θ`, no `1 ≤ K` and no
`1 ≤ Cset`, and asks only that `p` lie in the *dilated* slab. -/
theorem plank_subset_dilation_of_angle_le
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (V : Plank a b hab hb1) (S : Slab θ hθ1) (K Cset : ℝ≥0)
    (haθb : a ≤ θ * b) (hang : Prism3D.angle V S ≤ (K : ℝ) * (θ : ℝ))
    {p : EuclideanSpace ℝ (Fin 3)}
    (hpV : p ∈ (V.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hpS : p ∈ ((S.toPrismNDim.dilation Cset).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    (V.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (S.toPrismNDim.dilation (Cset + 4 * K + 8)).carrier := by
  have hpV' := abs_inner_le_of_mem_carrier V.toPrismNDim hpV
  have hpS' := abs_inner_le_of_mem_dilation S.toPrismNDim Cset hpS
  intro x hxV
  have hxV' := abs_inner_le_of_mem_carrier V.toPrismNDim hxV
  have hw : ∀ j : Fin 3, |inner ℝ (V.basis j) (x -ᵥ p)| ≤ 2 * ((V.thicknesses j : ℝ≥0) : ℝ) := by
    intro j
    rw [show x -ᵥ p = (x -ᵥ V.center) - (p -ᵥ V.center) from
      (vsub_sub_vsub_cancel_right x p V.center).symm, inner_sub_right]
    exact (abs_sub _ _).trans (by linarith only [hxV' j, hpV' j])
  have hframe := abs_inner_slabBasis_le_of_plank_frame_bounds V S K haθb hang (x -ᵥ p) hw
  refine mem_dilation_of_abs_inner_le S.toPrismNDim _ fun k => ?_
  rw [show x -ᵥ S.center = (x -ᵥ p) + (p -ᵥ S.center) from
    (vsub_add_vsub_cancel x p S.center).symm, inner_add_right]
  refine (abs_add_le _ _).trans ?_
  push_cast
  linarith only [hframe k, hpS' k]




end Plank

end
