/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.KatzTaoPlankInputs
public import Kakeya.DimensionThree.Plank.TransversePlankEstimate
public import Kakeya.DimensionThree.Plank.SlabFamilyControl
public import Kakeya.DimensionThree.Plank.GlobalPlankFactorization

/-!
# The normalised inner family of GWZ Proposition 6.6(B)

The Part-(B) inner output demanded by `Kakeya.factoringAndMultPropGlobal`, assembled from the honest
inner normalisation `Plank.normaliseTubesInsidePlank` (geometry in
`Kakeya.DimensionThree.Plank.TubePlankNormalisation`).

`Kakeya.innerShadedPlankFamily` produces, from a family of fine `δ`-tubes inside an `a × b × 1`
plank `W` and its affine normalisation, a family of **shaded** planks of the exact dimensions
`a' = δ/b`, `b' = δ/a`, which

* lies in the working window `closedBall 0 4`;
* has the preserved eccentricity `a'/b' = a/b`, together with `δ ≤ a'`, `a' ≤ a₀`, `b' ≤ b₀ᵢ`;
* transfers fullness and maximal density from the fine family, up to one absolute constant `Cnorm`;
* satisfies the **wide-slab pullback link**: a member of the inner family contained in a wide slab
  `S` comes from a fine tube contained in `f⁻¹(S)`.

## Where the `γ = 1` count plugs in

The pullback link is exactly the interface of the counting step
(blueprint `lem:factorInnerSlabNonconcentration`): together with the coarse-parent data
`Kakeya.CoarseParentSystem` recorded here — the assignment `fine → coarse`, containment of a fine
tube in its coarse parent, two-sided comparability of the coarse fibres, containment of the parents
in `W`, and the Frostman property of the coarse family in `W` — and with a coarse container `K_S ⊆ W`
of volume `≲ φ |W|` capturing the parents of every fine tube pulling back into `S`
(blueprint `eq:factor-coarse-container-compatibility`, which fine-tube containment does *not*
imply), `Kakeya.card_le_of_frostmanIn` and `Kakeya.card_le_of_comparable_fibres_of_selected_le`
give the `γ = 1` bound `|{i : P i ⊆ S}| ≤ Cfib² · C_F · Cvol · φ · |q|`.

That composition is carried out here: `Kakeya.card_parents_le_of_container` is the Frostman coarse
count, `Kakeya.card_leaves_le_of_container` the fine count, and
`Kakeya.innerFamilySlabNonconcentration` the packaged `γ = 1` inner family.  Its slab clause is
reported with the **raw** coefficient `Cfib² · innerCoarseTubeVolumeRatio · CF · Cvol`, not absorbed
into a power of `a'`; the caller absorbs it into `δ ^ (-ηᵢ)` instead.  See that theorem's docstring
for why the `a'`-absorption is unavailable to Section 6.6(B).
-/

@[expose] public section

open MeasureTheory Kakeya ConvexSpaceBody
open scoped NNReal Real ENNReal

noncomputable section

namespace Kakeya

/-- **The coarse-parent data of the `γ = 1` inner count** (blueprint
`lem:factorInnerSlabNonconcentration`).

A fine family `(T i)_{i ∈ q}` of `δ`-tubes, a coarse family `(R k)_{k ∈ r}` of `ρ`-tubes inside an
`a × b × 1` plank `W`, an assignment of parents, two-sided comparability of the coarse fibres with
common size `m` and factor `Cfib`, and the `CF`-Frostman property of the coarse family in `W`.

These are exactly the facts the inner count consumes.  Keeping them in one structure is what stops
them from being smuggled into a consumer's statement: the fibre bounds are stated in the shape
required by `Kakeya.card_le_of_comparable_fibres`, and the Frostman field in the shape required by
`Kakeya.card_le_of_frostmanIn`. -/
structure CoarseParentSystem {ιq ιr : Type*} [DecidableEq ιq] [DecidableEq ιr]
    (q : Finset ιq) (r : Finset ιr) {δ ρ : ℝ≥0}
    (T : ιq → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (R : ιr → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    (Cfib CF m : ℝ≥0) where
  /-- The coarse parent of each fine index. -/
  assign : ιq → ιr
  /-- Parents of used fine indices are used coarse indices. -/
  assign_mem : ∀ i ∈ q, assign i ∈ r
  /-- Each fine tube lies in its coarse parent. -/
  leaf_le_parent : ∀ i ∈ q, (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody
  /-- The fibre comparability factor is at least `1`. -/
  one_le_Cfib : 1 ≤ Cfib
  /-- Every coarse fibre carries at least `Cfib⁻¹ m` fine indices. -/
  fibre_lower : ∀ k ∈ r, Cfib⁻¹ * m ≤ (({i ∈ q | assign i = k}).card : ℝ≥0)
  /-- Every coarse fibre carries at most `Cfib m` fine indices. -/
  fibre_upper : ∀ k ∈ r, (({i ∈ q | assign i = k}).card : ℝ≥0) ≤ Cfib * m
  /-- Every coarse tube lies in the plank. -/
  parent_le_plank : ∀ k ∈ r, (R k).toConvexSpaceBody ≤ W.toConvexSpaceBody
  /-- The coarse family is `CF`-Frostman in the plank. -/
  frostman : IsFrostmanIn r (fun k => (R k).toConvexSpaceBody) W.toConvexSpaceBody (CF : ENNReal)
  /-- The coarse family is nonempty (it carries the fine family). -/
  parents_nonempty : r.Nonempty

/-- **A coarse-parent system depends only on the carriers of the fine family.**

Every field of `Kakeya.CoarseParentSystem` that mentions the fine family mentions it through
`ShadedTube.toConvexSpaceBody`, i.e. through the underlying tube; no field sees a shade.  So the
system transports verbatim along a re-shading of the same tubes.  Section 6.6(B) needs exactly this:
the inner pipeline is run on the fine tubes carrying the *refined* Proposition-5.1 shades, while the
coarse-parent data is built from the datum's original family. -/
def CoarseParentSystem.ofTubeEq {ιq ιr : Type*} [DecidableEq ιq] [DecidableEq ιr]
    {q : Finset ιq} {r : Finset ιr} {δ ρ : ℝ≥0}
    {T T' : ιq → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {R : ιr → Tube ρ (EuclideanSpace ℝ (Fin 3))}
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {W : Plank a b hab hb1} {Cfib CF m : ℝ≥0}
    (data : CoarseParentSystem q r T R W Cfib CF m)
    (hTT' : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody) :
    CoarseParentSystem q r T' R W Cfib CF m := by
  exact {
    assign := data.assign
    assign_mem := data.assign_mem
    leaf_le_parent := by
      intro i hi
      rw [hTT' i]
      exact data.leaf_le_parent i hi
    one_le_Cfib := data.one_le_Cfib
    fibre_lower := data.fibre_lower
    fibre_upper := data.fibre_upper
    parent_le_plank := data.parent_le_plank
    frostman := data.frostman
    parents_nonempty := data.parents_nonempty }

/-! ### Wide slabs that meet the family are automatically tangent -/

/-- **Tangency of a wide slab, from the plank angle alone.**

The `Slab`-typed `Plank.abs_inner_slabNormal_le_of_angle` never uses the two long half-widths of the
slab — only `S.basis 0` and `Prism3D.angle P S` enter — so the same estimate holds for a *wide* slab
`Prism3D φ R R`.  The constant `2` covers the regime `1 < φ`, where the bound is trivial because
`|⟪S.basis 0, v⟫| ≤ 1`.

This is the observation that makes the coarse-container obligation of
`Kakeya.innerFamilySlabNonconcentration` tractable: a slab whose thin normal is *not* nearly
orthogonal to `g 0` cannot make the plank angle small, so it collects no planks at all. -/
theorem abs_inner_wideSlab_normal_le_of_angle_of_orthogonal
    {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
    (P : Plank a' b' ha'b' hb'1) {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1)
    (hPv : (inner ℝ (P.basis 0) v : ℝ) = 0)
    {φ R : ℝ≥0} {hφR : φ ≤ R} (S : Prism3D φ R R hφR le_rfl)
    (hang : Prism3D.angle P S ≤ (φ : ℝ)) :
    |(inner ℝ (S.basis 0) v : ℝ)| ≤ 2 * (φ : ℝ) := by
  by_cases hφ1 : φ ≤ 1
  · -- Case `φ ≤ 1`: copy the body of `abs_inner_slabNormal_le_of_angle` with `θ := φ`, `e := v`.
    let n : EuclideanSpace ℝ (Fin 3) := P.basis 0
    let mm : EuclideanSpace ℝ (Fin 3) := S.basis 0
    let c : ℝ := inner ℝ n mm
    have hn : ‖n‖ = 1 := by simp [n]
    have hmm : ‖mm‖ = 1 := by simp [mm]
    have hphi0 : 0 ≤ (φ : ℝ) := NNReal.coe_nonneg φ
    have hφ1' : (φ : ℝ) ≤ 1 := by exact_mod_cast hφ1
    -- `1 ≤ π` (as in the model proof): `sin (π/2) = 1` and `sin x ≤ x`.
    have hpi_ge_one : (1 : ℝ) ≤ Real.pi := by
      have hsin_le_pi2 : Real.sin (Real.pi / 2) ≤ Real.pi / 2 :=
        Real.sin_le (show 0 ≤ Real.pi / 2 by linarith [Real.pi_pos])
      have hsin_pi2 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      have h1le_pi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith
      have hpi2_le_pi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
      linarith
    have hφ1π : (φ : ℝ) ≤ Real.pi := by linarith [hφ1', hpi_ge_one]
    -- Step 1: cos φ ≤ |c|
    have hcosc : Real.cos (φ : ℝ) ≤ |c| := by
      change Real.cos (φ : ℝ) ≤ |inner ℝ (P.basis 0) (S.basis 0)|
      rw [← Prism3D.cos_angle P S]
      refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ ?_ ?_
      · exact Prism3D.angle_nonneg P S
      · exact hφ1π
      · exact hang
    -- cos φ ≥ 0 since 1 - φ²/2 ≤ cos φ and φ ≤ 1
    have hcosφ_nonneg : 0 ≤ Real.cos (φ : ℝ) := by
      have hlower : 1 - (φ : ℝ) ^ 2 / 2 ≤ Real.cos (φ : ℝ) := by
        simpa using (Real.one_sub_sq_div_two_le_cos (x := (φ : ℝ)))
      nlinarith [hlower, hφ1']
    -- Step 2: 1 - c² ≤ φ²
    have hsin_le_φ : Real.sin (φ : ℝ) ≤ (φ : ℝ) := Real.sin_le hphi0
    have hsin_nonneg : 0 ≤ Real.sin (φ : ℝ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hphi0 hφ1π
    have hsin_sq : (Real.sin (φ : ℝ)) ^ 2 ≤ (φ : ℝ) ^ 2 := by
      nlinarith [hsin_le_φ, hsin_nonneg]
    have hcos_sq : (Real.cos (φ : ℝ)) ^ 2 = 1 - (Real.sin (φ : ℝ)) ^ 2 := by
      have h := Real.sin_sq_add_cos_sq (φ : ℝ)
      nlinarith
    have hcosφ_sq_ge : 1 - (φ : ℝ) ^ 2 ≤ (Real.cos (φ : ℝ)) ^ 2 := by
      nlinarith [hcos_sq, hsin_sq]
    have hc_sq_ge : (Real.cos (φ : ℝ)) ^ 2 ≤ |c| ^ 2 := by
      exact sq_le_sq' (by nlinarith [hcosφ_nonneg, abs_nonneg c]) hcosc
    have hcq : c ^ 2 = |c| ^ 2 := by rw [sq_abs]
    have hsq2 : 1 - c ^ 2 ≤ (φ : ℝ) ^ 2 := by
      rw [hcq]
      nlinarith [hcosφ_sq_ge, hc_sq_ge]
    -- Step 3: decompose w = mm - c • n
    let w : EuclideanSpace ℝ (Fin 3) := mm - c • n
    have hw_norm_sq : ‖w‖ ^ 2 = 1 - c ^ 2 := by
      change ‖mm - c • n‖ ^ 2 = 1 - c ^ 2
      rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm, norm_smul, hmm, hn]
      simp [c, n, mm, sq_abs]
      ring
    -- Step 4: inner mm v = inner w v
    have hw_v : inner ℝ w v = inner ℝ mm v := by
      change inner ℝ (mm - c • n) v = inner ℝ mm v
      rw [inner_sub_left, real_inner_smul_left, hPv]
      ring
    -- Step 5: |inner mm v| = |inner w v| ≤ ‖w‖ ≤ φ
    have hwle : |inner ℝ w v| ≤ ‖w‖ := by
      have hit := abs_real_inner_le_norm w v
      rwa [hv, mul_one] at hit
    have hw_phi : ‖w‖ ≤ (φ : ℝ) := by
      nlinarith [hw_norm_sq, hsq2, norm_nonneg w, hphi0]
    have hw_v' : inner ℝ (S.basis 0) v = inner ℝ w v := by simpa [mm] using hw_v.symm
    calc
      |inner ℝ (S.basis 0) v| = |inner ℝ w v| := by rw [← hw_v']
      _ ≤ (φ : ℝ) := (hwle.trans hw_phi)
      _ ≤ 2 * (φ : ℝ) := by linarith [hphi0]
  · -- Case `1 < φ`: `|inner ℝ (S.basis 0) v| ≤ ‖S.basis 0‖ * ‖v‖ = 1 ≤ φ ≤ 2φ`.
    have hφgt1_nn : 1 < φ := lt_of_not_ge hφ1
    have hφgt1 : (1 : ℝ) < (φ : ℝ) := by exact_mod_cast hφgt1_nn
    have hφge1 : (1 : ℝ) ≤ (φ : ℝ) := le_of_lt hφgt1
    have hphi0 : 0 ≤ (φ : ℝ) := NNReal.coe_nonneg φ
    have hφ2 : (φ : ℝ) ≤ 2 * (φ : ℝ) := by linarith
    have hstep1 : |(inner ℝ (S.basis 0) v : ℝ)| ≤ ‖S.basis 0‖ * ‖v‖ :=
      abs_real_inner_le_norm (S.basis 0) v
    have hnorm1 : ‖S.basis 0‖ = 1 := by simp
    have hle1 : |(inner ℝ (S.basis 0) v : ℝ)| ≤ 1 := by
      calc
        |(inner ℝ (S.basis 0) v : ℝ)| ≤ ‖S.basis 0‖ * ‖v‖ := hstep1
        _ = 1 := by simp [hnorm1, hv]
    exact le_trans (le_trans hle1 hφge1) hφ2

/-- **A wide slab that collects at least one plank is tangent.**

Membership in `Plank.inWideSlabFamily` carries the angle bound `Prism3D.angle (P i) S ≤ φ`, so a
single member is enough.  Contrapositively, a slab failing the tangency bound has an *empty* wide
slab family. -/
theorem abs_inner_wideSlab_normal_le_of_nonempty
    {ι : Type*} {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
    (s : Finset ι) (P : ι → Plank a' b' ha'b' hb'1)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1)
    (hPv : ∀ i ∈ s, (inner ℝ ((P i).basis 0) v : ℝ) = 0)
    {φ R : ℝ≥0} {hφR : φ ≤ R} (S : Prism3D φ R R hφR le_rfl)
    (hne : (Plank.inWideSlabFamily s P S).Nonempty) :
    |(inner ℝ (S.basis 0) v : ℝ)| ≤ 2 * (φ : ℝ) := by
  obtain ⟨i, hi⟩ := hne
  exact abs_inner_wideSlab_normal_le_of_angle_of_orthogonal (P i) hv
    (hPv i (Plank.mem_inWideSlabFamily.mp hi).1) S
    ((Plank.mem_inWideSlabFamily.mp hi).2.2)

/-! ### Comparing a wide slab with a unit slab -/

/-- **A wide slab, re-centred to a unit slab, on the part that matters.**

`Plank.coarseTubeContainerOfPullbackSlab` and `Plank.thickenedPullbackSlabVolume` are stated for
`Slab θ = Prism3D θ 1 1`, while the container obligation quantifies over the *window*-sized
`Prism3D φ Rslab Rslab`.  The bridge is that only `f '' W.carrier ∩ S.carrier` ever matters, and on
that set the two long coordinates are already bounded by `1` — measured from `f W.center` rather
than from `S.center`.  Re-centring along the thin axis,

`c' = f W.center + ⟪S.center - f W.center, S.basis 0⟫ • S.basis 0`,

leaves the thin coordinate unchanged (the correction is orthogonal to `S.basis 0`) and replaces the
two long ones by coordinates of `y - f W.center`, which the normalisation window bounds by `1`. -/
theorem exists_recentredSlab_of_wideSlab
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hWimg : ∀ x ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))), ‖f x - f W.center‖ ≤ 1)
    {φ : ℝ≥0} (hφ1 : φ ≤ 1) {hφR : φ ≤ Rslab} (S : Prism3D φ Rslab Rslab hφR le_rfl) :
    ∃ Ŝ : Slab φ hφ1, Ŝ.basis = S.basis ∧
      (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ''
          (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ (S.carrier : Set _)
        ⊆ (Ŝ.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  let e₀ : EuclideanSpace ℝ (Fin 3) := S.basis 0
  let p : EuclideanSpace ℝ (Fin 3) := f W.center
  let c' : EuclideanSpace ℝ (Fin 3) := p + (inner ℝ (S.center - p) e₀) • e₀
  let Ŝ : Slab φ hφ1 :=
    { toPrismNDim := PrismNDim.mk' c' S.basis ![φ, 1, 1]
      thicknesses_eq := rfl }
  have hŜ_basis : Ŝ.basis = S.basis := by
    dsimp [Ŝ]
    exact PrismNDim.basis_mk' c' S.basis ![φ, 1, 1]
  have hŜ_center : Ŝ.center = c' := by
    dsimp [Ŝ]
    exact PrismNDim.center_mk' c' S.basis ![φ, 1, 1]
  have hŜ_thick : Ŝ.thicknesses = ![φ, 1, 1] := by
    dsimp [Ŝ]
    exact PrismNDim.thicknesses_mk' c' S.basis ![φ, 1, 1]
  have hc'0 : inner ℝ e₀ (S.center - c') = 0 := by
    dsimp [c', e₀]
    rw [show S.center - (p + (inner ℝ (S.center - p) (S.basis 0)) • S.basis 0)
          = (S.center - p) - (inner ℝ (S.center - p) (S.basis 0)) • S.basis 0 by abel]
    rw [inner_sub_right, real_inner_smul_right, real_inner_comm,
      real_inner_self_eq_norm_sq, S.basis.norm_eq_one]
    ring
  have hc'j : ∀ j : Fin 3, j ≠ (0 : Fin 3) → inner ℝ (S.basis j) (c' - p) = 0 := by
    intro j hj
    dsimp [c', e₀]
    rw [show (p + (inner ℝ (S.center - p) (S.basis 0)) • S.basis 0) - p
          = (inner ℝ (S.center - p) (S.basis 0)) • S.basis 0 by abel]
    rw [real_inner_smul_right, S.basis.inner_eq_zero hj]
    ring
  refine ⟨Ŝ, hŜ_basis, ?cont⟩
  rintro y ⟨⟨x, hx, rfl⟩, ys⟩
  rw [Ŝ.mem_carrier_iff]
  intro j
  rw [hŜ_basis, hŜ_center]
  have hvsub : (f x -ᵥ c' : EuclideanSpace ℝ (Fin 3)) = f x - c' := vsub_eq_sub (f x) c'
  rw [hvsub, S.basis.repr_apply_apply]
  fin_cases j
  · -- `j = 0`, bound `φ`
    have hc'0' : inner ℝ (S.basis 0) (S.center - c') = 0 := by simpa [e₀] using hc'0
    have hys0 := (S.mem_carrier_iff (f x)).1 ys 0
    have hvsubS : (f x -ᵥ S.center : EuclideanSpace ℝ (Fin 3)) = f x - S.center :=
      vsub_eq_sub (f x) S.center
    have h00 : |inner ℝ (S.basis 0) (f x - S.center)| ≤ (φ : ℝ) := by
      rw [hvsubS, S.basis.repr_apply_apply] at hys0
      simpa [S.thicknesses_eq] using hys0
    have hpr : (f x - c' : EuclideanSpace ℝ (Fin 3)) = (f x - S.center) + (S.center - c') := by
      abel
    change |inner ℝ (S.basis (0 : Fin 3)) (f x - c')| ≤ ↑(Ŝ.thicknesses (0 : Fin 3))
    rw [hpr, inner_add_right, hc'0', add_zero]
    simpa [hŜ_thick] using h00
  · -- `j = 1`, bound `1`
    have hyc' : inner ℝ (S.basis 1) (f x - c') = inner ℝ (S.basis 1) (f x - p) := by
      rw [show f x - c' = (f x - p) + (p - c') by abel]
      rw [inner_add_right]
      have hpc : inner ℝ (S.basis 1) (p - c') = 0 := by
        rw [show p - c' = -(c' - p) by abel, inner_neg_right, hc'j 1 (by decide), neg_zero]
      rw [hpc, add_zero]
    have hyn : ‖f x - p‖ ≤ 1 := by simpa [p] using hWimg x hx
    have hle1 : |inner ℝ (S.basis 1) (f x - p)| ≤ 1 := by
      calc
        |inner ℝ (S.basis 1) (f x - p)| ≤ ‖S.basis 1‖ * ‖f x - p‖ :=
          abs_real_inner_le_norm (S.basis 1) (f x - p)
        _ = ‖f x - p‖ := by rw [S.basis.norm_eq_one 1, one_mul]
        _ ≤ 1 := hyn
    simpa [hyc', hŜ_thick] using hle1
  · -- `j = 2`, bound `1`
    have hyc' : inner ℝ (S.basis 2) (f x - c') = inner ℝ (S.basis 2) (f x - p) := by
      rw [show f x - c' = (f x - p) + (p - c') by abel]
      rw [inner_add_right]
      have hpc : inner ℝ (S.basis 2) (p - c') = 0 := by
        rw [show p - c' = -(c' - p) by abel, inner_neg_right, hc'j 2 (by decide), neg_zero]
      rw [hpc, add_zero]
    have hyn : ‖f x - p‖ ≤ 1 := by simpa [p] using hWimg x hx
    have hle1 : |inner ℝ (S.basis 2) (f x - p)| ≤ 1 := by
      calc
        |inner ℝ (S.basis 2) (f x - p)| ≤ ‖S.basis 2‖ * ‖f x - p‖ :=
          abs_real_inner_le_norm (S.basis 2) (f x - p)
        _ = ‖f x - p‖ := by rw [S.basis.norm_eq_one 2, one_mul]
        _ ≤ 1 := hyn
    simpa [hyc', hŜ_thick] using hle1

/-! ### Discharging the coarse-container obligation -/

/-- **The guarded coarse container.**

This discharges the container hypothesis of `Kakeya.innerFamilySlabNonconcentration` under its two
guards: `a / b ≤ φ` and the tangency `|⟪S.basis 0, g 0⟫| ≤ 2φ`.

Three regimes.  For `1 < φ` the plank itself works, since `Cvol · φ ≥ 1`.  For `φ ≤ 1` the wide slab
is replaced by the re-centred unit slab of `Kakeya.exists_recentredSlab_of_wideSlab`, and then
`Plank.coarseTubeContainerOfPullbackSlab` supplies the containment while
`Plank.thickenedPullbackSlabVolume` supplies the volume — the tangency guard is exactly the
hypothesis the latter needs, and it transfers because the re-centred slab has the same frame.  If
the pullback is empty the container is a point.

No geometry is developed here; only the existing S6G17/S6G19 estimates are combined. -/
theorem exists_coarse_container_of_guards {κ : ℝ} (hκ : 0 < κ) (cfac : ℝ≥0) (hcfac : 0 < cfac) :
    ∃ Cvol : ℝ≥0, 1 ≤ Cvol ∧
      ∀ {ιq ιr : Type*} {a b δ ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (ha : 0 < a) (hρa : ρ ≤ a)
        (W : Plank a b hab hb1) (q : Finset ιq)
        (T : ιq → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (R : ιr → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ιq → ιr)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0)
        (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))),
        0 < J → Plank.IsPlankNormalisation W f κ g →
        (∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E) →
        (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ''
            (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 1 →
        (∀ x ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))), ‖f x - f W.center‖ ≤ 1) →
        cfac ≤ J * (a * b) →
        (∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ q, ((R (assign i)).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ ((R (assign i)).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab) (S : Prism3D φ Rslab Rslab hφR le_rfl),
          a / b ≤ φ → |(inner ℝ (S.basis 0) (g 0) : ℝ)| ≤ 2 * (φ : ℝ) →
          ∃ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)), K ≤ W.toConvexSpaceBody ∧
            volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3)))
              ≤ (Cvol : ENNReal) * (φ : ENNReal)
                * volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∧
            ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
                ⊆ (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹'
                    (S.carrier : Set (EuclideanSpace ℝ (Fin 3))) →
              (R (assign i)).toConvexSpaceBody ≤ K := by
  classical
  obtain ⟨Cpull, hCpull, hS17⟩ := Plank.volumePullbackNormalisedSlab cfac hcfac
  -- `coarseTubeContainerOfPullbackSlab` needs `0 < δ`, which is absent here; its proof only uses
  -- `NNReal.coe_nonneg δ` with `Crad = 4`, so we reproduce the containment inline with `Crad = 4`.
  obtain ⟨Cctr, hCctr, hS19vol⟩ :=
    Plank.thickenedPullbackSlabVolume κ hκ 2 Cpull 4 hCpull (by norm_num)
  refine ⟨max 1 (Cctr * Cpull), le_max_left _ _, ?_⟩
  intro ιq ιr a b δ ρ hab hb1 ha hρa W q T R assign f J g hJ hnorm hvolf himg hWimg hJab
    hTW hRW hTR φ hφR S hφab htang
  let Cvol : ℝ≥0 := max 1 (Cctr * Cpull)
  -- S6G16 helper: volume of the pullback of a unit slab is `≤ Cpull·θ·|W|`.
  have hS16 (θ : ℝ≥0) (hθ1 : θ ≤ 1) (S' : Slab θ hθ1) :
      volume (W.carrier ∩ f ⁻¹' S'.carrier)
        ≤ (Cpull : ENNReal) * (θ : ENNReal) * volume W.carrier :=
    (hS17 ha W f J hJ hvolf himg hJab θ hθ1 S').2
  by_cases hφ1 : φ ≤ 1
  · -- Case `φ ≤ 1`
    have hφ0 : 0 < φ := by
      have hb0 : 0 < b := lt_of_lt_of_le ha hab
      have hab_pos : 0 < a / b := by
        rw [← NNReal.coe_pos]
        rw [NNReal.coe_div]
        exact div_pos (by exact_mod_cast ha) (by exact_mod_cast hb0)
      exact lt_of_lt_of_le hab_pos hφab
    obtain ⟨Ŝ, hŜbasis, hŜsub⟩ := exists_recentredSlab_of_wideSlab W f hWimg hφ1 S
    have htang' : |(inner ℝ (Ŝ.basis 0) (g 0) : ℝ)| ≤ 2 * (φ : ℝ) := by
      simpa [hŜbasis] using htang
    by_cases hne : (W.carrier ∩ f ⁻¹' Ŝ.carrier).Nonempty
    · -- Sub-case: pullback nonempty.  Build `K` with carrier `W ∩ N_{4ρ}(W ∩ f⁻¹ Ŝ)`.
      have hInnerConv : Convexity.IsConvexSet ℝ (W.carrier ∩ f ⁻¹' Ŝ.carrier) :=
        (hS17 ha W f J hJ hvolf himg hJab φ hφ1 Ŝ).1
      have hThickConv : Convexity.IsConvexSet ℝ
          (Metric.cthickening ((4 * ρ : ℝ≥0) : ℝ) (W.carrier ∩ f ⁻¹' Ŝ.carrier)) := by
        exact (hInnerConv.convex.cthickening ((4 * ρ : ℝ≥0) : ℝ)).isConvexSet
      have hThickClosed : IsClosed
          (Metric.cthickening ((4 * ρ : ℝ≥0) : ℝ) (W.carrier ∩ f ⁻¹' Ŝ.carrier)) :=
        Metric.isClosed_cthickening
      let Kset : Set (EuclideanSpace ℝ (Fin 3)) :=
        W.carrier ∩ Metric.cthickening ((4 * ρ : ℝ≥0) : ℝ) (W.carrier ∩ f ⁻¹' Ŝ.carrier)
      have hKcompact : IsCompact Kset := W.isCompact'.inter_right hThickClosed
      have hKnonempty : Kset.Nonempty := by
        exact hne.mono (fun x hx => ⟨hx.1,
          (Metric.self_subset_cthickening (δ := ((4 * ρ : ℝ≥0) : ℝ))
            (W.carrier ∩ f ⁻¹' Ŝ.carrier)) hx⟩)
      let K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
        { carrier := Kset,
          convex' := W.convex'.inter hThickConv,
          isCompact' := hKcompact,
          nonempty' := hKnonempty }
      have hKleW : K ≤ W.toConvexSpaceBody := by
        exact SetLike.coe_subset_coe.mpr (by
          change Kset ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))
          exact Set.inter_subset_left)
      -- the volume bound
      have hvol_thick : volume (W.carrier ∩ Metric.cthickening ((4 * ρ : ℝ≥0) : ℝ)
          (W.carrier ∩ f ⁻¹' Ŝ.carrier))
          ≤ (Cctr : ENNReal) * (Cpull : ENNReal) * (φ : ENNReal) * volume W.carrier :=
        hS19vol ha hρa W f g hnorm hWimg hS16 φ hφ0 hφ1 Ŝ hφab htang'
      have hCC : (Cctr : ENNReal) * (Cpull : ENNReal) ≤ (Cvol : ENNReal) := by
        rw [← ENNReal.coe_mul]
        exact ENNReal.coe_le_coe.mpr (le_max_right (1 : ℝ≥0) (Cctr * Cpull))
      have hKvol : volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ≤ (Cvol : ENNReal) * (φ : ENNReal) * volume W.carrier := by
        calc
          volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3)))
              = volume (W.carrier ∩ Metric.cthickening ((4 * ρ : ℝ≥0) : ℝ)
                  (W.carrier ∩ f ⁻¹' Ŝ.carrier)) := rfl
          _ ≤ (Cctr : ENNReal) * (Cpull : ENNReal) * (φ : ENNReal) * volume W.carrier := hvol_thick
          _ ≤ (Cvol : ENNReal) * (φ : ENNReal) * volume W.carrier := by
            gcongr
      -- the containment: reproduce `coarseTubeContainerOfPullbackSlab` (fine tube → coarse tube
      -- within `4ρ` of the pullback), which needs no positivity of `δ`.
      have hcontPull (i : ιq) (hi : i ∈ q)
          (hTi_in : (T i).carrier ⊆ W.carrier ∩ f ⁻¹' Ŝ.carrier) :
          (R (assign i)).carrier ⊆
            (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
              Metric.cthickening ((4 * ρ : ℝ≥0) : ℝ)
                (W.carrier ∩ f ⁻¹' Ŝ.carrier) := by
        let Tf : Tube δ (EuclideanSpace ℝ (Fin 3)) := (T i).toTube
        let Rc : Tube ρ (EuclideanSpace ℝ (Fin 3)) := R (assign i)
        have hclose : ∀ p ∈ segment ℝ Tf.x Tf.y,
            ∃ q ∈ segment ℝ Rc.x Rc.y, dist p q ≤ (ρ : ℝ) := by
          intro p hp
          have hpTf : p ∈ (T i).carrier := by
            change p ∈ Tf.carrier
            rw [Tf.carrier_eq]
            exact Set.mem_iUnion₂.mpr ⟨p, hp, Metric.mem_closedBall_self (NNReal.coe_nonneg δ)⟩
          have hpR : p ∈ (R (assign i)).carrier := hTR i hi hpTf
          rw [Rc.carrier_eq] at hpR
          obtain ⟨q, hq, hpq⟩ := Set.mem_iUnion₂.mp hpR
          exact ⟨q, hq, Metric.mem_closedBall.mp hpq⟩
        have hsymm : ∀ z ∈ segment ℝ Rc.x Rc.y,
            ∃ w ∈ segment ℝ Tf.x Tf.y, dist z w ≤ 3 * (ρ : ℝ) :=
          Tube.symm_hausdorff_segment
            (a := Tf.x) (b := Tf.y) (c := Rc.x) (d := Rc.y)
            (hab := Tf.norm_direction) (hcd := Rc.norm_direction)
            (hρ := (NNReal.coe_nonneg ρ)) (hclose := hclose)
        have hcthk : (R (assign i)).carrier ⊆
            Metric.cthickening ((4 * ρ : ℝ≥0) : ℝ) (W.carrier ∩ f ⁻¹' Ŝ.carrier) := by
          intro y hy
          rw [Rc.carrier_eq] at hy
          obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hy
          obtain ⟨w, hw, hzw⟩ := hsymm z hz
          refine Metric.mem_cthickening_of_dist_le y w ((4 * ρ : ℝ≥0) : ℝ) _ ?_ ?_
          · have hwTf : w ∈ (T i).carrier := by
              change w ∈ Tf.carrier
              rw [Tf.carrier_eq]
              exact Set.mem_iUnion₂.mpr ⟨w, hw, Metric.mem_closedBall_self (NNReal.coe_nonneg δ)⟩
            exact hTi_in hwTf
          · calc
              dist y w ≤ dist y z + dist z w := dist_triangle y z w
              _ ≤ (ρ : ℝ) + 3 * (ρ : ℝ) := add_le_add (Metric.mem_closedBall.mp hyz) hzw
              _ = (4 : ℝ) * (ρ : ℝ) := by ring
              _ = ((4 * ρ : ℝ≥0) : ℝ) := by norm_num [NNReal.coe_mul]
        exact Set.subset_inter (hRW i hi) hcthk
      have hcontain : ∀ i ∈ q,
          (T i).carrier ⊆ (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S.carrier →
          (R (assign i)).toConvexSpaceBody ≤ K := by
        intro i hi hTiS
        have hi_in : (T i).carrier ⊆ W.carrier ∩ f ⁻¹' Ŝ.carrier := by
          intro x hx
          have hxW : x ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := hTW i hi hx
          have hxpre : x ∈ f ⁻¹' (Ŝ.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
            rw [Set.mem_preimage]
            have hfW : f x ∈ f '' (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := ⟨x, hxW, rfl⟩
            have hfS : f x ∈ (S.carrier : Set (EuclideanSpace ℝ (Fin 3))) := hTiS hx
            exact hŜsub ⟨hfW, hfS⟩
          exact ⟨hxW, hxpre⟩
        have hRsub : (R (assign i)).carrier ⊆ Kset := by
          simpa [Kset] using hcontPull i hi hi_in
        exact SetLike.coe_subset_coe.mpr hRsub
      exact ⟨K, hKleW, hKvol, hcontain⟩
    · -- Sub-case: pullback empty.  Take `K` the single point `W.center`.
      let K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
        ConvexSpaceBody.closedBall W.center 0 le_rfl
      have hcen : W.center ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
        exact PrismNDim.center_mem_carrier (W.toPrismNDim)
      have hKleW : K ≤ W.toConvexSpaceBody := by
        exact SetLike.coe_subset_coe.mpr (by
          change (K : Set (EuclideanSpace ℝ (Fin 3))) ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))
          intro x hx
          have hx0 : x = W.center := by
            have hd : dist x W.center = 0 := le_antisymm (Metric.mem_closedBall.mp hx) dist_nonneg
            exact dist_eq_zero.mp hd
          rw [hx0]
          exact hcen)
      have hKvol : volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ≤ (Cvol : ENNReal) * (φ : ENNReal) * volume W.carrier := by
        calc
          volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3)))
              = volume (Metric.closedBall (W.center : EuclideanSpace ℝ (Fin 3)) 0) := rfl
          _ = volume ({W.center} : Set (EuclideanSpace ℝ (Fin 3))) := by
            rw [Metric.closedBall_zero]
          _ = 0 := by rw [measure_singleton]
          _ ≤ (Cvol : ENNReal) * (φ : ENNReal) * volume W.carrier := by simp
      have hcontain : ∀ i ∈ q,
          (T i).carrier ⊆ (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S.carrier →
          (R (assign i)).toConvexSpaceBody ≤ K := by
        intro i hi hTiS
        have hi_in : (T i).carrier ⊆ W.carrier ∩ f ⁻¹' Ŝ.carrier := by
          intro x hx
          have hxW : x ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := hTW i hi hx
          have hxpre : x ∈ f ⁻¹' (Ŝ.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
            rw [Set.mem_preimage]
            have hfW : f x ∈ f '' (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := ⟨x, hxW, rfl⟩
            have hfS : f x ∈ (S.carrier : Set (EuclideanSpace ℝ (Fin 3))) := hTiS hx
            exact hŜsub ⟨hfW, hfS⟩
          exact ⟨hxW, hxpre⟩
        exfalso
        exact hne ((T i).nonempty'.mono hi_in)
      exact ⟨K, hKleW, hKvol, hcontain⟩
  · -- Case `1 < φ`: take `K := W`.
    let K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := W.toConvexSpaceBody
    have hφgt1 : (1 : ℝ≥0) < φ := lt_of_not_ge hφ1
    have hCvol1 : (1 : ℝ≥0) ≤ Cvol := by simp [Cvol]
    have hle1φ : (1 : ENNReal) ≤ (φ : ENNReal) := ENNReal.coe_le_coe.mpr (le_of_lt hφgt1)
    have hle1C : (1 : ENNReal) ≤ (Cvol : ENNReal) := ENNReal.coe_le_coe.mpr hCvol1
    have hKW : K ≤ W.toConvexSpaceBody := le_rfl
    have hKvol : volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ≤ (Cvol : ENNReal) * (φ : ENNReal) * volume W.carrier := by
      calc
        volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3)))
            = volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by simp [K]
        _ = (1 : ENNReal) * (1 : ENNReal) * volume W.carrier := by simp
        _ ≤ (Cvol : ENNReal) * (φ : ENNReal) * volume W.carrier := by
          gcongr
    have hcontain : ∀ i ∈ q,
        (T i).carrier ⊆ (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S.carrier →
        (R (assign i)).toConvexSpaceBody ≤ K := by
      intro i hi hTiS
      exact SetLike.coe_subset_coe.mpr (hRW i hi)
    exact ⟨K, hKW, hKvol, hcontain⟩

/-! ### Shading the normalised inner planks -/

/-- **Attaching a shading to a plank.**  The inner family of Proposition 6.6(B) is a family of
*shaded* planks: the plank comes from the normalisation and the shading is the image of the fine
tube's shading. -/
def attachShade {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1} (P : Plank a' b' ha'b' hb'1)
    (shade : Set (EuclideanSpace ℝ (Fin 3))) (hmeas : MeasurableSet shade)
    (hsub : shade ⊆ (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    ShadedPlank a' b' ha'b' hb'1 where
  toPrism3D := P
  shade := shade
  measurableSet_shade := hmeas
  shade_subset := hsub

@[simp] theorem attachShade_toPrism3D {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
    (P : Plank a' b' ha'b' hb'1) (shade : Set (EuclideanSpace ℝ (Fin 3)))
    (hmeas : MeasurableSet shade)
    (hsub : shade ⊆ (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    (attachShade P shade hmeas hsub).toPrism3D = P := rfl

@[simp] theorem attachShade_shade {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
    (P : Plank a' b' ha'b' hb'1) (shade : Set (EuclideanSpace ℝ (Fin 3)))
    (hmeas : MeasurableSet shade)
    (hsub : shade ⊆ (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    (attachShade P shade hmeas hsub).shade = shade := rfl

/-- **Fullness transfer to the normalised inner family** (`lem:geometryAffineShadingTransfer`,
shading half).

If each inner plank carries the image of its fine tube's shading and contains the image of the whole
tube, the fine family's fullness is at most `8 / (κ³ c₃)` times the inner family's: the shading
volumes agree up to the Jacobian `J`, and the carrier volumes are compared by
`Plank.volume_normalisedPlank_le`. -/
theorem fullness_le_of_shade_image {ι : Type*} (s : Finset ι) {a b δ : ℝ≥0} {hab : a ≤ b}
    {hb1 : b ≤ 1} (ha : 0 < a) (hδ0 : 0 < δ) (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ} (hκ : 0 < κ)
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : Plank.IsPlankNormalisation W f κ g) {J : ℝ≥0}
    (hvolf : ∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    {ha'b' : δ / b ≤ δ / a} {hb'1 : δ / a ≤ 1}
    (P : ι → ShadedPlank (δ / b) (δ / a) ha'b' hb'1)
    (hshade : ∀ i ∈ s, ((P i).shade : Set (EuclideanSpace ℝ (Fin 3)))
      = f '' ((T i).shade : Set (EuclideanSpace ℝ (Fin 3))))
    (hsub : ∀ i ∈ s, f '' ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    ShadedBody.fullness s (fun i => (T i).toShadedBody)
      ≤ (8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3) : ℝ≥0)
        * ShadedBody.fullness s (fun i => (P i).toShadedBody) := by
  classical
  have _image_subset : ∀ i ∈ s,
      f '' ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))) := hsub
  let Cnn : ℝ≥0 := 8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3)
  let c : ENNReal := (Cnn : ENNReal)
  let j : ENNReal := (J : ENNReal)
  let A : ENNReal := ∑ i ∈ s, volume (T i).shade
  let B : ENNReal := ∑ i ∈ s, volume (T i).carrier
  let A' : ENNReal := ∑ i ∈ s, volume (P i).shade
  let B' : ENNReal := ∑ i ∈ s, volume (P i).carrier
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hJeq : J * (a * b) = Real.toNNReal κ ^ 3 :=
    Plank.jacobian_eq ha W hκ hnorm hvolf
  have hden : 0 < Real.toNNReal κ ^ 3 * Tube.le_volume.c 3 := by
    exact mul_pos (pow_pos (Real.toNNReal_pos.mpr hκ) 3) (Tube.le_volume.c_pos 3)
  have hCnn : 0 < Cnn := by
    apply NNReal.coe_pos.mp
    rw [NNReal.coe_div]
    exact div_pos (by norm_num) (NNReal.coe_pos.mpr hden)
  have hc0 : c ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt hCnn)
  have hcT : c ≠ ⊤ := ENNReal.coe_ne_top
  have hJnn0 : J ≠ 0 := by
    intro hJz
    have hκ3 : (Real.toNNReal κ ^ 3 : ℝ≥0) ≠ 0 := by
      exact pow_ne_zero 3 (ne_of_gt (Real.toNNReal_pos.mpr hκ))
    have hz : J * (a * b) = 0 := by simp [hJz]
    rw [hz] at hJeq
    exact (hκ3 hJeq.symm).elim
  have hj0 : j ≠ 0 := by
    simpa [j] using (ENNReal.coe_ne_zero).mpr hJnn0
  have hjT : j ≠ ⊤ := ENNReal.coe_ne_top
  have hcj0 : c * j ≠ 0 := mul_ne_zero hc0 hj0
  have hcjT : c * j ≠ ⊤ := ENNReal.mul_ne_top hcT hjT
  -- the shading volumes agree up to the Jacobian
  have hterm (i : ι) (hi : i ∈ s) :
      volume (P i).shade = j * volume (T i).shade := by
    rw [hshade i hi, hvolf]
  have hA' : A' = j * A := by
    calc
      A' = ∑ i ∈ s, volume (P i).shade := rfl
      _ = ∑ i ∈ s, j * volume (T i).shade := by
        exact Finset.sum_congr rfl (fun i hi => hterm i hi)
      _ = j * A := by
        dsimp [A]
        rw [Finset.mul_sum]
  -- the carrier volumes are compared by volume_normalisedPlank_le
  have htermB (i : ι) (hi : i ∈ s) :
      volume (P i).carrier ≤ c * (j * volume (T i).carrier) := by
    have hle := Plank.volume_normalisedPlank_le ha hb hδ0 hκ
        (P i).toPrism3D (T i).toTube hJeq
    simpa [c, j] using hle
  have hB' : B' ≤ c * j * B := by
    calc
      B' ≤ ∑ i ∈ s, c * (j * volume (T i).carrier) := by
        dsimp [B']
        exact Finset.sum_le_sum (fun i hi => by simpa using htermB i hi)
      _ = c * j * B := by
        calc
          (∑ i ∈ s, c * (j * volume (T i).carrier))
              = ∑ i ∈ s, (c * j) * volume (T i).carrier := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [mul_assoc]
          _ = (c * j) * (∑ i ∈ s, volume (T i).carrier) := by
            rw [← Finset.mul_sum]
          _ = c * j * B := by rfl
  have hmain : A / B ≤ c * (A' / B') := by
    calc
      A / B = (c * j) * A / ((c * j) * B) :=
        (ENNReal.mul_div_mul_left A B hcj0 hcjT).symm
      _ = (c * A') / ((c * j) * B) := by
        have hnum : (c * j) * A = c * A' := by
          calc (c * j) * A = c * (j * A) := by rw [mul_assoc]
            _ = c * A' := by rw [← hA']
        rw [hnum]
      _ ≤ (c * A') / B' := ENNReal.div_le_div_left hB' (c * A')
      _ = c * (A' / B') := by
        calc
          (c * A') / B' = (c * A') * B'⁻¹ := by rw [div_eq_mul_inv]
          _ = c * (A' * B'⁻¹) := mul_assoc c A' B'⁻¹
          _ = c * (A' / B') := by rw [div_eq_mul_inv]
  change ShadedBody.fullness s (fun i => (T i).toShadedBody) ≤
    Cnn * ShadedBody.fullness s (fun i => (P i).toShadedBody)
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul]
  rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness]
  have hTfull : ShadedBody.fullness' s (fun i => (T i).toShadedBody) = A / B := by
    dsimp [ShadedBody.fullness', A, B]
  have hPfull : ShadedBody.fullness' s (fun i => (P i).toShadedBody) = A' / B' := by
    dsimp [ShadedBody.fullness', A', B']
  rw [hTfull, hPfull]
  simpa [c] using hmain

/-! ### The normalised inner family -/

/-- **The normalised inner family of GWZ Proposition 6.6(B).**

From a family of fine `δ`-tubes inside an `a × b × 1` plank `W` and an affine normalisation `f` of
`W` onto the unit window (`Plank.IsPlankNormalisation`, constant Jacobian `J`, as produced by
`Plank.factorNormalisingAffineEquiv`), this produces the inner family of *shaded* planks at the
exact scales `a' = δ/b`, `b' = δ/a` with

* `0 < a'`, `δ ≤ a'`, `a' ≤ a₀`, `b' ≤ b₀ᵢ` (the last two from the smallness hypotheses on `δ`);
* the exact eccentricity identity `a'/b' = a/b`, in `ℝ≥0` and in `ℝ≥0∞`;
* windowing in `closedBall 0 plankWindowRadius`;
* the fullness transfer `λ(𝒯, Y) ≤ Cnorm · λ(inner)`;
* the maximal density transfer `Δ_max(inner) ≤ Cnorm · Δ_max(𝒯)`;
* the **wide-slab pullback link**: if the inner plank of `i` lies in a wide slab `S`, then the fine
  tube `T i` lies in `f⁻¹(S)`.

The last item is the interface of the `γ = 1` count: combined with `Kakeya.CoarseParentSystem` and a
coarse container for `S` it yields, through `Kakeya.card_le_of_frostmanIn` and
`Kakeya.card_le_of_comparable_fibres_of_selected_le`, the slab non-concentration bound
`|{i : P i ⊆ S}| ≤ Cfib² · C_F · Cvol · φ · |q|`.

Two clauses of the inner block of `Kakeya.factoringAndMultPropGlobal` are deliberately *absent*
here, because the exact normalisation does not produce them: pairwise essential distinctness of the
inner family (which needs the dyadic-plus-conflict-graph extraction of an essentially distinct
subfamily at a fixed loss, not the pointwise normalisation), and a *constant-free* maximal density
transfer (the inner plank has volume `8 δ²/(ab)` while the image of the tube it contains has volume
`≈ κ³ δ²/(ab)`, so a constant is forced). -/
theorem innerShadedPlankFamily (κ : ℝ) (hκ : 0 < κ) :
    ∃ Cnorm : ℝ≥0, 1 ≤ Cnorm ∧
      ∀ {ι : Type*} {a b δ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a) (hδ0 : 0 < δ)
        (hδa : δ ≤ a) (a₀ b₀ᵢ : ℝ≥0) (hsmalla : δ ≤ a₀ * b) (hsmallb : δ ≤ b₀ᵢ * a)
        (W : Plank a b hab hb1) (q : Finset ι)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0)
        (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))),
        0 < J →
        Plank.IsPlankNormalisation W f κ g →
        (∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E) →
        f '' (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 1 →
        (∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
          ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1)
            (Pj : ι → ShadedPlank a' b' ha'b' hb'1),
            a' = δ / b ∧ b' = δ / a ∧
            0 < a' ∧ δ ≤ a' ∧ a' ≤ a₀ ∧ b' ≤ b₀ᵢ ∧
            a' / b' = a / b ∧
            ((a' : ENNReal) / (b' : ENNReal) = (a : ENNReal) / (b : ENNReal)) ∧
            (∀ i ∈ q, ((Pj i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
              ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
            ShadedBody.fullness q (fun i => (T i).toShadedBody)
              ≤ Cnorm * ShadedBody.fullness q (fun i => (Pj i).toShadedBody) ∧
            maxDensity q (fun i => (Pj i).toConvexSpaceBody)
              ≤ (Cnorm : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) ∧
            (∀ (φ Rw : ℝ≥0) (hφR : φ ≤ Rw) (S : Prism3D φ Rw Rw hφR le_rfl) (i : ι),
                i ∈ Plank.inWideSlabFamily q (fun i => (Pj i).toPrism3D) S →
                ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
                  ⊆ f ⁻¹' (S.carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
            (∀ i ∈ q, ((Pj i).shade : Set (EuclideanSpace ℝ (Fin 3)))
                = f '' ((T i).shade : Set (EuclideanSpace ℝ (Fin 3)))) ∧
            (∀ i ∈ q, f '' ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
                ⊆ ((Pj i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
            (∀ i ∈ q, (Pj i).basis 2
                = (‖f (T i).y - f (T i).x‖)⁻¹ • (f (T i).y - f (T i).x)) ∧
            (∀ i ∈ q, (inner ℝ ((Pj i).basis 0) (g 0) : ℝ) = 0) := by
  classical
  let ccl : ℝ≥0 := 8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3)
  let Cnorm : ℝ≥0 := max 1 ccl
  refine ⟨Cnorm, le_max_left _ _, ?_⟩
  intro ι a b δ hab hb1 ha hδ0 hδa a₀ b₀ᵢ hsmalla hsmallb W q T f J g hJ hnorm hvolf himg hcarrier
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hb0R : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb0
  have ha0R : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hκ3 : 3 * κ ^ 2 ≤ 1 := by
    exact Plank.three_mul_sq_le_one_of_image_subset_closedBall ha W hκ hnorm himg
  have ha'b' : δ / b ≤ δ / a := by
    rw [← NNReal.coe_le_coe]
    rw [NNReal.coe_div, NNReal.coe_div]
    exact div_le_div_of_nonneg_left (NNReal.coe_nonneg δ) ha0R (by exact_mod_cast hab)
  have hb'1 : δ / a ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    rw [NNReal.coe_div]
    have hδaR : (δ : ℝ) ≤ (a : ℝ) := by exact_mod_cast hδa
    rw [div_le_iff₀ ha0R]
    simpa using hδaR
  have hδpos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδpos_a' : 0 < δ / b := by
    rw [← NNReal.coe_pos]
    rw [NNReal.coe_div]
    exact div_pos hδpos hb0R
  have hδ_le_a' : δ ≤ δ / b := by
    rw [← NNReal.coe_le_coe]
    rw [NNReal.coe_div]
    have hb1R : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
    have hδR0' : (0 : ℝ) ≤ (δ : ℝ) := le_of_lt hδpos
    rw [le_div_iff₀ hb0R]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_right hb1R hδR0')
  have ha'_le_a0 : δ / b ≤ a₀ := by
    rw [← NNReal.coe_le_coe]
    rw [NNReal.coe_div]
    have hδsR : (δ : ℝ) ≤ (a₀ : ℝ) * (b : ℝ) := by exact_mod_cast hsmalla
    exact (div_le_iff₀ hb0R).mpr hδsR
  have hb'_le_b0 : δ / a ≤ b₀ᵢ := by
    rw [← NNReal.coe_le_coe]
    rw [NNReal.coe_div]
    have hδsR : (δ : ℝ) ≤ (b₀ᵢ : ℝ) * (a : ℝ) := by exact_mod_cast hsmallb
    exact (div_le_iff₀ ha0R).mpr hδsR
  have hratio_nn : (δ / b) / (δ / a) = a / b := by
    apply NNReal.coe_injective
    simp [NNReal.coe_div]
    field_simp [show (δ : ℝ) ≠ 0 from (by exact_mod_cast hδ0.ne'),
      show (a : ℝ) ≠ 0 from ne_of_gt ha0R,
      show (b : ℝ) ≠ 0 from ne_of_gt hb0R]
  have hδa_pos : 0 < δ / a := by
    rw [← NNReal.coe_pos]
    rw [NNReal.coe_div]
    exact div_pos hδpos ha0R
  have hδa_ne : δ / a ≠ 0 := ne_of_gt hδa_pos
  have hb_ne : (b : NNReal) ≠ 0 := ne_of_gt hb0
  have hratio_enn : ((δ / b : NNReal) : ENNReal) / ((δ / a : NNReal) : ENNReal)
      = (a : ENNReal) / (b : ENNReal) := by
    rw [← ENNReal.coe_div hδa_ne]
    rw [← ENNReal.coe_div hb_ne]
    exact congrArg (fun z : NNReal => (z : ENNReal)) hratio_nn
  obtain ⟨F, hF⟩ := Plank.exists_affineEquiv_of_isPlankNormalisation ha W hκ hnorm
  have hFim (A : Set (EuclideanSpace ℝ (Fin 3))) :
      (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' A
        = (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' A := by
    apply congrArg (fun m : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) => m '' A)
    funext x
    exact hF x
  have key : ∀ i : ι, ∃ P : ShadedPlank (δ / b) (δ / a) ha'b' hb'1,
      i ∈ q → ((f '' ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
                 ⊆ (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
               ((P.shade : Set (EuclideanSpace ℝ (Fin 3)))
                 = f '' ((T i).shade : Set (EuclideanSpace ℝ (Fin 3)))) ∧
               ((P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
               (P.basis 2
                 = (‖f (T i).y - f (T i).x‖)⁻¹ • (f (T i).y - f (T i).x)) ∧
               ((inner ℝ (P.basis 0) (g 0) : ℝ) = 0)) := by
    intro i
    by_cases hi : i ∈ q
    · obtain ⟨P, hortho, halign, hcont, hwin⟩ :=
        Plank.exists_normalisedTubePlank ha hδ0 hδa W hκ hκ3 hnorm himg
          ha'b' hb'1 (T i).toTube (hcarrier i hi)
      have hmeas : MeasurableSet (f '' ((T i).shade : Set (EuclideanSpace ℝ (Fin 3)))) := by
        have hae : MeasurableSet ((T i).toShadedBody.mapAffine F).shade :=
          ((T i).toShadedBody.mapAffine F).measurableSet_shade
        rw [ShadedBody.mapAffine_shade] at hae
        rw [hFim ((T i).shade)] at hae
        exact hae
      have hsubShade : f '' ((T i).shade : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
        exact (Set.image_mono (T i).shade_subset).trans hcont
      exact ⟨attachShade P (f '' ((T i).shade : Set (EuclideanSpace ℝ (Fin 3)))) hmeas hsubShade,
        fun hm => ⟨by simpa using hcont, by simpa, by simpa using hwin, by simpa using halign,
          by simpa using hortho⟩⟩
    · let P0 : Plank (δ / b) (δ / a) ha'b' hb'1 :=
        { toPrismNDim := PrismNDim.mk' (0 : EuclideanSpace ℝ (Fin 3)) g ![δ / b, δ / a, (1 : NNReal)]
          thicknesses_eq := rfl }
      exact ⟨attachShade P0 ∅ MeasurableSet.empty (Set.empty_subset _), fun hm => absurd hm hi⟩
  choose Pj hPj using key
  refine ⟨δ / b, δ / a, ha'b', hb'1, Pj, rfl, rfl, hδpos_a', hδ_le_a', ha'_le_a0, hb'_le_b0,
    hratio_nn, hratio_enn, ?window, ?full, ?max, ?pull, ?shade, ?carrier, ?align, ?ortho⟩
  · intro i hi
    exact (hPj i hi).2.2.1
  · calc
    ShadedBody.fullness q (fun i => (T i).toShadedBody)
       ≤ ccl * ShadedBody.fullness q (fun i => (Pj i).toShadedBody) := by
          exact fullness_le_of_shade_image q ha hδ0 W hκ hnorm hvolf T Pj
            (fun i hi => (hPj i hi).2.1) (fun i hi => (hPj i hi).1)
    _ ≤ Cnorm * ShadedBody.fullness q (fun i => (Pj i).toShadedBody) := by
          gcongr
          exact le_max_right 1 ccl
  · have hmax : maxDensity q (fun i => (Pj i).toConvexSpaceBody) ≤ (ccl : ENNReal) *
          maxDensity q (fun i => (T i).toConvexSpaceBody) := by
      simpa using (Plank.maxDensity_le_of_image_subset q ha hδ0 W hκ hnorm hvolf T
        (fun i => (Pj i).toPrism3D) (fun i hi => (hPj i hi).1))
    calc
      maxDensity q (fun i => (Pj i).toConvexSpaceBody)
          ≤ (ccl : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) := hmax
      _ ≤ (Cnorm : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) := by
        gcongr
        exact le_max_right 1 ccl
  · intro φ Rw hφR S i hi
    rcases (Plank.mem_inWideSlabFamily.mp hi) with ⟨hiq, hPh, _⟩
    intro x hx
    rw [Set.mem_preimage]
    have hxP : f x ∈ (Pj i).carrier := (hPj i hiq).1 ⟨x, hx, rfl⟩
    exact hPh (by simpa [ShadedPlank.plank_carrier] using hxP)
  · intro i hi
    exact (hPj i hi).2.1
  · intro i hi
    exact (hPj i hi).1
  · intro i hi
    exact (hPj i hi).2.2.2.1
  · intro i hi
    exact (hPj i hi).2.2.2.2

/-! ### The `γ = 1` count -/

/-- The ratio of the two dimensional constants bounding the volume of a `ρ`-tube in `ℝ³`
(`Tube.le_volume`, `Tube.volume_le`).  It converts a Frostman volume ratio into a
count of coarse tubes. -/
def innerCoarseTubeVolumeRatio : ℝ≥0 := Tube.volume_le.C 3 / Tube.le_volume.c 3

/-- **Counting the coarse tubes inside a container** (the Frostman step of
`lem:factorInnerSlabNonconcentration`).

If the coarse `ρ`-tube family is `CF`-Frostman in `W` and `K ⊆ W` has volume at most
`Cvol · φ · |W|`, then at most `innerCoarseTubeVolumeRatio · CF · Cvol · φ · |r|` coarse tubes lie in `K`.

`Kakeya.card_le_of_frostmanIn` gives the volume-weighted form; the two-sided tube volume bounds
`Tube.le_volume` and `Tube.volume_le` turn the weights into the absolute ratio
`innerCoarseTubeVolumeRatio`. -/
theorem card_parents_le_of_container {ιr : Type*} [DecidableEq ιr] {r : Finset ιr} {ρ : ℝ≥0}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (R : ιr → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a) (W : Plank a b hab hb1)
    {CF : ℝ≥0}
    (hfrost : IsFrostmanIn r (fun k => (R k).toConvexSpaceBody) W.toConvexSpaceBody (CF : ENNReal))
    (hRW : ∀ k ∈ r, (R k).toConvexSpaceBody ≤ W.toConvexSpaceBody)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (hKW : K ≤ W.toConvexSpaceBody)
    {Cvol φ : ℝ≥0}
    (hvolK : volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ (Cvol : ENNReal) * (φ : ENNReal)
        * volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    (({k ∈ r | (R k).toConvexSpaceBody ≤ K}).card : ℝ≥0)
      ≤ innerCoarseTubeVolumeRatio * CF * Cvol * φ * (r.card : ℝ≥0) := by
  classical
  let v : ENNReal := ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (ρ : ENNReal) ^ 2
  let θ : ℝ≥0 := Cvol * φ
  have hv0 : v ≠ 0 := by
    dsimp [v]
    refine mul_ne_zero ?_ ?_
    · exact ENNReal.coe_ne_zero.mpr (ne_of_gt (Tube.le_volume.c_pos 3))
    · exact pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr (ne_of_gt hρ0))
  have hvtop : v ≠ ⊤ := by
    dsimp [v]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hvmin : ∀ k ∈ r, v ≤ volume ((R k).toConvexSpaceBody).carrier := by
    intro k hk
    simpa [v, finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)] using
      (Tube.le_volume (E := EuclideanSpace ℝ (Fin 3)) (R k))
  have hmax : ∀ k ∈ r, volume ((R k).toConvexSpaceBody).carrier ≤
      (innerCoarseTubeVolumeRatio : ENNReal) * v := by
    intro k hk
    have hle : volume (R k).carrier ≤ ((Tube.volume_le.C 3 * ρ ^ 2 : ℝ≥0) : ENNReal) := by
      simpa [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)] using
        (Tube.volume_le (E := EuclideanSpace ℝ (Fin 3)) hρ1 (R k))
    have hc : Tube.le_volume.c 3 ≠ (0 : ℝ≥0) := ne_of_gt (Tube.le_volume.c_pos 3)
    have hul : innerCoarseTubeVolumeRatio * (Tube.le_volume.c 3 * ρ ^ 2) =
        Tube.volume_le.C 3 * ρ ^ 2 := by
      rw [innerCoarseTubeVolumeRatio, ← mul_assoc]
      rw [div_mul_cancel₀ (Tube.volume_le.C 3) hc]
    have hcoef : (innerCoarseTubeVolumeRatio : ENNReal) * v =
        ((Tube.volume_le.C 3 * ρ ^ 2 : ℝ≥0) : ENNReal) := by
      dsimp [v]
      rw [← ENNReal.coe_pow, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
      exact congrArg (fun z : ℝ≥0 => (z : ENNReal)) hul
    calc
      volume ((R k).toConvexSpaceBody).carrier ≤
          ((Tube.volume_le.C 3 * ρ ^ 2 : ℝ≥0) : ENNReal) := hle
      _ = (innerCoarseTubeVolumeRatio : ENNReal) * v := by
        rw [hcoef]
  have hW0 : volume (W.toConvexSpaceBody).carrier ≠ 0 := by
    exact ne_of_gt (Prism3D.volume_pos_of_pos W ha)
  have hWtop : volume (W.toConvexSpaceBody).carrier ≠ ⊤ := by
    rw [Prism3D.volume_carrier W]
    have h8 : (8 : ENNReal) ≠ ⊤ := by norm_num
    have h1 : (1 : ENNReal) ≠ ⊤ := by norm_num
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top h8 ENNReal.coe_ne_top)
      ENNReal.coe_ne_top) h1
  have hvolb : volume (K.carrier : Set _) / volume (W.toConvexSpaceBody).carrier ≤
      (θ : ENNReal) := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl hW0) (Or.inl hWtop)]
    simpa [θ, ENNReal.coe_mul, mul_assoc] using hvolK
  have hmain : (({k ∈ r | (R k).toConvexSpaceBody ≤ K}).card : ENNReal) * v
      ≤ (CF : ENNReal) * ((r.card : ENNReal) * ((innerCoarseTubeVolumeRatio : ENNReal) * v))
        * (volume (K.carrier : Set _) / volume (W.toConvexSpaceBody).carrier) := by
    exact card_le_of_frostmanIn hfrost hRW hKW hv0 hvmin hmax hW0 hWtop
  have hstep : (CF : ENNReal) * ((r.card : ENNReal) * ((innerCoarseTubeVolumeRatio : ENNReal) * v))
      * (volume (K.carrier : Set _) / volume (W.toConvexSpaceBody).carrier)
      ≤ ((innerCoarseTubeVolumeRatio * CF * θ : ℝ≥0) : ENNReal) * (r.card : ENNReal) * v := by
    calc
      (CF : ENNReal) * ((r.card : ENNReal) * ((innerCoarseTubeVolumeRatio : ENNReal) * v))
          * (volume (K.carrier : Set _) / volume (W.toConvexSpaceBody).carrier)
          ≤ (CF : ENNReal) * ((r.card : ENNReal) * ((innerCoarseTubeVolumeRatio : ENNReal) * v))
              * (θ : ENNReal) := by
            gcongr
      _ = ((innerCoarseTubeVolumeRatio * CF * θ : ℝ≥0) : ENNReal) * (r.card : ENNReal) * v := by
            simp [ENNReal.coe_mul, mul_assoc, mul_left_comm, mul_comm]
  have hleft : v * (({k ∈ r | (R k).toConvexSpaceBody ≤ K}).card : ENNReal)
      ≤ v * (((innerCoarseTubeVolumeRatio * CF * θ : ℝ≥0) : ENNReal) * (r.card : ENNReal)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (le_trans hmain hstep)
  have hcard : (({k ∈ r | (R k).toConvexSpaceBody ≤ K}).card : ENNReal)
      ≤ ((innerCoarseTubeVolumeRatio * CF * θ : ℝ≥0) : ENNReal) * (r.card : ENNReal) := by
    exact (ENNReal.mul_le_mul_iff_right hv0 hvtop).mp hleft
  simpa [θ, mul_assoc, mul_comm, mul_left_comm] using (ENNReal.coe_le_coe.mp hcard)

/-- **The `γ = 1` inner count** (blueprint `eq:factor-inner-slab-concentration-explicit`).

Any set `qS` of fine indices whose coarse parents all lie in a container `K ⊆ W` of volume at most
`Cvol · φ · |W|` satisfies `|qS| ≤ Cfib² · (ratio · CF · Cvol) · φ · |q|`.

This is `Kakeya.card_le_of_comparable_fibres_of_selected_le` — the counting core
`Kakeya.card_le_of_comparable_fibres` together with the fibre normalisation — fed with the Frostman
coarse count `Kakeya.card_parents_le_of_container`.  Every input comes from the explicit
`Kakeya.CoarseParentSystem`, so nothing is hidden in the consumer. -/
theorem card_leaves_le_of_container {ιq ιr : Type*} [DecidableEq ιq] [DecidableEq ιr]
    {q : Finset ιq} {r : Finset ιr} {δ ρ : ℝ≥0}
    (T : ιq → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (R : ιr → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a) (W : Plank a b hab hb1)
    {Cfib CF m : ℝ≥0} (data : CoarseParentSystem q r T R W Cfib CF m)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (hKW : K ≤ W.toConvexSpaceBody)
    {Cvol φ : ℝ≥0}
    (hvolK : volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ (Cvol : ENNReal) * (φ : ENNReal)
        * volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    {qS : Finset ιq} (hqS : qS ⊆ q)
    (hcompat : ∀ i ∈ qS, (R (data.assign i)).toConvexSpaceBody ≤ K) :
    (qS.card : ℝ≥0)
      ≤ Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol * φ) * (q.card : ℝ≥0) := by
  classical
  let sel : Finset ιr := {k ∈ r | (R k).toConvexSpaceBody ≤ K}
  let Cθ : ℝ≥0 := innerCoarseTubeVolumeRatio * CF * Cvol * φ
  have hsel : sel ⊆ r := by
    simp [sel]
  have hselcard : (sel.card : ℝ≥0) ≤ Cθ * (r.card : ℝ≥0) := by
    have h := Kakeya.card_parents_le_of_container hρ0 hρ1 R ha W
      data.frostman data.parent_le_plank K hKW hvolK
    simpa [sel, Cθ] using h
  have hmem : ∀ i ∈ qS, data.assign i ∈ sel := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨data.assign_mem i (hqS hi), hcompat i hi⟩
  exact card_le_of_comparable_fibres_of_selected_le
    (Cfib := Cfib) (m := m) (Cθ := Cθ) (proj := data.assign)
    (hCfib := data.one_le_Cfib) (hr := data.parents_nonempty)
    (hproj := data.assign_mem) (hlb := data.fibre_lower) (hub := data.fibre_upper)
    (sel := sel) (hsel := hsel) (hselcard := hselcard)
    (qS := qS) (hmem := hmem) hqS

/-- **The `γ = 1` inner family of GWZ Proposition 6.6(B), packaged.**

`Kakeya.innerShadedPlankFamily` plus `Kakeya.card_leaves_le_of_container`: the normalised inner
family of shaded planks at the exact scales `a' = δ/b`, `b' = δ/a`, together with the wide-slab
non-concentration bound in the **raw** form
`Cfib² · innerCoarseTubeVolumeRatio · CF · Cvol · φ · |q|`.

The coefficient is deliberately not absorbed into a power of `a'`.  The absorption threshold of
`Plank.exists_rpow_absorbs_constant` depends on the constant being absorbed, hence on `Cfib` and
`CF`; but Section 6.6(B) must fix its smallness threshold `s₀` before those exist, and as `δ → 0`
the admissible `Cfib, CF ≤ δ ^ (-η)` drive that threshold to `0`, so no fixed `s₀` could supply the
required `δ ≤ a₀ · b`.  The caller absorbs the raw coefficient into `δ ^ (-ηᵢ)` instead, where the
sub-polynomial bounds make it legitimate (`Kakeya.partB_finalize_selected_inner_bounds`).

`a₀` survives only as a pass-through: it is a plain input here, forwarded to
`Kakeya.innerShadedPlankFamily`, whose conclusion `a' ≤ a₀` is re-exported unchanged.

The coarse container is a hypothesis, not a conclusion: for every wide slab `S` there must be a
convex body `K ⊆ W` with `|K| ≤ Cvol · φ · |W|` containing the coarse parent of every fine tube that
pulls back into `S` (blueprint `eq:factor-coarse-container-compatibility`).  Fine-tube containment
alone does not give it. -/
theorem innerFamilySlabNonconcentration (κ : ℝ) (hκ : 0 < κ) (Cvol : ℝ≥0) :
    ∃ Cnorm : ℝ≥0, 1 ≤ Cnorm ∧
      ∀ {ιq ιr : Type*} [DecidableEq ιq] [DecidableEq ιr]
        {a b δ ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a) (hδ0 : 0 < δ) (hδa : δ ≤ a)
        (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (a₀ b₀ᵢ : ℝ≥0)
        (hsmalla : δ ≤ a₀ * b) (hsmallb : δ ≤ b₀ᵢ * a)
        (W : Plank a b hab hb1) (q : Finset ιq) (r : Finset ιr)
        (T : ιq → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (R : ιr → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF : ℝ≥0)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0)
        (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))),
        0 < J →
        Plank.IsPlankNormalisation W f κ g →
        (∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E) →
        f '' (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 1 →
        (∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        ∀ (data : CoarseParentSystem q r T R W Cfib CF m),
        (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab) (S : Prism3D φ Rslab Rslab hφR le_rfl),
            a / b ≤ φ → |(inner ℝ (S.basis 0) (g 0) : ℝ)| ≤ 2 * (φ : ℝ) →
            ∃ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)), K ≤ W.toConvexSpaceBody ∧
              volume (K.carrier : Set (EuclideanSpace ℝ (Fin 3)))
                ≤ (Cvol : ENNReal) * (φ : ENNReal)
                  * volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∧
              ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
                  ⊆ f ⁻¹' (S.carrier : Set (EuclideanSpace ℝ (Fin 3))) →
                (R (data.assign i)).toConvexSpaceBody ≤ K) →
          ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1)
            (Pj : ιq → ShadedPlank a' b' ha'b' hb'1),
            a' = δ / b ∧ b' = δ / a ∧
            0 < a' ∧ δ ≤ a' ∧ a' ≤ a₀ ∧ b' ≤ b₀ᵢ ∧
            a' / b' = a / b ∧
            ((a' : ENNReal) / (b' : ENNReal) = (a : ENNReal) / (b : ENNReal)) ∧
            (∀ i ∈ q, ((Pj i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
              ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
            ShadedBody.fullness q (fun i => (T i).toShadedBody)
              ≤ Cnorm * ShadedBody.fullness q (fun i => (Pj i).toShadedBody) ∧
            maxDensity q (fun i => (Pj i).toConvexSpaceBody)
              ≤ (Cnorm : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) ∧
            (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a' / b' ≤ φ →
                ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
                ((Plank.inWideSlabFamily q (fun i => (Pj i).toPrism3D) S).card : ℝ≥0)
                  ≤ Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol)
                      * φ ^ (1 : ℝ) * (q.card : ℝ≥0)) ∧
            (∀ i ∈ q, ((Pj i).shade : Set (EuclideanSpace ℝ (Fin 3)))
                = f '' ((T i).shade : Set (EuclideanSpace ℝ (Fin 3)))) ∧
            (∀ i ∈ q, f '' ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
                ⊆ ((Pj i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
            (∀ i ∈ q, (Pj i).basis 2
                = (‖f (T i).y - f (T i).x‖)⁻¹ • (f (T i).y - f (T i).x)) ∧
            (∀ i ∈ q, (inner ℝ ((Pj i).basis 0) (g 0) : ℝ) = 0) := by
  classical
  obtain ⟨Cnorm, hCnorm, hfam⟩ := innerShadedPlankFamily κ hκ
  refine ⟨Cnorm, hCnorm, ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ ha hd0 hda hr0 hr1 a₀ b0 hsmalla hsmallb W q r T R m Cfib CF f J g
    hJ hnorm
    hvolf himg hcarrier data hcont
  obtain ⟨a', b', ha'b', hb'1, Pj, ha'def, hb'def, ha'pos, hδa', ha'a0, hb'b0, hratioNN,
      hratioENN, hwindow, hfull, hmaxd, hpull, hshade, hcarrimg, halign, hortho⟩ :=
    hfam ha hd0 hda a₀ b0 hsmalla hsmallb W q T f J g hJ hnorm hvolf himg hcarrier
  refine ⟨a', b', ha'b', hb'1, Pj, ha'def, hb'def, ha'pos, hδa', ha'a0, hb'b0, hratioNN, hratioENN,
    hwindow, hfull, hmaxd, ?count, hshade, hcarrimg, halign, hortho⟩
  · intro φ hφR hφge
    intro Slab
    by_cases htang : |(inner ℝ (Slab.basis 0) (g 0) : ℝ)| ≤ 2 * (φ : ℝ)
    swap
    · -- A slab that is not tangent to `g 0` collects no plank at all, by
      -- `Kakeya.abs_inner_wideSlab_normal_le_of_nonempty` applied to the exported orthogonality
      -- `⟪(Pj i).basis 0, g 0⟫ = 0`, so the count is `0`.
      have hempty : Plank.inWideSlabFamily q (fun i => (Pj i).toPrism3D) Slab = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro i hi
        exact htang (abs_inner_wideSlab_normal_le_of_nonempty q
          (fun i => (Pj i).toPrism3D) (g.norm_eq_one 0) hortho Slab ⟨i, hi⟩)
      rw [hempty]
      simp
    let qS := Plank.inWideSlabFamily q (fun i => (Pj i).toPrism3D) Slab
    obtain ⟨K, hKW, hKvol, hcap⟩ := hcont φ hφR Slab (hratioNN ▸ hφge) htang
    have hqsub : qS ⊆ q := by
      exact Plank.inWideSlabFamily_subset (s := q) (V := fun i => (Pj i).toPrism3D) (Sφ := Slab)
    have hcompat : ∀ i ∈ qS, (R (data.assign i)).toConvexSpaceBody ≤ K := by
      intro i hi
      have hTi : (T i).carrier ⊆ f ⁻¹' (Slab.carrier) := hpull φ Rslab hφR Slab i hi
      have hiq : i ∈ q := hqsub hi
      exact hcap i hiq hTi
    have hcount : (qS.card : ℝ≥0)
        ≤ (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol * φ)) * (q.card : ℝ≥0) :=
      card_leaves_le_of_container T R ha W data hr0 hr1 K hKW hKvol hqsub hcompat
    calc
      (qS.card : ℝ≥0) ≤ (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol * φ)) * (q.card : ℝ≥0) :=
        hcount
      _ = Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol) * φ ^ (1 : ℝ) * (q.card : ℝ≥0) := by
        rw [NNReal.rpow_one]
        ring

/-- **The inner family, with the coarse container discharged.**

`Kakeya.innerFamilySlabNonconcentration` takes the coarse container as a hypothesis.  Under its two
guards that hypothesis is now a theorem, `Kakeya.exists_coarse_container_of_guards`, whose three
set-inclusion inputs are all fields of the `Kakeya.CoarseParentSystem`.  This wrapper performs that
substitution once, so Section 6.6(B) can call the inner pipeline with no container obligation.

The extra hypotheses over `Kakeya.innerFamilySlabNonconcentration` are exactly what the container
needs and what `Plank.factorNormalisingAffineEquiv` already returns: `ρ ≤ a`, the centred window
`‖f x - f W.center‖ ≤ 1` on `W`, and the Jacobian lower bound `cfac ≤ J · (a·b)`.

**Quantifier order, and why the slab count is left un-absorbed.**  `Cnorm` comes from
`Kakeya.innerShadedPlankFamily` and depends on `κ` alone, so it is bound before everything else.
The slab count is reported with its *raw* constant `Cfib² · innerCoarseTubeVolumeRatio · CF · Cvol`
rather than absorbed into a power of `a'`.

Absorbing it here would be wrong for Section 6.6(B).  The absorption threshold `a₀` of
`Plank.exists_rpow_absorbs_constant` depends on the constant being absorbed, hence on `Cfib` and
`CF`; but the caller must fix its smallness threshold `s₀` *before* those exist, and as `δ → 0` the
admissible `Cfib, CF ≤ δ^(-η)` drive `a₀ → 0`, so no fixed `s₀` can supply `δ ≤ a₀ · b`.  The
caller absorbs the raw constant into `δ ^ (-ηᵢ)` instead, where the sub-polynomial bounds on `Cfib`
and `CF` make it legitimate.  `Cvol` is exported for exactly that purpose. -/
theorem exists_inner_family_of_partB (κ : ℝ) (hκ : 0 < κ) (cfac : ℝ≥0) (hcfac : 0 < cfac) :
    ∃ Cnorm Cvol : ℝ≥0, 1 ≤ Cnorm ∧ 1 ≤ Cvol ∧
      ∀ {ιq ιr : Type*} [DecidableEq ιq] [DecidableEq ιr]
        {a b δ ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a) (hδ0 : 0 < δ) (hδa : δ ≤ a)
        (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hρa : ρ ≤ a) (a₀ b₀ᵢ : ℝ≥0)
        (hsmalla : δ ≤ a₀ * b) (hsmallb : δ ≤ b₀ᵢ * a)
        (W : Plank a b hab hb1) (q : Finset ιq) (r : Finset ιr)
        (T : ιq → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (R : ιr → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF : ℝ≥0)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0)
        (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))),
        0 < J →
        Plank.IsPlankNormalisation W f κ g →
        (∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E) →
        f '' (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 1 →
        (∀ x ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))), ‖f x - f W.center‖ ≤ 1) →
        cfac ≤ J * (a * b) →
        (∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        ∀ (data : CoarseParentSystem q r T R W Cfib CF m),
          ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1)
            (Pj : ιq → ShadedPlank a' b' ha'b' hb'1),
            a' = δ / b ∧ b' = δ / a ∧
            0 < a' ∧ δ ≤ a' ∧ a' ≤ a₀ ∧ b' ≤ b₀ᵢ ∧
            a' / b' = a / b ∧
            ((a' : ENNReal) / (b' : ENNReal) = (a : ENNReal) / (b : ENNReal)) ∧
            (∀ i ∈ q, ((Pj i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
              ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
            ShadedBody.fullness q (fun i => (T i).toShadedBody)
              ≤ Cnorm * ShadedBody.fullness q (fun i => (Pj i).toShadedBody) ∧
            maxDensity q (fun i => (Pj i).toConvexSpaceBody)
              ≤ (Cnorm : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) ∧
            (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a' / b' ≤ φ →
                ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
                ((Plank.inWideSlabFamily q (fun i => (Pj i).toPrism3D) S).card : ℝ≥0)
                  ≤ Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol)
                      * φ ^ (1 : ℝ) * (q.card : ℝ≥0)) ∧
            (∀ i ∈ q, ((Pj i).shade : Set (EuclideanSpace ℝ (Fin 3)))
                = f '' ((T i).shade : Set (EuclideanSpace ℝ (Fin 3)))) ∧
            (∀ i ∈ q, f '' ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
                ⊆ ((Pj i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
            (∀ i ∈ q, (Pj i).basis 2
                = (‖f (T i).y - f (T i).x‖)⁻¹ • (f (T i).y - f (T i).x)) ∧
            (∀ i ∈ q, (inner ℝ ((Pj i).basis 0) (g 0) : ℝ) = 0) := by
  classical
  obtain ⟨Cvol, hCvol, hcontainer⟩ := exists_coarse_container_of_guards hκ cfac hcfac
  obtain ⟨Cnorm, hCnorm, hinner⟩ := innerFamilySlabNonconcentration κ hκ Cvol
  refine ⟨Cnorm, Cvol, hCnorm, hCvol, ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ ha hδ0 hδa hρ0 hρ1 hρa a₀ b₀ hsmalla hsmallb W q r T R m Cfib CF f J g
    hJ hnorm hvolf himg hWimg hJab hcarrier data
  refine hinner ha hδ0 hδa hρ0 hρ1 a₀ b₀ hsmalla hsmallb W q r T R m Cfib CF f J g hJ hnorm hvolf
    himg hcarrier data ?_
  intro φ hφR S hφab htang
  refine hcontainer ha hρa W q T R data.assign f J g hJ hnorm hvolf himg hWimg hJab hcarrier ?_ ?_ φ
    hφR S hφab htang
  · intro i hi
    exact SetLike.coe_subset_coe.mpr
      (data.parent_le_plank (data.assign i) (data.assign_mem i hi))
  · intro i hi
    exact SetLike.coe_subset_coe.mpr (data.leaf_le_parent i hi)

end Kakeya

end
