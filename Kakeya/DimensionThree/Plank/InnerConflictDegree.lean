/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.PlankOverlapGeometry
public import Kakeya.DimensionThree.Plank.TubePlankNormalisation
public import Kakeya.DimensionThree.Plank.EDDegree
public import Kakeya.DimensionThree.Plank.TubeParentPacking
public import Kakeya.Tube.EDPacking.DirectionCapCount
public import Kakeya.Tube.Nets

/-!
# The pullback container of a conflicting inner plank family

This module builds the *container* half of the inner-plank conflict-degree bound of Section 6(B).

The conflict degree to be bounded is `Kakeya.edConflictDegree q (fun j => (P j).carrier) i`, for the
normalised inner planks `P j` of scales `a' = δ/b`, `b' = δ/a`.  The bridge is that a plank
conflict forces its tube into one fixed set:

`¬ ED (P i) (P j)` → `P j ⊆ 11 · P i`  (`Kakeya.large_overlap_plank_subset_dilation`)
→ `f '' (T j).carrier ⊆ 11 · P i`
→ `(T j).carrier ⊆ f ⁻¹' (11 · P i) =: K i`.

`K i` is *not* a tube and must not be replaced by one: nothing here needs it to be a box, because
`Kakeya.exists_ED_directionCap_degree_bound` accepts an arbitrary compact measurable container.

## The volume bookkeeping

The dilation costs the fixed factor `11³`, and the plank itself has volume `8 a' b'`.  The
normalisation has constant Jacobian `J = κ³/(ab)` (`Plank.jacobian_eq`), so the preimage divides
by it, and the two anisotropies cancel exactly: `|K i| = 11³ · 8 · a' b' / J = (10648/κ³) · δ²`.

## What this module does not do

It supplies no direction cap.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

/-- The absolute volume constant of the inner pullback container, `11³ · 8 / κ³`. -/
def innerPullbackVolumeConst (κ : ℝ) : ℝ≥0 := 10648 / Real.toNNReal κ ^ 3

/-- Volume coefficient for the pullback of an `L`-dilated inner test plank. -/
def innerPullbackTestVolumeConst (κ : ℝ) (L : ℝ≥0) : ℝ≥0 :=
  8 * L ^ 3 / Real.toNNReal κ ^ 3

/-- **Preimage volume under an affine equivalence of constant Jacobian.**  If the forward map
multiplies every volume by `J`, the preimage divides by it. -/
theorem mul_volume_preimage_affineEquiv
    {F : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {J : ℝ≥0}
    (hvol : ∀ E : Set (EuclideanSpace ℝ (Fin 3)),
      volume ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E)
        = (J : ENNReal) * volume E)
    (S : Set (EuclideanSpace ℝ (Fin 3))) :
    (J : ENNReal) * volume ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S)
      = volume S := by
  rw [← hvol ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S)]
  rw [Set.image_preimage_eq S F.surjective]

/-- The pullback of a dilated three-dimensional prism has the expected volume.  This is the
variable-dilation form used by the inner non-concentration count; the older conflict-degree
argument is its specialization at dilation factor `11`. -/
theorem mul_volume_preimage_dilation_prism3D
    {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (P : Prism3D a b c hab hbc)
    {F : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {J L : ℝ≥0}
    (hvol : ∀ E : Set (EuclideanSpace ℝ (Fin 3)),
      volume ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E)
        = (J : ENNReal) * volume E) :
    (J : ENNReal) * volume
        ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹'
          ((P.toPrismNDim.dilation L).carrier : Set (EuclideanSpace ℝ (Fin 3)))) =
      (L : ENNReal) ^ 3 * volume P.carrier := by
  rw [mul_volume_preimage_affineEquiv hvol]
  exact P.toPrismNDim.volume_dilation L

/-- The preimage of a compact set under an affine equivalence of a finite-dimensional space is
compact: the map is a homeomorphism. -/
theorem isCompact_preimage_affineEquiv
    (F : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsCompact S) :
    IsCompact ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S) := by
  have hPre : ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S) =
      ((F.symm : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' S) :=
    (Equiv.image_symm_eq_preimage (F.toEquiv) S).symm
  rw [hPre]
  exact hS.image (AffineEquiv.continuous_of_finiteDimensional F.symm)

/-! ### Part A: the common pullback container -/

/-! ### Part B: the volume of the pullback container -/

/-- **Part B: the pullback container has volume `(10648/κ³) · δ²`, free of `a` and `b`.**
The inner plank has volume `8 a' b' = 8 δ²/(ab)`, the dilation multiplies by `11³`. -/
theorem volume_preimage_dilation_inner_plank
    {a b δ : ℝ≥0} (ha : 0 < a) (hb : 0 < b) {κ : ℝ} (hκ : 0 < κ)
    {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
    (ha'def : a' = δ / b) (hb'def : b' = δ / a)
    (Pi : Plank a' b' ha'b' hb'1)
    {F : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {J : ℝ≥0} (hJ : 0 < J)
    (hJab : J * (a * b) = Real.toNNReal κ ^ 3)
    (hvol : ∀ E : Set (EuclideanSpace ℝ (Fin 3)),
      volume ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E)
        = (J : ENNReal) * volume E) :
    volume ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹'
        ((Pi.toPrismNDim.dilation 11).carrier : Set (EuclideanSpace ℝ (Fin 3))))
      = (innerPullbackVolumeConst κ : ENNReal) * (δ : ENNReal) ^ 2 := by
  set S : Set (EuclideanSpace ℝ (Fin 3)) := (Pi.toPrismNDim.dilation 11).carrier with hS
  have h_true : volume S = (10648 : ℝ≥0) * (a' : ENNReal) * (b' : ENNReal) := by
    rw [hS]
    rw [Pi.toPrismNDim.volume_dilation (11 : NNReal)]
    rw [Prism3D.volume_carrier Pi]
    norm_num [pow_three]
    ring_nf
  have h_pre : (J : ENNReal) * volume
      ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S) = volume S := by
    exact mul_volume_preimage_affineEquiv hvol S
  have hA : J * (innerPullbackVolumeConst κ * δ ^ 2) = (10648 : ℝ≥0) * a' * b' := by
    unfold innerPullbackVolumeConst
    apply NNReal.coe_injective
    have hJab_r : (J : ℝ) * (a : ℝ) * (b : ℝ) = ((Real.toNNReal κ : ℝ)) ^ 3 := by
      have h1 := congrArg (fun q : ℝ≥0 => (q : ℝ)) hJab
      rw [NNReal.coe_mul] at h1
      rw [NNReal.coe_mul] at h1
      rw [NNReal.coe_pow] at h1
      simpa [mul_assoc] using h1
    have ha_r : (a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
    have hb_r : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
    have hJ_r : (J : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hJ)
    have hκn_r : ((Real.toNNReal κ) : ℝ) ≠ 0 := by
      exact (ne_of_gt (NNReal.coe_pos.mpr (Real.toNNReal_pos.mpr hκ)))
    rw [ha'def, hb'def]
    simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow, mul_comm]
    field_simp [hJ_r, ha_r, hb_r, hκn_r]
    rw [← hJab_r]
    ring
  have hA_en : (J : ENNReal) * ((innerPullbackVolumeConst κ : ENNReal) * (δ : ENNReal) ^ 2) =
      (10648 : ℝ≥0) * (a' : ENNReal) * (b' : ENNReal) := by
    exact_mod_cast hA
  have h_step2 : (J : ENNReal) * volume
        ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S) =
      (10648 : ℝ≥0) * (a' : ENNReal) * (b' : ENNReal) := by
    rw [h_pre, h_true]
  have hJ_ne : (J : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hJ)
  have hJ_top : (J : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hcommon : (J : ENNReal) * volume
        ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S) =
      (J : ENNReal) * ((innerPullbackVolumeConst κ : ENNReal) * (δ : ENNReal) ^ 2) := by
    rw [h_step2, ← hA_en]
  have hcommon2 : volume
        ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S) * (J : ENNReal) =
      (innerPullbackVolumeConst κ : ENNReal) * (δ : ENNReal) ^ 2 * (J : ENNReal) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcommon
  have hcancel := (ENNReal.mul_left_inj (c := (J : ENNReal)) hJ_ne hJ_top).mp hcommon2
  simpa [hS] using hcancel

/-- Exact pullback volume of the dilated `φ`-thickening of a normalised inner plank.

For inner widths `a' = δ/b`, `b' = δ/a`, the test plank has widths
`(φ b', b', 1)`.  Dividing its volume by the normalisation Jacobian gives
`C(κ,L) · φ · (b/a) · δ²`. -/
theorem volume_preimage_dilation_thickened_inner_plank
    {a b δ : ℝ≥0} (ha : 0 < a) (hb : 0 < b) {κ : ℝ} (hκ : 0 < κ)
    {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
    (ha'def : a' = δ / b) (hb'def : b' = δ / a)
    (P : Plank a' b' ha'b' hb'1) {φ : ℝ≥0} (hφ1 : φ ≤ 1) (L : ℝ≥0)
    {F : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {J : ℝ≥0} (hJ : 0 < J)
    (hJab : J * (a * b) = Real.toNNReal κ ^ 3)
    (hvol : ∀ E : Set (EuclideanSpace ℝ (Fin 3)),
      volume ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E)
        = (J : ENNReal) * volume E) :
    volume ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹'
        ((((Plank.thickened P φ hφ1).toPrismNDim).dilation L).carrier :
          Set (EuclideanSpace ℝ (Fin 3)))) =
      (innerPullbackTestVolumeConst κ L : ENNReal) * (φ : ENNReal) *
        ((b : ENNReal) / (a : ENNReal)) * (δ : ENNReal) ^ 2 := by
  let Q := Plank.thickened P φ hφ1
  let S : Set (EuclideanSpace ℝ (Fin 3)) := (Q.toPrismNDim.dilation L).carrier
  have hpre : (J : ENNReal) * volume
      ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S) = volume S :=
    mul_volume_preimage_affineEquiv hvol S
  have hSvol : volume S = (L : ENNReal) ^ 3 *
      (8 * ((φ * b' : ℝ≥0) : ENNReal) * (b' : ENNReal)) := by
    dsimp [S, Q]
    rw [(Plank.thickened P φ hφ1).toPrismNDim.volume_dilation L,
      Prism3D.volume_carrier (Plank.thickened P φ hφ1)]
    simp only [ENNReal.coe_mul, ENNReal.coe_one, mul_one]
  have htargetNN : J * (innerPullbackTestVolumeConst κ L * φ * (b / a) * δ ^ 2) =
      L ^ 3 * (8 * (φ * b') * b') := by
    unfold innerPullbackTestVolumeConst
    apply NNReal.coe_injective
    have hJabR : (J : ℝ) * (a : ℝ) * (b : ℝ) = ((Real.toNNReal κ : ℝ)) ^ 3 := by
      have h := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) hJab
      push_cast at h
      simpa [mul_assoc] using h
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
    have hκr : ((Real.toNNReal κ : ℝ)) ≠ 0 :=
      ne_of_gt (NNReal.coe_pos.mpr (Real.toNNReal_pos.mpr hκ))
    push_cast
    rw [hb'def]
    push_cast
    field_simp [haR, hbR, hJr, hκr]
    rw [← hJabR]
    ring
  have htarget : (J : ENNReal) *
      ((innerPullbackTestVolumeConst κ L : ENNReal) * (φ : ENNReal) *
        ((b : ENNReal) / (a : ENNReal)) * (δ : ENNReal) ^ 2) =
      (L : ENNReal) ^ 3 * (8 * ((φ * b' : ℝ≥0) : ENNReal) * (b' : ENNReal)) := by
    have hcast := congrArg (fun x : ℝ≥0 ↦ (x : ENNReal)) htargetNN
    simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_div ha.ne'] at hcast
    norm_num at hcast ⊢
    exact hcast
  have hJ0 : (J : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hJ.ne'
  have hJtop : (J : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hcommon : (J : ENNReal) * volume
        ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S) =
      (J : ENNReal) *
        ((innerPullbackTestVolumeConst κ L : ENNReal) * (φ : ENNReal) *
          ((b : ENNReal) / (a : ENNReal)) * (δ : ENNReal) ^ 2) := by
    calc
    (J : ENNReal) * volume
        ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S) =
        volume S := hpre
    _ = (L : ENNReal) ^ 3 *
        (8 * ((φ * b' : ℝ≥0) : ENNReal) * (b' : ENNReal)) := hSvol
    _ = (J : ENNReal) *
        ((innerPullbackTestVolumeConst κ L : ENNReal) * (φ : ENNReal) *
          ((b : ENNReal) / (a : ENNReal)) * (δ : ENNReal) ^ 2) := htarget.symm
  have hcommon' : volume
        ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹' S) * (J : ENNReal) =
      ((innerPullbackTestVolumeConst κ L : ENNReal) * (φ : ENNReal) *
          ((b : ENNReal) / (a : ENNReal)) * (δ : ENNReal) ^ 2) * (J : ENNReal) := by
    simpa [mul_comm] using hcommon
  have hcancel := (ENNReal.mul_left_inj (c := (J : ENNReal)) hJ0 hJtop).mp hcommon'
  simpa [S, Q] using hcancel

/-! ### Part C, algebraic core: the Cramer estimate -/

/-- The area of the parallelogram spanned by two vectors, as the square root of their Gram
determinant.  In the conflict-degree argument `q₀`, `q₁` are the pullback normals of the two thin
axes of the reference inner plank, and this is the quantity that the anisotropy of the normalisation
cancels against. -/
def pullbackArea (q₀ q₁ : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.sqrt (‖q₀‖ ^ 2 * ‖q₁‖ ^ 2 - (inner ℝ q₀ q₁ : ℝ) ^ 2)

/-- **The Cramer estimate.**  A vector in the plane spanned by `q₀`, `q₁` is controlled by its two
inner products against them, at the cost of dividing by the area they span.

This is the step that the triangle inequality cannot replace: bounding `‖v‖` by
`|⟪q₀,v⟫|·‖Πq₀‖ + |⟪q₁,v⟫|·‖Πq₁‖` loses a factor `b/a`, because the two pullback directions are
nearly parallel exactly when the normalisation is most anisotropic.  The proof is the Gram identity
`‖v‖² · G = ‖q₀‖²⟪q₁,v⟫² - 2⟪q₀,q₁⟫⟪q₀,v⟫⟪q₁,v⟫ + ‖q₁‖²⟪q₀,v⟫²`, which is `ring` once `v` is
expanded, followed by Cauchy-Schwarz on the cross term. -/
theorem norm_mul_pullbackArea_le {q₀ q₁ v : EuclideanSpace ℝ (Fin 3)} {x y : ℝ}
    (hv : v = x • q₀ + y • q₁) :
    ‖v‖ * pullbackArea q₀ q₁
      ≤ ‖q₀‖ * |(inner ℝ q₁ v : ℝ)| + ‖q₁‖ * |(inner ℝ q₀ v : ℝ)| := by
  let r₀ : ℝ := ‖q₀‖
  let r₁ : ℝ := ‖q₁‖
  let c : ℝ := inner ℝ q₀ q₁
  let A : ℝ := inner ℝ q₀ v
  let B : ℝ := inner ℝ q₁ v
  have hcs : |c| ≤ r₀ * r₁ := by
    dsimp [c, r₀, r₁]
    exact abs_real_inner_le_norm q₀ q₁
  have hA : A = x * r₀ ^ 2 + y * c := by
    dsimp [A, r₀, c]
    rw [hv]
    simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hB : B = x * c + y * r₁ ^ 2 := by
    dsimp [B, r₁, c]
    rw [hv]
    simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm q₀ q₁]
  have hnorm : ‖v‖ ^ 2 = x ^ 2 * r₀ ^ 2 + 2 * x * y * c + y ^ 2 * r₁ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp [r₀, r₁, c]
    rw [hv]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    simp only [real_inner_self_eq_norm_sq]
    rw [real_inner_comm q₀ q₁]
    ring
  let G : ℝ := r₀ ^ 2 * r₁ ^ 2 - c ^ 2
  have hG : 0 ≤ G := by
    dsimp [G]
    have hcsq : c ^ 2 ≤ (r₀ * r₁) ^ 2 := by
      have hR : 0 ≤ r₀ * r₁ := by
        dsimp [r₀, r₁]
        positivity
      have hcs' : |c| ≤ |r₀ * r₁| := by
        simpa [abs_of_nonneg hR] using hcs
      exact sq_le_sq.mpr hcs'
    have hring : (r₀ * r₁) ^ 2 = r₀ ^ 2 * r₁ ^ 2 := by ring
    nlinarith [hcsq, hring]
  have hgram : ‖v‖ ^ 2 * G = r₀ ^ 2 * B ^ 2 - 2 * c * A * B + r₁ ^ 2 * A ^ 2 := by
    dsimp [G]
    rw [hnorm, hA, hB]
    ring
  have hcross : -2 * c * A * B ≤ 2 * |c| * |A| * |B| := by
    have h1 : -(c * A * B) ≤ |c * A * B| := by
      simpa [abs_neg] using le_abs_self (-(c * A * B))
    have h2 : |c * A * B| = |c| * |A| * |B| := by
      rw [abs_mul, abs_mul]
    nlinarith
  have hcross2 : 2 * |c| * |A| * |B| ≤ 2 * r₀ * r₁ * |A| * |B| := by
    have hfac : 0 ≤ 2 * |A| * |B| := by positivity
    calc
      2 * |c| * |A| * |B| = 2 * |A| * |B| * |c| := by ring
      _ ≤ 2 * |A| * |B| * (r₀ * r₁) := by
        exact mul_le_mul_of_nonneg_left hcs hfac
      _ = 2 * r₀ * r₁ * |A| * |B| := by ring
  have hle : ‖v‖ ^ 2 * G ≤ (r₀ * |B| + r₁ * |A|) ^ 2 := by
    rw [hgram]
    rw [← sq_abs B, ← sq_abs A]
    nlinarith [hcross, hcross2]
  have hreal : (‖v‖ * Real.sqrt G) ^ 2 = ‖v‖ ^ 2 * G := by
    rw [mul_pow]
    rw [Real.sq_sqrt hG]
  have hsq : (‖v‖ * Real.sqrt G) ^ 2 ≤ (r₀ * |B| + r₁ * |A|) ^ 2 := by
    rw [hreal]
    exact hle
  unfold pullbackArea
  change ‖v‖ * Real.sqrt G ≤ r₀ * |B| + r₁ * |A|
  have hnn : 0 ≤ r₀ * |B| + r₁ * |A| := by
    nlinarith [norm_nonneg q₀, norm_nonneg q₁, abs_nonneg A, abs_nonneg B]
  nlinarith [hsq, norm_nonneg v, Real.sqrt_nonneg (r₀ ^ 2 * r₁ ^ 2 - c ^ 2), hnn]

/-- **The pullback normals of the two thin axes are orthogonal to the tube direction.**

This is where the long-axis alignment exported by `Plank.exists_normalisedTubePlank` is spent: the
inner plank's long axis `P.basis 2` is the normalised affine image of the tube's core direction, so
the other two axes pair to zero with it, and `Plank.inner_pullbackNormal_sub` transports that
orthogonality back through the normalisation.

Consequently `q₀`, `q₁` span the plane orthogonal to `T.direction`, which is what lets the Cramer
estimate be applied there. -/
theorem inner_direction_pullbackNormal_eq_zero
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : Plank.IsPlankNormalisation W f κ g)
    {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1} (P : Plank a' b' ha'b' hb'1)
    {δ : ℝ≥0} (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (halign : P.basis 2 = (‖f T.y - f T.x‖)⁻¹ • (f T.y - f T.x))
    {k : Fin 3} (hk : k ≠ 2) :
    (inner ℝ T.direction (Plank.pullbackNormal W κ g (P.basis k)) : ℝ) = 0 := by
  change (inner ℝ (T.y - T.x) (Plank.pullbackNormal W κ g (P.basis k)) : ℝ) = 0
  rw [← W.inner_pullbackNormal_sub hnorm (P.basis k) T.y T.x]
  let d : EuclideanSpace ℝ (Fin 3) := f T.y - f T.x
  change (inner ℝ d (P.basis k) : ℝ) = 0
  by_cases hd0 : ‖d‖ = 0
  · have hd0' : d = 0 := norm_eq_zero.mp hd0
    simp [hd0']
  · have hd : d = ‖d‖ • P.basis 2 := by
      calc
        d = ‖d‖ • ((‖d‖)⁻¹ • d) := by
          rw [smul_smul]
          rw [mul_inv_cancel₀ hd0]
          simp
        _ = ‖d‖ • P.basis 2 := by rw [← halign]
    rw [hd]
    simp only [real_inner_smul_left]
    rw [P.basis.inner_eq_ite]
    simp [Ne.symm hk]

/-- **The pullback normal is the adjoint of the linear part.**  Testing `L w` against `n` is the
same as testing `w` against `pullbackNormal n`.  This is `Plank.inner_pullbackNormal_sub` with the
second point at the origin. -/
theorem inner_linear_eq_inner_pullbackNormal
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : Plank.IsPlankNormalisation W f κ g)
    (n w : EuclideanSpace ℝ (Fin 3)) :
    (inner ℝ (f.linear w) n : ℝ) = inner ℝ w (Plank.pullbackNormal W κ g n) := by
  have h := Plank.inner_pullbackNormal_sub W hnorm n w 0
  have hL : f w - f 0 = f.linear w := by
    simpa [sub_zero] using (AffineMap.linearMap_vsub f w 0).symm
  simpa [hL] using h

/-- **Squared determinant invariance between orthonormal bases.**  Only the square is needed, so the
two `±1` change-of-basis signs disappear and no orientation bookkeeping is required. -/
theorem sq_det_toMatrix_orthonormalBasis
    (c p : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    (Matrix.det (LinearMap.toMatrix c.toBasis p.toBasis L)) ^ 2 = (LinearMap.det L) ^ 2 := by
  have hfac : LinearMap.toMatrix c.toBasis p.toBasis L
      = LinearMap.toMatrix p.toBasis p.toBasis L
        * LinearMap.toMatrix c.toBasis p.toBasis LinearMap.id := by
    rw [← LinearMap.toMatrix_comp c.toBasis p.toBasis p.toBasis L LinearMap.id, LinearMap.comp_id]
  rw [hfac, Matrix.det_mul, LinearMap.det_toMatrix, LinearMap.toMatrix_id_eq_basis_toMatrix]
  rw [OrthonormalBasis.coe_toBasis, ← Module.Basis.det_apply]
  rcases OrthonormalBasis.det_to_matrix_orthonormalBasis_real (a := p) (b := c) with h | h
  · rw [h]; ring
  · rw [h]; ring

/-- **The determinant of a plank normalisation.**  Its linear part is diagonal from `W.basis` to
`g` with entries `κ / W.thicknesses i`, so `(det L)² = (κ³/(ab))²`. -/
theorem sq_det_linear_eq
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : Plank.IsPlankNormalisation W f κ g) (ha : 0 < a) :
    (LinearMap.det f.linear) ^ 2 = (κ ^ 3 / ((a : ℝ) * (b : ℝ))) ^ 2 := by
  rw [← sq_det_toMatrix_orthonormalBasis W.basis g f.linear]
  -- The `(k, m)`-entry of the mixed matrix is the `g k`-coordinate of `f.linear (W.basis m)`,
  -- which by `Plank.inner_pullbackNormal_sub` is `κ / W.thicknesses m` on the diagonal and `0` off.
  have h_inner : ∀ m k : Fin 3,
      (inner ℝ (g k) (f.linear (W.basis m)) : ℝ)
        = if k = m then κ * ((W.thicknesses k : ℝ))⁻¹ else 0 := by
    intro m k
    rw [real_inner_comm]
    rw [inner_linear_eq_inner_pullbackNormal W hnorm (g k) (W.basis m)]
    dsimp [Plank.pullbackNormal]
    rw [inner_sum]
    simp_rw [real_inner_smul_right]
    by_cases hkm : k = m
    · subst m
      simp [W.basis.inner_eq_ite]
    · have hsum0 :
        (∑ i : Fin 3,
            κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ (g k) (g i)
              * inner ℝ (W.basis m) (W.basis i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        by_cases hik : i = k
        · subst i
          simp [W.basis.inner_eq_ite, Ne.symm hkm]
        · rw [g.inner_eq_ite]
          simp [Ne.symm hik]
      rw [hsum0]
      simp [hkm]
  have hM : LinearMap.toMatrix W.basis.toBasis g.toBasis f.linear =
      Matrix.diagonal (fun i : Fin 3 => κ * ((W.thicknesses i : ℝ))⁻¹) := by
    ext k m
    rw [LinearMap.toMatrix_apply]
    simpa [Matrix.diagonal, g.repr_apply_apply] using h_inner m k
  have hdet : Matrix.det (LinearMap.toMatrix W.basis.toBasis g.toBasis f.linear)
      = κ ^ 3 * ((a : ℝ) * (b : ℝ))⁻¹ := by
    rw [hM, Matrix.det_diagonal, Fin.prod_univ_three]
    rw [W.thicknesses_eq]
    simp
    field_simp [ne_of_gt ha, ne_of_gt (lt_of_lt_of_le ha hab)]
  rw [hdet, div_eq_mul_inv]

/-- **Part C1: the area identity.**  Choosing an orthonormal source frame whose last vector is `u`,
the `u`-column of the mixed matrix of `L` is `(0, 0, ‖L u‖)` by the exported long-axis alignment, so
the cofactor expansion leaves exactly the `2 × 2` minor whose square is the Gram determinant of
`q₀, q₁`. -/
theorem sq_pullbackArea_mul_sq_norm_linear_eq
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : Plank.IsPlankNormalisation W f κ g)
    {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1} (P : Plank a' b' ha'b' hb'1)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1)
    (halign : P.basis 2 = (‖f.linear u‖)⁻¹ • (f.linear u)) (hLu : f.linear u ≠ 0) :
    pullbackArea (Plank.pullbackNormal W κ g (P.basis 0))
        (Plank.pullbackNormal W κ g (P.basis 1)) ^ 2 * ‖f.linear u‖ ^ 2
      = (LinearMap.det f.linear) ^ 2 := by
  let q : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
    fun k => Plank.pullbackNormal W κ g (P.basis k)
  let N : ℝ := ‖f.linear u‖
  have hL_ne : ‖f.linear u‖ ≠ 0 := norm_ne_zero_iff.mpr hLu
  -- an orthonormal source frame whose last vector is `u`
  obtain ⟨n, hn, hnu, _⟩ := Plank.exists_unit_orthogonal_pair u u
  obtain ⟨c, hc0, hc2⟩ := Plank.exists_orthonormalBasis_fst_thd_eq hn hu hnu
  let M : Matrix (Fin 3) (Fin 3) ℝ := LinearMap.toMatrix c.toBasis P.basis.toBasis f.linear
  have hM_apply : ∀ k m : Fin 3, M k m = inner ℝ (c m) (q k) := by
    intro k m
    dsimp [M]
    rw [LinearMap.toMatrix_apply]
    rw [OrthonormalBasis.coe_toBasis_repr_apply]
    rw [P.basis.repr_apply_apply]
    calc
      inner ℝ (P.basis k) (f.linear (c.toBasis m))
          = inner ℝ (f.linear (c.toBasis m)) (P.basis k) := by
              exact real_inner_comm (f.linear (c.toBasis m)) (P.basis k)
      _ = inner ℝ (c.toBasis m) (Plank.pullbackNormal W κ g (P.basis k)) := by
              exact inner_linear_eq_inner_pullbackNormal W hnorm (P.basis k) (c.toBasis m)
      _ = inner ℝ (c m) (q k) := by
              simp [q]
  have hLuN : f.linear u = N • P.basis 2 := by
    calc
      f.linear u = ‖f.linear u‖ • ((‖f.linear u‖)⁻¹ • f.linear u) := by
        rw [smul_smul, mul_inv_cancel₀ hL_ne, one_smul]
      _ = N • P.basis 2 := by
        dsimp [N]
        rw [halign]
  have hq_orth : ∀ k : Fin 3, k ≠ 2 → inner ℝ u (q k) = 0 := by
    intro k hk
    have h := (inner_linear_eq_inner_pullbackNormal W hnorm (P.basis k) u).symm
    rw [h]
    rw [hLuN]
    simp only [real_inner_smul_left]
    rw [P.basis.inner_eq_ite]
    simp [Ne.symm hk]
  have hqu2 : inner ℝ u (q 2) = N := by
    have h := (inner_linear_eq_inner_pullbackNormal W hnorm (P.basis 2) u).symm
    rw [h]
    rw [hLuN]
    simp only [real_inner_smul_left]
    simp
  have hM02 : M 0 2 = 0 := by
    rw [hM_apply 0 2, hc2, hq_orth 0 (by decide)]
  have hM12 : M 1 2 = 0 := by
    rw [hM_apply 1 2, hc2, hq_orth 1 (by decide)]
  have hM22 : M 2 2 = N := by
    rw [hM_apply 2 2, hc2, hqu2]
  have hq0c2 : inner ℝ (c 2) (q 0) = 0 := by
    rw [hc2]
    exact hq_orth 0 (by decide)
  have hq1c2 : inner ℝ (c 2) (q 1) = 0 := by
    rw [hc2]
    exact hq_orth 1 (by decide)
  let a0 : ℝ := inner ℝ (c 0) (q 0)
  let a1 : ℝ := inner ℝ (c 1) (q 0)
  let b0 : ℝ := inner ℝ (c 0) (q 1)
  let b1 : ℝ := inner ℝ (c 1) (q 1)
  let D : ℝ := M 0 0 * M 1 1 - M 0 1 * M 1 0
  have hM00 : M 0 0 = a0 := by simpa [a0] using hM_apply 0 0
  have hM01 : M 0 1 = a1 := by simpa [a1] using hM_apply 0 1
  have hM10 : M 1 0 = b0 := by simpa [b0] using hM_apply 1 0
  have hM11 : M 1 1 = b1 := by simpa [b1] using hM_apply 1 1
  have hQR0 : ‖q 0‖ ^ 2 = a0 ^ 2 + a1 ^ 2 := by
    dsimp [a0, a1]
    rw [← c.sum_sq_inner_right (q 0)]
    rw [Fin.sum_univ_three, hq0c2]
    norm_num
  have hQR1 : ‖q 1‖ ^ 2 = b0 ^ 2 + b1 ^ 2 := by
    dsimp [b0, b1]
    rw [← c.sum_sq_inner_right (q 1)]
    rw [Fin.sum_univ_three, hq1c2]
    norm_num
  have hQI : inner ℝ (q 0) (q 1) = a0 * b0 + a1 * b1 := by
    dsimp [a0, a1, b0, b1]
    rw [← c.sum_inner_mul_inner (q 0) (q 1)]
    rw [Fin.sum_univ_three]
    have hq0c2' : inner ℝ (q 0) (c 2) = 0 := by
      rw [hc2]
      have hq0u_comm : inner ℝ (q 0) u = inner ℝ u (q 0) :=
        real_inner_comm u (q 0)
      rw [hq0u_comm]
      exact hq_orth 0 (by decide)
    rw [hq0c2']
    rw [real_inner_comm (q 0) (c 0), real_inner_comm (q 0) (c 1)]
    simp [hq1c2]
  have hGram : ‖q 0‖ ^ 2 * ‖q 1‖ ^ 2 - (inner ℝ (q 0) (q 1)) ^ 2 = D ^ 2 := by
    rw [hQR0, hQR1, hQI]
    dsimp [D]
    rw [hM00, hM11, hM01, hM10]
    ring
  have hG_nonneg : 0 ≤ ‖q 0‖ ^ 2 * ‖q 1‖ ^ 2 - (inner ℝ (q 0) (q 1)) ^ 2 := by
    rw [hGram]
    exact sq_nonneg D
  have hPA : pullbackArea (q 0) (q 1) ^ 2 = D ^ 2 := by
    unfold pullbackArea
    rw [hGram]
    rw [Real.sq_sqrt (sq_nonneg D)]
  have hdetM : Matrix.det M = N * D := by
    dsimp [D]
    rw [Matrix.det_fin_three M, hM02, hM12, hM22]
    ring
  have htarget : D ^ 2 * ‖f.linear u‖ ^ 2 = (Matrix.det M) ^ 2 := by
    rw [show ‖f.linear u‖ = N by rfl]
    rw [hdetM]
    ring
  have h1 : pullbackArea (q 0) (q 1) ^ 2 * ‖f.linear u‖ ^ 2 = (Matrix.det M) ^ 2 := by
    rw [hPA]
    exact htarget
  have hdet : (Matrix.det M) ^ 2 = (LinearMap.det f.linear) ^ 2 := by
    dsimp [M]
    exact sq_det_toMatrix_orthonormalBasis c P.basis f.linear
  change pullbackArea (q 0) (q 1) ^ 2 * ‖f.linear u‖ ^ 2 = (LinearMap.det f.linear) ^ 2
  rw [h1]
  exact hdet

/-- The image of a unit vector lying in the plank's own frame box has norm at most `4κ`. -/
theorem norm_linear_le_of_coord_bounds
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ} (hκ : 0 < κ)
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : Plank.IsPlankNormalisation W f κ g) (ha : 0 < a)
    {w : EuclideanSpace ℝ (Fin 3)}
    (hw : ∀ i : Fin 3, |(inner ℝ w (W.basis i) : ℝ)| ≤ 2 * (W.thicknesses i : ℝ)) :
    ‖f.linear w‖ ≤ 4 * κ := by
  have hbp : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (lt_of_lt_of_le ha hab)
  have htpos : ∀ j : Fin 3, (0 : ℝ) < (W.thicknesses j : ℝ) := by
    intro j
    fin_cases j
    · rw [W.thicknesses_eq]
      exact_mod_cast ha
    · rw [W.thicknesses_eq]
      exact hbp
    · rw [W.thicknesses_eq]
      norm_num
  have hlin : f w - f 0 = f.linear w := by
    have h := (AffineMap.linearMap_vsub f w 0).symm
    simpa using h
  have hcoef : ∀ i : Fin 3, inner ℝ (f.linear w) (g i)
      = κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ w (W.basis i) := by
    intro i
    have h := Plank.inner_image_sub_basis W hnorm w 0 i
    rw [hlin] at h
    simpa using h
  have hbound : ∀ i : Fin 3, |inner ℝ (f.linear w) (g i)| ≤ 2 * κ := by
    intro i
    have hti_ne : (W.thicknesses i : ℝ) ≠ 0 := ne_of_gt (htpos i)
    calc
      |inner ℝ (f.linear w) (g i)| = |κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ w (W.basis i)| := by
        rw [hcoef i]
      _ = κ * ((W.thicknesses i : ℝ))⁻¹ * |inner ℝ w (W.basis i)| := by
        rw [abs_mul, abs_mul]
        rw [abs_of_pos hκ, abs_of_pos (inv_pos.mpr (htpos i))]
      _ ≤ κ * ((W.thicknesses i : ℝ))⁻¹ * (2 * (W.thicknesses i : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (hw i)
          (mul_nonneg hκ.le (le_of_lt (inv_pos.mpr (htpos i))))
      _ = 2 * κ := by
        field_simp [hti_ne]
  have hsq : ‖f.linear w‖ ^ 2 ≤ (4 * κ) ^ 2 := by
    calc
      ‖f.linear w‖ ^ 2 = ∑ i : Fin 3, (inner ℝ (f.linear w) (g i)) ^ 2 := by
        rw [← g.sum_sq_inner_left (f.linear w)]
      _ ≤ ∑ i : Fin 3, (2 * κ) ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro i _
        exact (sq_le_sq.mpr (by
          rw [abs_of_nonneg (by positivity : 0 ≤ 2 * κ)]
          exact hbound i))
      _ = 3 * (2 * κ) ^ 2 := by simp
      _ ≤ (4 * κ) ^ 2 := by
        nlinarith [sq_nonneg κ]
  have hnon : 0 ≤ ‖f.linear w‖ := norm_nonneg _
  have hconc : 0 ≤ 4 * κ := mul_nonneg (by norm_num) hκ.le
  have habs : |‖f.linear w‖| ≤ |4 * κ| := (sq_le_sq.mp hsq)
  simpa [abs_of_nonneg hnon, abs_of_nonneg hconc] using habs

/-- **Part C1: the area lower bound.**  Combining the area identity with `|det L| = κ³/(ab)` and
`‖L u‖ ≤ 4κ`.  The `ab` in the denominator is exactly what cancels the two anisotropic probe
bounds of Part C3. -/
theorem le_pullbackArea
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ} (hκ : 0 < κ)
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : Plank.IsPlankNormalisation W f κ g) (ha : 0 < a)
    {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1} (P : Plank a' b' ha'b' hb'1)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1)
    (hw : ∀ i : Fin 3, |(inner ℝ u (W.basis i) : ℝ)| ≤ 2 * (W.thicknesses i : ℝ))
    (halign : P.basis 2 = (‖f.linear u‖)⁻¹ • (f.linear u)) (hLu : f.linear u ≠ 0) :
    κ ^ 2 / (4 * (a : ℝ) * (b : ℝ))
      ≤ pullbackArea (Plank.pullbackNormal W κ g (P.basis 0))
          (Plank.pullbackNormal W κ g (P.basis 1)) := by
  set A := pullbackArea (Plank.pullbackNormal W κ g (P.basis 0))
      (Plank.pullbackNormal W κ g (P.basis 1)) with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    unfold pullbackArea
    exact Real.sqrt_nonneg _
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (lt_of_lt_of_le ha hab)
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hN0 : 0 < ‖f.linear u‖ := norm_pos_iff.mpr hLu
  have hNle : ‖f.linear u‖ ≤ 4 * κ := norm_linear_le_of_coord_bounds W hκ hnorm ha hw
  have hkey : A ^ 2 * ‖f.linear u‖ ^ 2 = (κ ^ 3 / ((a : ℝ) * (b : ℝ))) ^ 2 := by
    rw [hAdef]
    rw [sq_pullbackArea_mul_sq_norm_linear_eq W hnorm P hu halign hLu]
    exact sq_det_linear_eq W hnorm ha
  have hstep : (κ ^ 3 / ((a : ℝ) * (b : ℝ))) ^ 2 ≤ A ^ 2 * (4 * κ) ^ 2 := by
    rw [← hkey]
    have hN2 : ‖f.linear u‖ ^ 2 ≤ (4 * κ) ^ 2 := by nlinarith [hN0.le, hNle, hκ.le]
    nlinarith [sq_nonneg A, hN2]
  have hsq : (κ ^ 2 / (4 * (a : ℝ) * (b : ℝ))) ^ 2 ≤ A ^ 2 := by
    have hid : (κ ^ 3 / ((a : ℝ) * (b : ℝ))) ^ 2
        = (κ ^ 2 / (4 * (a : ℝ) * (b : ℝ))) ^ 2 * (4 * κ) ^ 2 := by
      field_simp [ne_of_gt ha0, ne_of_gt hb0, ne_of_gt hκ]
    have h4 : 0 < (4 * κ) ^ 2 := by positivity
    have hstep' : (κ ^ 2 / (4 * (a : ℝ) * (b : ℝ))) ^ 2 * (4 * κ) ^ 2
        ≤ A ^ 2 * (4 * κ) ^ 2 := by
      simpa [hid] using hstep
    exact le_of_mul_le_mul_right hstep' h4
  have hlhs0 : 0 ≤ κ ^ 2 / (4 * (a : ℝ) * (b : ℝ)) := by positivity
  simpa [abs_of_nonneg hlhs0, abs_of_nonneg hA0] using (sq_le_sq.mp hsq)

/-! ### Part C, frame bounds for the pullback normals -/

/-- **The crude pullback-normal bound.**  A unit normal pulls back to a vector of norm at most
`κ / a`, the largest dilation factor of the normalisation. -/
theorem norm_pullbackNormal_le_div_thin {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : Plank a b hab hb1) {κ : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1) :
    ‖Plank.pullbackNormal W κ g n‖ ≤ κ / (a : ℝ) := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have hbp : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le ha hab)
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hb1' : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have ht0 : (W.thicknesses 0 : ℝ) = (a : ℝ) := by
    rw [W.thicknesses_eq]
    simp
  have ht1 : (W.thicknesses 1 : ℝ) = (b : ℝ) := by
    rw [W.thicknesses_eq]
    simp
  have ht2 : (W.thicknesses 2 : ℝ) = (1 : ℝ) := by
    rw [W.thicknesses_eq]
    simp
  have htpos : ∀ j : Fin 3, 0 < (W.thicknesses j : ℝ) := by
    intro j
    fin_cases j
    · rw [W.thicknesses_eq]
      simp [ha]
    · rw [W.thicknesses_eq]
      simp [lt_of_lt_of_le ha hab]
    · rw [W.thicknesses_eq]
      norm_num
  have hinv : ∀ j : Fin 3, ((W.thicknesses j : ℝ))⁻¹ ≤ ((a : ℝ))⁻¹ := by
    intro j
    fin_cases j
    · rw [W.thicknesses_eq]
      simp
    · rw [W.thicknesses_eq]
      simpa using (inv_le_inv₀ hbp hap).mpr hab'
    · rw [W.thicknesses_eq]
      simpa using (inv_le_inv₀ (by norm_num : 0 < (1 : ℝ)) hap).mpr (le_trans hab' hb1')
  rw [Plank.pullbackNormal]
  let c : Fin 3 → ℝ := fun i => κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ n (g i)
  change ‖∑ i : Fin 3, c i • W.basis i‖ ≤ κ / (a : ℝ)
  have hcoef_apply : ∀ i : Fin 3,
      inner ℝ (W.basis i) (∑ j : Fin 3, c j • W.basis j) = c i := by
    intro i
    fin_cases i <;> simp [Fin.sum_univ_three, inner_add_right, real_inner_smul_right,
      W.basis.inner_eq_ite]
  have hcoef_sq : ∀ i : Fin 3,
      (c i) ^ 2 ≤ ((κ : ℝ) * (a : ℝ)⁻¹) ^ 2 * (inner ℝ n (g i)) ^ 2 := by
    intro i
    have hB : 0 ≤ (κ : ℝ) * (a : ℝ)⁻¹ := mul_nonneg hκ.le (inv_nonneg.mpr hap.le)
    have hB' : 0 ≤ κ * ((W.thicknesses i : ℝ))⁻¹ :=
      mul_nonneg hκ.le (inv_nonneg.mpr (le_of_lt (htpos i)))
    have hle : κ * ((W.thicknesses i : ℝ))⁻¹ ≤ (κ : ℝ) * (a : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (hinv i) hκ.le
    have hsqA : (κ * ((W.thicknesses i : ℝ))⁻¹) ^ 2 ≤ ((κ : ℝ) * (a : ℝ)⁻¹) ^ 2 := by
      exact (sq_le_sq).mpr (by
        rw [abs_of_nonneg hB', abs_of_nonneg hB]
        exact hle)
    calc
      (c i) ^ 2 = (κ * ((W.thicknesses i : ℝ))⁻¹) ^ 2 * (inner ℝ n (g i)) ^ 2 := by
        dsimp [c]
        ring
      _ ≤ ((κ : ℝ) * (a : ℝ)⁻¹) ^ 2 * (inner ℝ n (g i)) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hsqA (sq_nonneg _)
  have hsq : ‖∑ i : Fin 3, c i • W.basis i‖ ^ 2 ≤ (κ / (a : ℝ)) ^ 2 := by
    calc
      ‖∑ i : Fin 3, c i • W.basis i‖ ^ 2 = ∑ i : Fin 3, (c i) ^ 2 := by
        rw [← W.basis.sum_sq_inner_right (∑ i : Fin 3, c i • W.basis i)]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hcoef_apply i]
      _ ≤ ∑ i : Fin 3, ((κ : ℝ) * (a : ℝ)⁻¹) ^ 2 * (inner ℝ n (g i)) ^ 2 := by
        exact Finset.sum_le_sum (fun i hi => hcoef_sq i)
      _ = ((κ : ℝ) * (a : ℝ)⁻¹) ^ 2 * (∑ i : Fin 3, (inner ℝ n (g i)) ^ 2) := by
        rw [← Finset.mul_sum]
      _ = ((κ : ℝ) * (a : ℝ)⁻¹) ^ 2 := by
        rw [g.sum_sq_inner_left n, hn]
        simp
  have hdiv : 0 ≤ κ / (a : ℝ) := div_nonneg hκ.le hap.le
  have hleabs : |‖∑ i : Fin 3, c i • W.basis i‖| ≤ |κ / (a : ℝ)| := (sq_le_sq).mp hsq
  simpa [abs_of_nonneg (norm_nonneg (∑ i : Fin 3, c i • W.basis i)), abs_of_nonneg hdiv]
    using hleabs

/-- **The sharp pullback-normal bound for the thin axis of an inner plank.**  A unit normal that is
orthogonal to `g 0` misses the `κ/a` dilation entirely and pulls back to a vector of norm at most
`κ / b`.

The hypothesis is exactly the orthogonality clause exported by
`Plank.exists_normalisedTubePlank`, and this factor `b` rather than `a` is what makes the area
lower bound of the conflict-degree argument scale correctly. -/
theorem norm_pullbackNormal_le_div_mid {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : Plank a b hab hb1) {κ : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    {n : EuclideanSpace ℝ (Fin 3)} (hn : ‖n‖ = 1) (h0 : (inner ℝ n (g 0) : ℝ) = 0) :
    ‖Plank.pullbackNormal W κ g n‖ ≤ κ / (b : ℝ) := by
  have hbp : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (ha.trans_le hab)
  have hb1r : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  let c : Fin 3 → ℝ := fun i => κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ n (g i)
  have hdecomp : Plank.pullbackNormal W κ g n = ∑ i, c i • W.basis i := by
    rfl
  -- coefficient extraction: the inner product with `W.basis i` picks out `c i`
  have hcoeff : ∀ i, inner ℝ (∑ j, c j • W.basis j) (W.basis i) = c i := by
    intro i
    simpa using (Orthonormal.inner_left_fintype W.basis.orthonormal (fun j => c j) i)
  -- Parseval on the orthonormal frame `W.basis`: `‖m‖² = ∑ᵢ cᵢ²`
  have hnorm_sq : ‖∑ i, c i • W.basis i‖ ^ 2 = ∑ i, (c i) ^ 2 := by
    calc
      ‖∑ i, c i • W.basis i‖ ^ 2 = ∑ i, (inner ℝ (∑ j, c j • W.basis j) (W.basis i)) ^ 2 := by
        rw [← W.basis.sum_sq_inner_left (∑ j, c j • W.basis j)]
      _ = ∑ i, (c i) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hcoeff i]
  -- `1 ≤ b⁻¹` because `b ≤ 1`, so `κ ≤ κ / b`
  have hκ_le : κ ≤ κ / (b : ℝ) := by
    have hinv : (1 : ℝ) ≤ (b : ℝ)⁻¹ := by
      have : (1 : ℝ)⁻¹ ≤ (b : ℝ)⁻¹ := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1) hbp).mpr hb1r
      simpa using this
    rw [div_eq_mul_inv]
    calc
      κ = κ * 1 := (mul_one κ).symm
      _ ≤ κ * (b : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hinv hκ.le
  have hκ2_le : κ ^ 2 ≤ (κ / (b : ℝ)) ^ 2 := by
    exact (sq_le_sq.mpr (by
      rw [abs_of_nonneg hκ.le, abs_of_nonneg (div_nonneg hκ.le hbp.le)]
      exact hκ_le))
  -- termwise bounds: `i = 0` vanishes, `i = 1` is exact, `i = 2` uses `κ² / (κ/b)²`
  have hterm : ∀ i, (c i) ^ 2 ≤ (κ / (b : ℝ)) ^ 2 * (inner ℝ n (g i)) ^ 2 := by
    intro i
    fin_cases i
    · have hc0 : c 0 = 0 := by
        simp [c, h0]
      change c 0 ^ 2 ≤ (κ / (b : ℝ)) ^ 2 * (inner ℝ n (g 0)) ^ 2
      rw [hc0]
      norm_num
      exact mul_nonneg (sq_nonneg (κ / (b : ℝ))) (sq_nonneg (inner ℝ n (g 0)))
    · have hc1 : (c 1) ^ 2 = (κ / (b : ℝ)) ^ 2 * (inner ℝ n (g 1)) ^ 2 := by
        dsimp [c]
        rw [W.thicknesses_eq, div_eq_mul_inv]
        simp
        ring
      change c 1 ^ 2 ≤ (κ / (b : ℝ)) ^ 2 * (inner ℝ n (g 1)) ^ 2
      rw [hc1]
    · have hc2 : (c 2) ^ 2 = κ ^ 2 * (inner ℝ n (g 2)) ^ 2 := by
        dsimp [c]
        rw [W.thicknesses_eq]
        simp
        ring
      change c 2 ^ 2 ≤ (κ / (b : ℝ)) ^ 2 * (inner ℝ n (g 2)) ^ 2
      rw [hc2]
      exact mul_le_mul_of_nonneg_right hκ2_le (sq_nonneg (inner ℝ n (g 2)))
  -- sum the termwise bounds and apply Parseval for `g`: `∑ᵢ ⟪n, g i⟫² = ‖n‖² = 1`
  have hstep : ∑ i, (c i) ^ 2 ≤ (κ / (b : ℝ)) ^ 2 * ∑ i, (inner ℝ n (g i)) ^ 2 := by
    calc
      ∑ i, (c i) ^ 2 ≤ ∑ i, (κ / (b : ℝ)) ^ 2 * (inner ℝ n (g i)) ^ 2 :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = (κ / (b : ℝ)) ^ 2 * ∑ i, (inner ℝ n (g i)) ^ 2 := by
        rw [Finset.mul_sum]
  have hp : ∑ i, (inner ℝ n (g i)) ^ 2 = 1 := by
    rw [g.sum_sq_inner_left n, hn]
    norm_num
  have hbnd : ‖Plank.pullbackNormal W κ g n‖ ^ 2 ≤ ((κ / (b : ℝ)) ^ 2) := by
    calc
      ‖Plank.pullbackNormal W κ g n‖ ^ 2 = ∑ i, (c i) ^ 2 := by
        rw [hdecomp, hnorm_sq]
      _ ≤ (κ / (b : ℝ)) ^ 2 * ∑ i, (inner ℝ n (g i)) ^ 2 := hstep
      _ = (κ / (b : ℝ)) ^ 2 := by
        rw [hp, mul_one]
  have hnon : 0 ≤ ‖Plank.pullbackNormal W κ g n‖ := norm_nonneg _
  have hqn : 0 ≤ κ / (b : ℝ) := div_nonneg hκ.le hbp.le
  have hbnd' : ‖Plank.pullbackNormal W κ g n‖ ≤ |κ / (b : ℝ)| := by
    simpa [abs_of_nonneg hnon] using (sq_le_sq.mp hbnd)
  simpa [abs_of_nonneg hqn] using hbnd'

/-! ### Part C2: the span -/

/-- **Part C2.**  Two vectors orthogonal to a unit `u` and spanning positive area span the whole
plane `u ᗮ`, so every vector orthogonal to `u` is a combination of them.

Both `span ℝ {q₀, q₁}` and `(ℝ ∙ u)ᗮ` have finrank `2` in `EuclideanSpace ℝ (Fin 3)`, and the
former is contained in the latter, so they agree. -/
theorem exists_smul_add_smul_of_inner_eq_zero
    {u q₀ q₁ v : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1)
    (hq0 : (inner ℝ u q₀ : ℝ) = 0) (hq1 : (inner ℝ u q₁ : ℝ) = 0)
    (harea : 0 < pullbackArea q₀ q₁) (hv : (inner ℝ u v : ℝ) = 0) :
    ∃ x y : ℝ, v = x • q₀ + y • q₁ := by
  -- Step 1: positive Gram determinant gives linear independence of `![q₀, q₁]`
  have hG : 0 < ‖q₀‖ ^ 2 * ‖q₁‖ ^ 2 - (inner ℝ q₀ q₁ : ℝ) ^ 2 := by
    unfold pullbackArea at harea
    exact Real.sqrt_pos.mp harea
  have hli : LinearIndependent ℝ ![q₀, q₁] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : s * ‖q₀‖ ^ 2 + t * (inner ℝ q₀ q₁ : ℝ) = 0 := by
      have h := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => (inner ℝ q₀ w : ℝ)) hst
      simpa [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] using h
    have h2 : s * (inner ℝ q₀ q₁ : ℝ) + t * ‖q₁‖ ^ 2 = 0 := by
      have h := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => (inner ℝ w q₁ : ℝ)) hst
      simpa [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] using h
    have hs : s = 0 := by
      have hsG : s * (‖q₀‖ ^ 2 * ‖q₁‖ ^ 2 - (inner ℝ q₀ q₁ : ℝ) ^ 2) = 0 := by
        calc
          s * (‖q₀‖ ^ 2 * ‖q₁‖ ^ 2 - (inner ℝ q₀ q₁ : ℝ) ^ 2)
              = (s * ‖q₀‖ ^ 2 + t * (inner ℝ q₀ q₁ : ℝ)) * ‖q₁‖ ^ 2
                - (s * (inner ℝ q₀ q₁ : ℝ) + t * ‖q₁‖ ^ 2) * (inner ℝ q₀ q₁ : ℝ) := by
                  ring
          _ = 0 := by rw [h1, h2]; ring
      exact (mul_eq_zero.mp hsG).resolve_right (ne_of_gt hG)
    have ht : t = 0 := by
      have htG : t * (‖q₀‖ ^ 2 * ‖q₁‖ ^ 2 - (inner ℝ q₀ q₁ : ℝ) ^ 2) = 0 := by
        calc
          t * (‖q₀‖ ^ 2 * ‖q₁‖ ^ 2 - (inner ℝ q₀ q₁ : ℝ) ^ 2)
              = (s * (inner ℝ q₀ q₁ : ℝ) + t * ‖q₁‖ ^ 2) * ‖q₀‖ ^ 2
                - (s * ‖q₀‖ ^ 2 + t * (inner ℝ q₀ q₁ : ℝ)) * (inner ℝ q₀ q₁ : ℝ) := by
                  ring
          _ = 0 := by rw [h1, h2]; ring
      exact (mul_eq_zero.mp htG).resolve_right (ne_of_gt hG)
    exact ⟨hs, ht⟩
  -- Step 2: the orthogonal complement `H = (ℝ ∙ u)ᗮ` has finrank 2 and contains q₀, q₁, v
  let H : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
    (Submodule.span ℝ ({u} : Set (EuclideanSpace ℝ (Fin 3))))ᗮ
  have hu_ne : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    norm_num at hu
  have hq0H : q₀ ∈ H := by
    dsimp [H]
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    rw [real_inner_comm]
    exact hq0
  have hq1H : q₁ ∈ H := by
    dsimp [H]
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    rw [real_inner_comm]
    exact hq1
  have hvH : v ∈ H := by
    dsimp [H]
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    rw [real_inner_comm]
    exact hv
  have hfin_H : Module.finrank ℝ H = 2 := by
    dsimp [H]
    refine Submodule.finrank_add_finrank_orthogonal'
      (K := Submodule.span ℝ ({u} : Set (EuclideanSpace ℝ (Fin 3)))) ?_
    rw [finrank_span_singleton hu_ne, finrank_euclideanSpace_fin]
  -- Step 3: `span ℝ {q₀, q₁} ≤ H` with finrank 2, so they agree
  have hS_le_H : (Submodule.span ℝ ({q₀, q₁} : Set (EuclideanSpace ℝ (Fin 3)))) ≤ H := by
    rw [Submodule.span_le]
    intro z hz
    rcases hz with rfl | hz
    · exact hq0H
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hq1H
  have hfin_S : Module.finrank ℝ
      (Submodule.span ℝ ({q₀, q₁} : Set (EuclideanSpace ℝ (Fin 3)))) = 2 := by
    rw [← Matrix.range_cons_cons_empty q₀ q₁ ![],
      finrank_span_eq_card (R := ℝ) (M := EuclideanSpace ℝ (Fin 3)) hli]
    simp
  have hS_eq_H : (Submodule.span ℝ ({q₀, q₁} : Set (EuclideanSpace ℝ (Fin 3)))) = H := by
    refine Submodule.eq_of_le_of_finrank_eq hS_le_H ?_
    rw [hfin_S, hfin_H]
  -- Step 4: `v ∈ H = span ℝ {q₀, q₁}` gives the combination
  have hvS : v ∈ Submodule.span ℝ ({q₀, q₁} : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [hS_eq_H]
    exact hvH
  rcases (Submodule.mem_span_pair.mp hvS) with ⟨x, y, hxy⟩
  exact ⟨x, y, hxy.symm⟩

/-- Two pullback-normal coordinates control projective direction distance inside one hemisphere.

The directions are first oriented towards the unit reference `r`.  Their orthogonal projections
to `rᵌ` lie in the plane spanned by `q₀,q₁`; Cramer's estimate controls the difference of
those projections, and the unit-sphere graph estimate recovers the full projective chord. -/
theorem projNormalDist_le_two_mul_pullbackCoordinates
    {r v w q₀ q₁ : EuclideanSpace ℝ (Fin 3)}
    (hr : ‖r‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvr : projNormalDist v r ≤ 1 / 2) (hwr : projNormalDist w r ≤ 1 / 2)
    (hrq₀ : (inner ℝ r q₀ : ℝ) = 0) (hrq₁ : (inner ℝ r q₁ : ℝ) = 0)
    (harea : 0 < pullbackArea q₀ q₁) :
    projNormalDist v w ≤ 2 *
      ((‖q₀‖ * |(inner ℝ q₁ (orientedNormal r v - orientedNormal r w) : ℝ)|
          + ‖q₁‖ * |(inner ℝ q₀ (orientedNormal r v - orientedNormal r w) : ℝ)|) /
        pullbackArea q₀ q₁) := by
  let v' := orientedNormal r v
  let w' := orientedNormal r w
  let z := (v' - (inner ℝ r v' : ℝ) • r) -
    (w' - (inner ℝ r w' : ℝ) • r)
  have hrr : (inner ℝ r r : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hr]
    norm_num
  have hzorth : (inner ℝ r z : ℝ) = 0 := by
    dsimp [z]
    simp only [inner_sub_right, real_inner_smul_right, hrr]
    ring
  have hq₀z : (inner ℝ q₀ z : ℝ) = inner ℝ q₀ (v' - w') := by
    have hq₀r : (inner ℝ q₀ r : ℝ) = 0 := by
      simpa [real_inner_comm] using hrq₀
    dsimp [z]
    simp only [inner_sub_right, real_inner_smul_right, hq₀r]
    ring
  have hq₁z : (inner ℝ q₁ z : ℝ) = inner ℝ q₁ (v' - w') := by
    have hq₁r : (inner ℝ q₁ r : ℝ) = 0 := by
      simpa [real_inner_comm] using hrq₁
    dsimp [z]
    simp only [inner_sub_right, real_inner_smul_right, hq₁r]
    ring
  obtain ⟨x, y, hzspan⟩ :=
    exists_smul_add_smul_of_inner_eq_zero hr hrq₀ hrq₁ harea hzorth
  have hcramer := norm_mul_pullbackArea_le hzspan
  have hzbound : ‖z‖ ≤
      (‖q₀‖ * |(inner ℝ q₁ (v' - w') : ℝ)|
          + ‖q₁‖ * |(inner ℝ q₀ (v' - w') : ℝ)|) /
        pullbackArea q₀ q₁ := by
    rw [le_div_iff₀ harea]
    simpa only [hq₀z, hq₁z] using hcramer
  have hgraph := norm_orientedNormal_sub_le_two_mul_norm_orthogonal_sub
    r v w hr hv hw hvr hwr
  calc
    projNormalDist v w ≤ ‖v' - w'‖ := by
      dsimp [v', w']
      exact projNormalDist_le_norm_orientedNormal_sub r v w
    _ ≤ 2 * ‖z‖ := by simpa only [v', w', z] using hgraph
    _ ≤ 2 * ((‖q₀‖ * |(inner ℝ q₁ (v' - w') : ℝ)|
          + ‖q₁‖ * |(inner ℝ q₀ (v' - w') : ℝ)|) /
        pullbackArea q₀ q₁) := by gcongr
    _ = 2 * ((‖q₀‖ *
          |(inner ℝ q₁ (orientedNormal r v - orientedNormal r w) : ℝ)|
          + ‖q₁‖ *
          |(inner ℝ q₀ (orientedNormal r v - orientedNormal r w) : ℝ)|) /
        pullbackArea q₀ q₁) := by rfl

/-- One direction is projectively close to a reference when its two pullback-normal coordinates
are small.  Unlike the two-direction graph estimate, this form needs no a priori cap assumption. -/
theorem projNormalDist_le_sqrtTwo_mul_pullbackCoordinates
    {r w q₀ q₁ : EuclideanSpace ℝ (Fin 3)}
    (hr : ‖r‖ = 1) (hw : ‖w‖ = 1)
    (hrq₀ : (inner ℝ r q₀ : ℝ) = 0) (hrq₁ : (inner ℝ r q₁ : ℝ) = 0)
    (harea : 0 < pullbackArea q₀ q₁) :
    projNormalDist w r ≤ Real.sqrt 2 *
      ((‖q₀‖ * |(inner ℝ q₁ w : ℝ)| + ‖q₁‖ * |(inner ℝ q₀ w : ℝ)|) /
        pullbackArea q₀ q₁) := by
  let z := w - (inner ℝ r w : ℝ) • r
  have hrr : (inner ℝ r r : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hr]
    norm_num
  have hzorth : (inner ℝ r z : ℝ) = 0 := by
    dsimp [z]
    simp only [inner_sub_right, real_inner_smul_right, hrr]
    ring
  have hq₀z : (inner ℝ q₀ z : ℝ) = inner ℝ q₀ w := by
    have hq₀r : (inner ℝ q₀ r : ℝ) = 0 := by simpa [real_inner_comm] using hrq₀
    dsimp [z]
    simp [inner_sub_right, real_inner_smul_right, hq₀r]
  have hq₁z : (inner ℝ q₁ z : ℝ) = inner ℝ q₁ w := by
    have hq₁r : (inner ℝ q₁ r : ℝ) = 0 := by simpa [real_inner_comm] using hrq₁
    dsimp [z]
    simp [inner_sub_right, real_inner_smul_right, hq₁r]
  obtain ⟨x, y, hzspan⟩ :=
    exists_smul_add_smul_of_inner_eq_zero hr hrq₀ hrq₁ harea hzorth
  have hcramer := norm_mul_pullbackArea_le hzspan
  have hzbound : ‖z‖ ≤
      (‖q₀‖ * |(inner ℝ q₁ w : ℝ)| + ‖q₁‖ * |(inner ℝ q₀ w : ℝ)|) /
        pullbackArea q₀ q₁ := by
    rw [le_div_iff₀ harea]
    simpa only [hq₀z, hq₁z] using hcramer
  have hproj := projective_cap_of_orthogonal_le
    (u := r) (v := w)
    (r := (‖q₀‖ * |(inner ℝ q₁ w : ℝ)| + ‖q₁‖ * |(inner ℝ q₀ w : ℝ)|) /
      pullbackArea q₀ q₁)
    hr hw (by positivity) (by simpa [z] using hzbound)
  simpa only [projNormalDist] using hproj

/-- A rectangular pair of direction coordinates gives a finite projective-cap partition.

A maximum coordinate-separated subfamily supplies the class representatives.  Rectangular volume
packing bounds their number, while saturation and `hclose` put every original direction into the
projective cap of its assigned representative. -/
theorem exists_projective_direction_partition_of_rectangle
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {I : Type*} {s : Finset I} {a b : I → ℝ} {T : I → E}
    {Rx Ry r cδ : ℝ} (hr : 0 < r) (hRx : 0 ≤ Rx) (hRy : 0 ≤ Ry) (hcδ : 0 ≤ cδ)
    (ha : ∀ i ∈ s, |a i| ≤ Rx) (hb : ∀ i ∈ s, |b i| ≤ Ry)
    (hclose : ∀ i ∈ s, ∀ j ∈ s,
      |a i - a j| + |b i - b j| < r → projNormalDist (T i) (T j) ≤ cδ) :
    ∃ (S : Finset I) (g : I → I), S ⊆ s ∧
      (∀ i ∈ s, g i ∈ S) ∧
      (∀ i ∈ s, projNormalDist (T i) (T (g i)) ≤ cδ) ∧
      (S.card : ℝ) ≤
        ((Rx + r / 4) / (r / 4)) * ((Ry + r / 4) / (r / 4)) := by
  classical
  let Rel : I → I → Prop := fun i j ↦ r ≤ |a i - a j| + |b i - b j|
  have hsymm : ∀ i j, Rel i j → Rel j i := by
    intro i j hij
    dsimp [Rel] at hij ⊢
    simpa only [abs_sub_comm] using hij
  obtain ⟨S, hSs, hsep, hsat⟩ := exists_max_card_separated s Rel hsymm
  choose! g hgS hg using fun i (hi : i ∈ s) ↦ hsat i hi
  have hdir : ∀ i ∈ s, projNormalDist (T i) (T (g i)) ≤ cδ := by
    intro i hi
    rcases hg i hi with hgi | hnrel
    · rw [hgi]
      simpa [projNormalDist] using hcδ
    · apply hclose i hi (g i) (hSs (hgS i hi))
      apply lt_of_not_ge
      intro hge
      apply hnrel
      dsimp [Rel]
      simpa only [abs_sub_comm] using hge
  have hcard : (S.card : ℝ) ≤
      ((Rx + r / 4) / (r / 4)) * ((Ry + r / 4) / (r / 4)) := by
    have hp := Tube.card_le_of_L1_separated_in_rectangle
      S a b 0 0 hr hRx hRy (fun i hi j hj hij ↦ hsep i hi j hj hij)
      (fun i hi ↦ by simpa [Real.norm_eq_abs] using ha i (hSs hi))
      (fun i hi ↦ by simpa [Real.norm_eq_abs] using hb i (hSs hi))
    simpa using hp
  exact ⟨S, g, hSs, hgS, hdir, hcard⟩

/-- Pullback-normal coordinates partition a direction family into position-counting caps.

The first coordinate is weighted by `‖q₁‖ / area` and the second by `‖q₀‖ / area`; with these
weights the Cramer bound is exactly their `L¹` distance. -/
theorem exists_pullback_direction_partition
    {I : Type*} {s : Finset I} {dir : I → EuclideanSpace ℝ (Fin 3)}
    {r q₀ q₁ : EuclideanSpace ℝ (Fin 3)}
    (hrunit : ‖r‖ = 1) (hunit : ∀ i ∈ s, ‖dir i‖ = 1)
    (hrq₀ : (inner ℝ r q₀ : ℝ) = 0) (hrq₁ : (inner ℝ r q₁ : ℝ) = 0)
    (harea : 0 < pullbackArea q₀ q₁)
    {X Y cslide δ : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hcslide : 0 < cslide) (hδ : 0 < δ)
    (hcap : ∀ i ∈ s, projNormalDist (dir i) r ≤ 1 / 2)
    (hprobe₀ : ∀ i ∈ s, |(inner ℝ q₀ (dir i) : ℝ)| ≤ X)
    (hprobe₁ : ∀ i ∈ s, |(inner ℝ q₁ (dir i) : ℝ)| ≤ Y) :
    ∃ (S : Finset I) (g : I → I), S ⊆ s ∧
      (∀ i ∈ s, g i ∈ S) ∧
      (∀ i ∈ s, projNormalDist (dir i) (dir (g i)) ≤ cslide * δ) ∧
      (S.card : ℝ) ≤
        (((‖q₁‖ / pullbackArea q₀ q₁) * X + (cslide * δ / 2) / 4) /
            ((cslide * δ / 2) / 4)) *
          (((‖q₀‖ / pullbackArea q₀ q₁) * Y + (cslide * δ / 2) / 4) /
            ((cslide * δ / 2) / 4)) := by
  let A := pullbackArea q₀ q₁
  let fx : I → ℝ := fun i ↦ (‖q₁‖ / A) * inner ℝ q₀ (orientedNormal r (dir i))
  let fy : I → ℝ := fun i ↦ (‖q₀‖ / A) * inner ℝ q₁ (orientedNormal r (dir i))
  have hA : 0 < A := harea
  have hcoef₀ : 0 ≤ ‖q₁‖ / A := by positivity
  have hcoef₁ : 0 ≤ ‖q₀‖ / A := by positivity
  have horient₀ : ∀ i ∈ s,
      |(inner ℝ q₀ (orientedNormal r (dir i)) : ℝ)| = |(inner ℝ q₀ (dir i) : ℝ)| := by
    intro i hi
    unfold orientedNormal
    split_ifs <;> simp
  have horient₁ : ∀ i ∈ s,
      |(inner ℝ q₁ (orientedNormal r (dir i)) : ℝ)| = |(inner ℝ q₁ (dir i) : ℝ)| := by
    intro i hi
    unfold orientedNormal
    split_ifs <;> simp
  have hfx : ∀ i ∈ s, |fx i| ≤ (‖q₁‖ / A) * X := by
    intro i hi
    dsimp [fx]
    rw [abs_mul, abs_of_nonneg hcoef₀, horient₀ i hi]
    exact mul_le_mul_of_nonneg_left (hprobe₀ i hi) hcoef₀
  have hfy : ∀ i ∈ s, |fy i| ≤ (‖q₀‖ / A) * Y := by
    intro i hi
    dsimp [fy]
    rw [abs_mul, abs_of_nonneg hcoef₁, horient₁ i hi]
    exact mul_le_mul_of_nonneg_left (hprobe₁ i hi) hcoef₁
  have hclose : ∀ i ∈ s, ∀ j ∈ s,
      |fx i - fx j| + |fy i - fy j| < cslide * δ / 2 →
        projNormalDist (dir i) (dir j) ≤ cslide * δ := by
    intro i hi j hj hcoord
    have hproj := projNormalDist_le_two_mul_pullbackCoordinates
      hrunit (hunit i hi) (hunit j hj) (hcap i hi) (hcap j hj) hrq₀ hrq₁ harea
    have hrewrite :
        ((‖q₀‖ * |(inner ℝ q₁
              (orientedNormal r (dir i) - orientedNormal r (dir j)) : ℝ)|
            + ‖q₁‖ * |(inner ℝ q₀
              (orientedNormal r (dir i) - orientedNormal r (dir j)) : ℝ)|) / A) =
          |fx i - fx j| + |fy i - fy j| := by
      dsimp [fx, fy, A]
      rw [inner_sub_right, inner_sub_right]
      rw [show ‖q₁‖ / pullbackArea q₀ q₁ =
          ‖q₁‖ * (pullbackArea q₀ q₁)⁻¹ by ring,
        show ‖q₀‖ / pullbackArea q₀ q₁ =
          ‖q₀‖ * (pullbackArea q₀ q₁)⁻¹ by ring]
      rw [← mul_sub, ← mul_sub]
      simp only [abs_mul, abs_of_nonneg (norm_nonneg q₁),
        abs_of_nonneg (norm_nonneg q₀), abs_inv, abs_of_pos harea]
      field_simp [harea.ne']
      ring
    rw [hrewrite] at hproj
    linarith
  simpa only [A] using exists_projective_direction_partition_of_rectangle
    (s := s) (a := fx) (b := fy) (T := dir)
    (Rx := (‖q₁‖ / A) * X) (Ry := (‖q₀‖ / A) * Y)
    (r := cslide * δ / 2) (cδ := cslide * δ)
    (by positivity) (by positivity) (by positivity) (by positivity) hfx hfy hclose

/-- Pullback-coordinate direction partitioning followed by the sharp position count.

This lemma contains the finite-fibre bookkeeping shared by all inner-plank tests.  Its right-hand
side deliberately retains the exact rectangular packing expression; the application to
Proposition 6.6(A) bounds that expression using the normalisation geometry. -/
theorem exists_card_le_of_pullback_direction_partition :
    ∃ (cslide : ℝ) (Cpos : ℕ) (δ₀ : ℝ),
      0 < cslide ∧ 0 < Cpos ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : ℝ≥0} (_hδ : 0 < δ) (_hδ_le : (δ : ℝ) ≤ δ₀)
        {I : Type*} (s : Finset I) (T : I → Tube δ (EuclideanSpace ℝ (Fin 3)))
        (_hED : (s : Set I).Pairwise
          (fun i j ↦ _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier))
        {r q₀ q₁ : EuclideanSpace ℝ (Fin 3)}
        (_hrunit : ‖r‖ = 1) (_hunit : ∀ i ∈ s, ‖(T i).direction‖ = 1)
        (_hrq₀ : (inner ℝ r q₀ : ℝ) = 0) (_hrq₁ : (inner ℝ r q₁ : ℝ) = 0)
        (_harea : 0 < pullbackArea q₀ q₁)
        {X Y : ℝ} (_hX : 0 ≤ X) (_hY : 0 ≤ Y)
        (_hcap : ∀ i ∈ s, projNormalDist (T i).direction r ≤ 1 / 2)
        (_hprobe₀ : ∀ i ∈ s, |(inner ℝ q₀ (T i).direction : ℝ)| ≤ X)
        (_hprobe₁ : ∀ i ∈ s, |(inner ℝ q₁ (T i).direction : ℝ)| ≤ Y)
        {K : Set (EuclideanSpace ℝ (Fin 3))}
        (_hK_meas : MeasurableSet K) (_hK_cpt : IsCompact K)
        {M : ℝ} (_hM_pos : 0 < M)
        (_hK_vol : volume K ≤ ENNReal.ofReal M * (δ : ENNReal) ^ 2)
        (_hsub : ∀ i ∈ s, (T i).carrier ⊆ K),
        (s.card : ℝ) ≤
          (((‖q₁‖ / pullbackArea q₀ q₁) * X + (cslide * (δ : ℝ) / 2) / 4) /
              ((cslide * (δ : ℝ) / 2) / 4)) *
            (((‖q₀‖ / pullbackArea q₀ q₁) * Y + (cslide * (δ : ℝ) / 2) / 4) /
              ((cslide * (δ : ℝ) / 2) / 4)) * (Cpos : ℝ) * M := by
  classical
  have hn : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  obtain ⟨cslide, Cpos, δ₀, hcslide, hCpos, hδ₀, hδ₀1, hpos⟩ :=
    position_count_le_of_bad_directionClass'
      (E := EuclideanSpace ℝ (Fin 3)) hn
  refine ⟨cslide, Cpos, δ₀, hcslide, hCpos, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδle I s T hED r q₀ q₁ hrunit hunit hrq₀ hrq₁ harea X Y hX hY hcap
    hprobe₀ hprobe₁ K hKmeas hKcpt M hMpos hKvol hsub
  obtain ⟨S, g, hSs, hgS, hgdir, hScard⟩ := exists_pullback_direction_partition
    hrunit hunit hrq₀ hrq₁ harea hX hY hcslide (NNReal.coe_pos.mpr hδ)
    hcap hprobe₀ hprobe₁
  have hfibre : ∀ u ∈ S,
      ((s.filter fun i ↦ g i = u).card : ℝ) ≤ (Cpos : ℝ) * M := by
    intro u hu
    have huS : u ∈ s := hSs hu
    have hED' : ((s.filter fun i ↦ g i = u : Finset I) : Set I).Pairwise
        (fun i j ↦ _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) :=
      hED.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    have hdir : ∀ i ∈ s.filter fun i ↦ g i = u,
        min ‖(T i).direction - (T u).direction‖
            ‖(T i).direction + (T u).direction‖ ≤ cslide * (δ : ℝ) := by
      intro i hi
      have hi' := Finset.mem_filter.mp hi
      simpa only [projNormalDist, hi'.2] using hgdir i hi'.1
    have hbad : ∀ i ∈ s.filter fun i ↦ g i = u,
        volume ((T i).carrier ∩ K) ≥ ENNReal.ofReal 1 * volume (T i).carrier := by
      intro i hi
      rw [ENNReal.ofReal_one, one_mul]
      rw [Set.inter_eq_left.mpr (hsub i (Finset.mem_filter.mp hi).1)]
    have hKvol' :
        volume K ≤ ENNReal.ofReal M *
          (δ : ENNReal) ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) := by
      simpa [finrank_euclideanSpace_fin] using hKvol
    have h := hpos hδ hδle (s.filter fun i ↦ g i = u) T hED'
      (e := (T u).direction) (hunit u huS) hdir
      (K := K) hKmeas hKcpt hMpos hKvol' (c := 1) (by norm_num) hbad
    simpa using h
  have hsum : (s.card : ℝ) = ∑ u ∈ S, ((s.filter fun i ↦ g i = u).card : ℝ) := by
    norm_cast
    exact Finset.card_eq_sum_card_fiberwise hgS
  calc
    (s.card : ℝ) = ∑ u ∈ S, ((s.filter fun i ↦ g i = u).card : ℝ) := hsum
    _ ≤ ∑ _u ∈ S, (Cpos : ℝ) * M := Finset.sum_le_sum hfibre
    _ = (S.card : ℝ) * ((Cpos : ℝ) * M) := by simp
    _ ≤
        ((((‖q₁‖ / pullbackArea q₀ q₁) * X + (cslide * (δ : ℝ) / 2) / 4) /
              ((cslide * (δ : ℝ) / 2) / 4)) *
            (((‖q₀‖ / pullbackArea q₀ q₁) * Y + (cslide * (δ : ℝ) / 2) / 4) /
              ((cslide * (δ : ℝ) / 2) / 4)) * ((Cpos : ℝ) * M)) := by
      gcongr
    _ = _ := by ring

/-! ### Part C3: the direction estimate -/

/-- **Part C3, the probe bounds.**  If the affine image of a tube lies in the `11`-fold dilation of
the reference inner plank, then the tube's direction pairs with the `k`-th pullback normal at scale
`22 · (the k-th half-width)`.  For `k = 0, 1` these are `22δ/b` and `22δ/a`. -/
theorem abs_inner_direction_pullbackNormal_le
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : Plank.IsPlankNormalisation W f κ g)
    {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1} (Pi : Plank a' b' ha'b' hb'1)
    {δ : ℝ≥0} (Tj : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hsub : (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ''
        (Tj.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ((Pi.toPrismNDim.dilation 11).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (k : Fin 3) :
    |(inner ℝ Tj.direction (Plank.pullbackNormal W κ g (Pi.basis k)) : ℝ)|
      ≤ 22 * (Pi.thicknesses k : ℝ) := by
  have hx_mem : Tj.x ∈ (Tj.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [Tj.carrier_eq]
    exact Set.mem_iUnion₂.mpr ⟨Tj.x, left_mem_segment ℝ Tj.x Tj.y,
      Metric.mem_closedBall_self (NNReal.coe_nonneg δ)⟩
  have hy_mem : Tj.y ∈ (Tj.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [Tj.carrier_eq]
    exact Set.mem_iUnion₂.mpr ⟨Tj.y, right_mem_segment ℝ Tj.x Tj.y,
      Metric.mem_closedBall_self (NNReal.coe_nonneg δ)⟩
  have hfy : f Tj.y ∈ (Pi.toPrismNDim.dilation 11).carrier := hsub ⟨Tj.y, hy_mem, rfl⟩
  have hfx : f Tj.x ∈ (Pi.toPrismNDim.dilation 11).carrier := hsub ⟨Tj.x, hx_mem, rfl⟩
  have hby : |(inner ℝ (Pi.basis k) (f Tj.y - Pi.center) : ℝ)| ≤ 11 * (Pi.thicknesses k : ℝ) := by
    have h := ((Pi.toPrismNDim.dilation 11).mem_carrier_iff (f Tj.y)).1 hfy k
    simp only [PrismNDim.dilation, PrismNDim.basis_mk', PrismNDim.center_mk',
      PrismNDim.thicknesses_mk'] at h
    rw [OrthonormalBasis.repr_apply_apply] at h
    rw [NNReal.coe_mul] at h
    exact h
  have hbx : |(inner ℝ (Pi.basis k) (f Tj.x - Pi.center) : ℝ)| ≤ 11 * (Pi.thicknesses k : ℝ) := by
    have h := ((Pi.toPrismNDim.dilation 11).mem_carrier_iff (f Tj.x)).1 hfx k
    simp only [PrismNDim.dilation, PrismNDim.basis_mk', PrismNDim.center_mk',
      PrismNDim.thicknesses_mk'] at h
    rw [OrthonormalBasis.repr_apply_apply] at h
    rw [NNReal.coe_mul] at h
    exact h
  change |(inner ℝ (Tj.y - Tj.x) (Plank.pullbackNormal W κ g (Pi.basis k)) : ℝ)|
      ≤ 22 * (Pi.thicknesses k : ℝ)
  rw [← Plank.inner_pullbackNormal_sub W hnorm (Pi.basis k) Tj.y Tj.x]
  rw [show f Tj.y - f Tj.x = (f Tj.y - Pi.center) - (f Tj.x - Pi.center) by abel]
  rw [inner_sub_left]
  simp_rw [real_inner_comm]
  calc
    |(inner ℝ (Pi.basis k) (f Tj.y - Pi.center) : ℝ)
        - (inner ℝ (Pi.basis k) (f Tj.x - Pi.center) : ℝ)|
      ≤ |(inner ℝ (Pi.basis k) (f Tj.y - Pi.center) : ℝ)|
          + |(inner ℝ (Pi.basis k) (f Tj.x - Pi.center) : ℝ)| := by
          exact abs_sub _ _
    _ ≤ 11 * (Pi.thicknesses k : ℝ) + 11 * (Pi.thicknesses k : ℝ) := by
          exact add_le_add hby hbx
    _ = 22 * (Pi.thicknesses k : ℝ) := by ring

/-- Variable-dilation form of `abs_inner_direction_pullbackNormal_le`.

If the normalised image of a tube lies in `L · P`, its direction has pullback-normal
coordinates at most `2L` times the corresponding half-width of `P`.  Keeping `L` visible is
essential for the dilated-thickening tests in the inner Frostman estimate. -/
theorem abs_inner_direction_pullbackNormal_le_dilation
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : Plank.IsPlankNormalisation W f κ g)
    {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1} (P : Plank a' b' ha'b' hb'1)
    {δ L : ℝ≥0} (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hsub : (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ''
        (T.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ((P.toPrismNDim.dilation L).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (k : Fin 3) :
    |(inner ℝ T.direction (Plank.pullbackNormal W κ g (P.basis k)) : ℝ)|
      ≤ 2 * (L : ℝ) * (P.thicknesses k : ℝ) := by
  have hx_mem : T.x ∈ (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr ⟨T.x, left_mem_segment ℝ T.x T.y,
      Metric.mem_closedBall_self (NNReal.coe_nonneg δ)⟩
  have hy_mem : T.y ∈ (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr ⟨T.y, right_mem_segment ℝ T.x T.y,
      Metric.mem_closedBall_self (NNReal.coe_nonneg δ)⟩
  have hfy : f T.y ∈ (P.toPrismNDim.dilation L).carrier := hsub ⟨T.y, hy_mem, rfl⟩
  have hfx : f T.x ∈ (P.toPrismNDim.dilation L).carrier := hsub ⟨T.x, hx_mem, rfl⟩
  have hby : |(inner ℝ (P.basis k) (f T.y - P.center) : ℝ)|
      ≤ (L : ℝ) * (P.thicknesses k : ℝ) := by
    have h := ((P.toPrismNDim.dilation L).mem_carrier_iff (f T.y)).1 hfy k
    simp only [PrismNDim.dilation, PrismNDim.basis_mk', PrismNDim.center_mk',
      PrismNDim.thicknesses_mk'] at h
    rw [OrthonormalBasis.repr_apply_apply, NNReal.coe_mul] at h
    exact h
  have hbx : |(inner ℝ (P.basis k) (f T.x - P.center) : ℝ)|
      ≤ (L : ℝ) * (P.thicknesses k : ℝ) := by
    have h := ((P.toPrismNDim.dilation L).mem_carrier_iff (f T.x)).1 hfx k
    simp only [PrismNDim.dilation, PrismNDim.basis_mk', PrismNDim.center_mk',
      PrismNDim.thicknesses_mk'] at h
    rw [OrthonormalBasis.repr_apply_apply, NNReal.coe_mul] at h
    exact h
  change |(inner ℝ (T.y - T.x) (Plank.pullbackNormal W κ g (P.basis k)) : ℝ)|
      ≤ 2 * (L : ℝ) * (P.thicknesses k : ℝ)
  rw [← Plank.inner_pullbackNormal_sub W hnorm (P.basis k) T.y T.x]
  rw [show f T.y - f T.x = (f T.y - P.center) - (f T.x - P.center) by abel]
  rw [inner_sub_left]
  simp_rw [real_inner_comm]
  calc
    |(inner ℝ (P.basis k) (f T.y - P.center) : ℝ)
        - (inner ℝ (P.basis k) (f T.x - P.center) : ℝ)|
      ≤ |(inner ℝ (P.basis k) (f T.y - P.center) : ℝ)|
          + |(inner ℝ (P.basis k) (f T.x - P.center) : ℝ)| := abs_sub _ _
    _ ≤ (L : ℝ) * (P.thicknesses k : ℝ)
        + (L : ℝ) * (P.thicknesses k : ℝ) := add_le_add hby hbx
    _ = 2 * (L : ℝ) * (P.thicknesses k : ℝ) := by ring

/-- **Part C3: the projective direction cap.**

A tube whose inner plank conflicts with that of `Ti` has its direction within `√2 · (176/κ) · δ` of
`± Ti.direction`.  The constant depends only on the fixed normalisation constant `κ`, not on
`a`, `b` or `δ`: the two anisotropic probe bounds `22δ/b`, `22δ/a` are paired with the two frame
norms `κ/b`, `κ/a` and divided by the area `≥ κ²/(4ab)`, and every occurrence of `a` and `b`
cancels. -/
theorem projective_cap_of_not_isEssentiallyDistinct
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ} (hκ : 0 < κ)
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : Plank.IsPlankNormalisation W f κ g) (ha : 0 < a)
    {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
    {δ : ℝ≥0} (hδ0 : 0 < δ) (ha'def : a' = δ / b) (hb'def : b' = δ / a)
    (Pi : Plank a' b' ha'b' hb'1)
    (Ti Tj : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hwi : ∀ k : Fin 3, |(inner ℝ Ti.direction (W.basis k) : ℝ)| ≤ 2 * (W.thicknesses k : ℝ))
    (halign : Pi.basis 2 = (‖f.linear Ti.direction‖)⁻¹ • (f.linear Ti.direction))
    (hortho : (inner ℝ (Pi.basis 0) (g 0) : ℝ) = 0)
    (hLu : f.linear Ti.direction ≠ 0)
    (hsub : (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ''
        (Tj.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ((Pi.toPrismNDim.dilation 11).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    min ‖Tj.direction - Ti.direction‖ ‖Tj.direction + Ti.direction‖
      ≤ Real.sqrt 2 * (176 / κ) * (δ : ℝ) := by
  -- notations for this proof
  let u : EuclideanSpace ℝ (Fin 3) := Ti.direction
  let q₀ : EuclideanSpace ℝ (Fin 3) := Plank.pullbackNormal W κ g (Pi.basis 0)
  let q₁ : EuclideanSpace ℝ (Fin 3) := Plank.pullbackNormal W κ g (Pi.basis 1)
  let w : EuclideanSpace ℝ (Fin 3) := Tj.direction
  let v : EuclideanSpace ℝ (Fin 3) := w - (inner ℝ u w : ℝ) • u
  -- the real-linear form of the long-axis alignment
  have hlin : f Ti.y - f Ti.x = f.linear (Ti.y - Ti.x) := by
    simpa using (AffineMap.linearMap_vsub f Ti.y Ti.x).symm
  have hlin' : f Ti.y - f Ti.x = f.linear Ti.direction := by
    simpa [Tube.direction] using hlin
  have halign' : Pi.basis 2 = (‖f Ti.y - f Ti.x‖)⁻¹ • (f Ti.y - f Ti.x) := by
    simpa [hlin'] using halign
  -- the two unit directions
  have hu : ‖u‖ = 1 := by
    simpa [u] using Ti.norm_direction
  have hw : ‖w‖ = 1 := by
    simpa [w] using Tj.norm_direction
  -- orthogonality of u with the two pullback normals
  have huq₀ : (inner ℝ u q₀ : ℝ) = 0 := by
    dsimp [u, q₀]
    exact inner_direction_pullbackNormal_eq_zero W hnorm Pi Ti halign'
      (show (0 : Fin 3) ≠ 2 by decide)
  have huq₁ : (inner ℝ u q₁ : ℝ) = 0 := by
    dsimp [u, q₁]
    exact inner_direction_pullbackNormal_eq_zero W hnorm Pi Ti halign'
      (show (1 : Fin 3) ≠ 2 by decide)
  -- scalar positivity
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (ha.trans_le hab)
  have haR_ne : (a : ℝ) ≠ 0 := ne_of_gt haR
  have hbR_ne : (b : ℝ) ≠ 0 := ne_of_gt hbR
  have hκ_ne : κ ≠ 0 := ne_of_gt hκ
  -- the area lower bound
  have hpa : κ ^ 2 / (4 * (a : ℝ) * (b : ℝ)) ≤ pullbackArea q₀ q₁ := by
    simpa [q₀, q₁] using le_pullbackArea W hκ hnorm ha Pi hu hwi halign hLu
  have hApos : 0 < pullbackArea q₀ q₁ := by
    have hq : 0 < κ ^ 2 / (4 * (a : ℝ) * (b : ℝ)) := by positivity
    exact lt_of_lt_of_le hq hpa
  -- the orthogonal part of w
  have hvu : (inner ℝ u v : ℝ) = 0 := by
    dsimp [v]
    have huu : (inner ℝ u u : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq, hu]
      norm_num
    rw [inner_sub_right, real_inner_smul_right, huu]
    ring
  obtain ⟨x, y, hvxy⟩ := exists_smul_add_smul_of_inner_eq_zero hu huq₀ huq₁ hApos hvu
  -- the Cramer estimate
  have hCr : ‖v‖ * pullbackArea q₀ q₁
      ≤ ‖q₀‖ * |(inner ℝ q₁ v : ℝ)| + ‖q₁‖ * |(inner ℝ q₀ v : ℝ)| :=
    norm_mul_pullbackArea_le hvxy
  -- ⟪qᵢ, v⟫ = ⟪qᵢ, w⟫ because ⟪qᵢ, u⟫ = 0
  have hq₀v : (inner ℝ q₀ v : ℝ) = inner ℝ q₀ w := by
    have hz : (inner ℝ q₀ u : ℝ) = 0 := by simpa [real_inner_comm] using huq₀
    dsimp [v]
    rw [inner_sub_right, real_inner_smul_right, hz]
    ring
  have hq₁v : (inner ℝ q₁ v : ℝ) = inner ℝ q₁ w := by
    have hz : (inner ℝ q₁ u : ℝ) = 0 := by simpa [real_inner_comm] using huq₁
    dsimp [v]
    rw [inner_sub_right, real_inner_smul_right, hz]
    ring
  -- the thicknesses of the inner plank
  have hth₀ : (Pi.thicknesses 0 : ℝ) = (δ : ℝ) / (b : ℝ) := by
    rw [Pi.thicknesses_eq, ha'def]
    simp
  have hth₁ : (Pi.thicknesses 1 : ℝ) = (δ : ℝ) / (a : ℝ) := by
    rw [Pi.thicknesses_eq, hb'def]
    simp
  -- probe bounds from the containment of Tj
  have probe₀ : |(inner ℝ q₀ w : ℝ)| ≤ 22 * ((δ : ℝ) / (b : ℝ)) := by
    calc
      |(inner ℝ q₀ w : ℝ)| = |(inner ℝ w q₀ : ℝ)| := by simp [real_inner_comm]
      _ ≤ 22 * (Pi.thicknesses 0 : ℝ) := by
        simpa [q₀, w] using (abs_inner_direction_pullbackNormal_le W hnorm Pi Tj hsub 0)
      _ = 22 * ((δ : ℝ) / (b : ℝ)) := by rw [hth₀]
  have probe₁ : |(inner ℝ q₁ w : ℝ)| ≤ 22 * ((δ : ℝ) / (a : ℝ)) := by
    calc
      |(inner ℝ q₁ w : ℝ)| = |(inner ℝ w q₁ : ℝ)| := by simp [real_inner_comm]
      _ ≤ 22 * (Pi.thicknesses 1 : ℝ) := by
        simpa [q₁, w] using (abs_inner_direction_pullbackNormal_le W hnorm Pi Tj hsub 1)
      _ = 22 * ((δ : ℝ) / (a : ℝ)) := by rw [hth₁]
  have hq₁abs : |(inner ℝ q₁ v : ℝ)| ≤ 22 * ((δ : ℝ) / (a : ℝ)) := by
    rw [hq₁v]
    exact probe₁
  have hq₀abs : |(inner ℝ q₀ v : ℝ)| ≤ 22 * ((δ : ℝ) / (b : ℝ)) := by
    rw [hq₀v]
    exact probe₀
  -- frame norms of the pull back normals
  have nq₀ : ‖q₀‖ ≤ κ / (b : ℝ) := by
    simpa [q₀] using norm_pullbackNormal_le_div_mid W hκ ha g (Pi.basis.norm_eq_one 0) hortho
  have nq₁ : ‖q₁‖ ≤ κ / (a : ℝ) := by
    simpa [q₁] using norm_pullbackNormal_le_div_thin W hκ ha g (Pi.basis.norm_eq_one 1)
  -- assemble the two anisotropic probe bounds against Cramer
  have amul₀ : ‖q₀‖ * |(inner ℝ q₁ v : ℝ)| ≤ (κ / (b : ℝ)) * (22 * ((δ : ℝ) / (a : ℝ))) :=
    mul_le_mul nq₀ hq₁abs (abs_nonneg (inner ℝ q₁ v)) (le_of_lt (div_pos hκ hbR))
  have amul₁ : ‖q₁‖ * |(inner ℝ q₀ v : ℝ)| ≤ (κ / (a : ℝ)) * (22 * ((δ : ℝ) / (b : ℝ))) :=
    mul_le_mul nq₁ hq₀abs (abs_nonneg (inner ℝ q₀ v)) (le_of_lt (div_pos hκ haR))
  have hsum : ‖q₀‖ * |(inner ℝ q₁ v : ℝ)| + ‖q₁‖ * |(inner ℝ q₀ v : ℝ)|
      ≤ (κ / (b : ℝ)) * (22 * ((δ : ℝ) / (a : ℝ)))
        + (κ / (a : ℝ)) * (22 * ((δ : ℝ) / (b : ℝ))) :=
    add_le_add amul₀ amul₁
  have hid : (κ / (b : ℝ)) * (22 * ((δ : ℝ) / (a : ℝ)))
        + (κ / (a : ℝ)) * (22 * ((δ : ℝ) / (b : ℝ)))
      = 44 * κ * (δ : ℝ) / ((a : ℝ) * (b : ℝ)) := by
    field_simp [haR_ne, hbR_ne, hκ_ne]
    ring
  have hmain : ‖v‖ * pullbackArea q₀ q₁ ≤ 44 * κ * (δ : ℝ) / ((a : ℝ) * (b : ℝ)) := by
    calc
      ‖v‖ * pullbackArea q₀ q₁
          ≤ ‖q₀‖ * |(inner ℝ q₁ v : ℝ)| + ‖q₁‖ * |(inner ℝ q₀ v : ℝ)| := hCr
      _ ≤ (κ / (b : ℝ)) * (22 * ((δ : ℝ) / (a : ℝ)))
            + (κ / (a : ℝ)) * (22 * ((δ : ℝ) / (b : ℝ))) := hsum
      _ = 44 * κ * (δ : ℝ) / ((a : ℝ) * (b : ℝ)) := hid
  have hstep : ‖v‖ * (κ ^ 2 / (4 * (a : ℝ) * (b : ℝ)))
      ≤ 44 * κ * (δ : ℝ) / ((a : ℝ) * (b : ℝ)) :=
    (mul_le_mul_of_nonneg_left hpa (norm_nonneg v)).trans hmain
  have hscaled : (‖v‖ * (κ ^ 2 / (4 * (a : ℝ) * (b : ℝ)))) * (4 * (a : ℝ) * (b : ℝ) / κ)
      ≤ (44 * κ * (δ : ℝ) / ((a : ℝ) * (b : ℝ))) * (4 * (a : ℝ) * (b : ℝ) / κ) :=
    mul_le_mul_of_nonneg_right hstep (by positivity)
  have hL : (‖v‖ * (κ ^ 2 / (4 * (a : ℝ) * (b : ℝ)))) * (4 * (a : ℝ) * (b : ℝ) / κ) = ‖v‖ * κ := by
    field_simp [haR_ne, hbR_ne, hκ_ne]
  have hR : ((44 * κ * (δ : ℝ)) / ((a : ℝ) * (b : ℝ))) *
      (4 * (a : ℝ) * (b : ℝ) / κ) = 176 * (δ : ℝ) := by
    field_simp [haR_ne, hbR_ne, hκ_ne]
    norm_num
  have hmed : ‖v‖ * κ ≤ 176 * (δ : ℝ) := by
    rw [← hL, ← hR]
    exact hscaled
  have hv1 : ‖v‖ ≤ 176 * (δ : ℝ) / κ := (le_div_iff₀ hκ).mpr hmed
  have hvF : ‖v‖ ≤ (176 / κ) * (δ : ℝ) := by
    calc
      ‖v‖ ≤ 176 * (δ : ℝ) / κ := hv1
      _ = (176 / κ) * (δ : ℝ) := by ring
  -- the projective cap: apply projective_cap_of_orthogonal_le with `v - ⟪u,v⟫•u`
  set r : ℝ := (176 / κ) * (δ : ℝ) with hr
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hproj : ‖w - (inner ℝ u w : ℝ) • u‖ ≤ r := by
    simpa [v, hr] using hvF
  /- BEGIN DISABLED (inlined projective-cap block removed via EDDegree lemma)
  have hcap : min ‖w - u‖ ‖w + u‖ ≤ Real.sqrt 2 * r := by
    -- (removed inline projective cap)
    -- removed
      -- removed
    -- removed
      -- removed
    · have hm2le2 : m ^ 2 ≤ 2 := by
        calc
          m ^ 2 ≤ 2 - 2 * |c| := hm2_abs
          _ ≤ 2 := by nlinarith [abs_nonneg c]
      have hr2 : 1 ≤ r ^ 2 := by nlinarith [h1, hr0]
      have hm2le : m ^ 2 ≤ 2 * r ^ 2 := by nlinarith [hm2le2, hr2, hr0]
      have hm2le' : m ^ 2 ≤ (Real.sqrt 2 * r) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        exact hm2le
      have hsqrt_nonneg : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg 2) hr0
      have h_abs : |m| ≤ |Real.sqrt 2 * r| := sq_le_sq.mp hm2le'
      rwa [abs_of_nonneg hm_nonneg, abs_of_nonneg hsqrt_nonneg] at h_abs
    · have hr1 : r < 1 := lt_of_not_ge h1
      have h1r2 : 0 ≤ 1 - r ^ 2 := by nlinarith [hr0, hr1]
      have hw2 : ‖pv‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg pv) hproj 2
      have hc2le : 1 - r ^ 2 ≤ c ^ 2 := by nlinarith [hc2, hw2]
      have hcabs : Real.sqrt (1 - r ^ 2) ≤ |c| := by
        have htmp : Real.sqrt (1 - r ^ 2) ≤ Real.sqrt (c ^ 2) :=
          Real.sqrt_le_sqrt hc2le
        rw [Real.sqrt_sq_eq_abs] at htmp
        exact htmp
      have hs_nonneg : 0 ≤ Real.sqrt (1 - r ^ 2) := Real.sqrt_nonneg _
      have hs_le1 : Real.sqrt (1 - r ^ 2) ≤ 1 :=
        (Real.sqrt_le_one).2 (by nlinarith [hr0, hr1])
      have hsq_le : Real.sqrt (1 - r ^ 2) ^ 2 ≤ Real.sqrt (1 - r ^ 2) := by
        nlinarith [hs_nonneg, hs_le1]
      have hmain : 2 - 2 * Real.sqrt (1 - r ^ 2) ≤ 2 * r ^ 2 := by
        have hsq : Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt h1r2
        nlinarith [hsq, hsq_le]
      have hm2le : m ^ 2 ≤ 2 * r ^ 2 := by
        calc
          m ^ 2 ≤ 2 - 2 * |c| := hm2_abs
          _ ≤ 2 - 2 * Real.sqrt (1 - r ^ 2) := by nlinarith [hcabs]
          _ ≤ 2 * r ^ 2 := hmain
      have hm2le' : m ^ 2 ≤ (Real.sqrt 2 * r) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        exact hm2le
      have hsqrt_nonneg : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg 2) hr0
      have h_abs : |m| ≤ |Real.sqrt 2 * r| := sq_le_sq.mp hm2le'
      rwa [abs_of_nonneg hm_nonneg, abs_of_nonneg hsqrt_nonneg] at h_abs
  -/
  have hcap : min ‖w - u‖ ‖w + u‖ ≤ Real.sqrt 2 * r := by
    exact projective_cap_of_orthogonal_le (r := r) hu hw hr0 hproj
  dsimp [u, w, r] at hcap
  simpa [u, w, mul_assoc] using hcap

/-- The linear part of an affine map that agrees with an affine equivalence is injective. -/
theorem linear_ne_zero_of_affineEquiv_eq
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)}
    {F : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} (hF : ∀ x, F x = f x)
    {w : EuclideanSpace ℝ (Fin 3)} (hw : w ≠ 0) : f.linear w ≠ 0 := by
  intro h0
  apply hw
  have hfw : f w = f 0 := by
    have := AffineMap.map_vadd f (0 : EuclideanSpace ℝ (Fin 3)) w
    simp [h0] at this
    simpa using this
  have : F w = F 0 := by
    rw [hF w, hF 0]
    exact hfw
  simpa using F.injective this

/-- A `δ`-tube inside the plank `W` has its core direction bounded by twice each half-width in
`W`'s own frame: both endpoints lie in `W`. -/
theorem abs_inner_direction_basis_le_of_subset
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (W : Plank a b hab hb1) {δ : ℝ≥0}
    (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hT : (T.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))) (k : Fin 3) :
    |(inner ℝ T.direction (W.basis k) : ℝ)| ≤ 2 * (W.thicknesses k : ℝ) := by
  have hx_mem : T.x ∈ (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr ⟨T.x, left_mem_segment ℝ T.x T.y,
      Metric.mem_closedBall_self (NNReal.coe_nonneg δ)⟩
  have hy_mem : T.y ∈ (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr ⟨T.y, right_mem_segment ℝ T.x T.y,
      Metric.mem_closedBall_self (NNReal.coe_nonneg δ)⟩
  have h := abs_repr_vsub_le_two_mul_thicknesses W.toPrismNDim (hT hy_mem) (hT hx_mem) k
  rwa [W.basis.repr_apply_apply, vsub_eq_sub, real_inner_comm] at h

/-! ### Part D: the conflict degree -/

/-- **The inner-plank conflict degree is absolutely bounded.**

Every member of the normalised inner plank family at scales `a' = δ/b`, `b' = δ/a` fails to be
essentially distinct from at most `d` others, with `d` and the smallness threshold `δ₀` depending
only on the fixed normalisation constant `κ` — not on `a`, `b`, `δ`, the index set, or the member.

The count is performed on the *original* fine tubes, which are pairwise essentially distinct.  A
plank conflict puts the conflicting tube in the fixed pullback container `f⁻¹(11 · Pᵢ)` (Part A) of
volume `(10648/κ³)·δ²` (Part B), and forces its direction into a single projective cap of radius
`√2·(176/κ)·δ` (Part C).  Those are exactly the hypotheses of
`Kakeya.exists_ED_directionCap_degree_bound`, whose bound is free of `δ`.

This is the input consumed by `Kakeya.exists_inner_plank_ED_subfamily_weighted`. -/
theorem exists_inner_plank_conflict_degree_bound {κ : ℝ} (hκ : 0 < κ) :
    ∃ d : ℕ, 0 < d ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type*} {a b δ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (_ha : 0 < a) (_hδ0 : 0 < δ) (_hδle : (δ : ℝ) ≤ δ₀)
        {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
        (_ha'def : a' = δ / b) (_hb'def : b' = δ / a)
        (W : Plank a b hab hb1) (q : Finset ι)
        (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
        (P : ι → Plank a' b' ha'b' hb'1)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
        (F : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0)
        (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
        (_hF : ∀ x, F x = f x) (_hJ : 0 < J)
        (_hnorm : Plank.IsPlankNormalisation W f κ g)
        (_hJab : J * (a * b) = Real.toNNReal κ ^ 3)
        (_hvolf : ∀ E : Set (EuclideanSpace ℝ (Fin 3)),
            volume ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E)
              = (J : ENNReal) * volume E)
        (_hcarrier : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))))
        (_himg : ∀ i ∈ q, (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ''
            ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
              ⊆ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
        (_halign : ∀ i ∈ q, (P i).basis 2
            = (‖f.linear (T i).direction‖)⁻¹ • (f.linear (T i).direction))
        (_hortho : ∀ i ∈ q, (inner ℝ ((P i).basis 0) (g 0) : ℝ) = 0)
        (_hED : (q : Set ι).Pairwise
            (fun i j => _root_.IsEssentiallyDistinct
              ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
              ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3))))),
        ∀ i ∈ q,
          edConflictDegree q (fun j => ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) i ≤ d := by
  classical
  have hn : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hA : 0 < Real.sqrt 2 * (176 / κ) := by
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) (div_pos (by norm_num) hκ)
  have hM : 0 < (((innerPullbackVolumeConst κ : ℝ≥0) : ℝ)) := by
    unfold innerPullbackVolumeConst
    rw [NNReal.coe_div, NNReal.coe_pow]
    exact div_pos (by norm_num) (pow_pos (NNReal.coe_pos.mpr (Real.toNNReal_pos.mpr hκ)) 3)
  have hc : 0 < (1 : ℝ) := by norm_num
  obtain ⟨d₀, δ₀, hδ_pos, hδ_le1, hcount⟩ :=
    exists_ED_directionCap_degree_bound (E := EuclideanSpace ℝ (Fin 3))
      (A := Real.sqrt 2 * (176 / κ))
      (M := (((innerPullbackVolumeConst κ : ℝ≥0) : ℝ))) (c := 1)
      hn hA hM hc
  refine ⟨max d₀ 1, ?_, δ₀, hδ_pos, hδ_le1, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (Nat.le_max_right d₀ 1)
  · intro ι a b δ hab hb1 ha hδ0 hδle a' b' ha'b' hb'1 ha'def hb'def W q T P f F J g
      hF hJ hnorm hJab hvolf hcarrier himg halign hortho hED
    intro i hi
    let s : Finset ι := q.filter (fun j : ι =>
      ¬ _root_.IsEssentiallyDistinct ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    let K : Set (EuclideanSpace ℝ (Fin 3)) :=
      (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹'
        (((P i).toPrismNDim.dilation 11).carrier : Set (EuclideanSpace ℝ (Fin 3)))
    have hb : 0 < b := lt_of_lt_of_le ha hab
    -- 1. pairwise ED on s
    have hED_s : (s : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct
          ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
      exact Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.filter_subset _ q)) hED
    -- 2. direction cap
    have hcap : ∀ j ∈ s,
        min ‖(T j).direction - (T i).direction‖ ‖(T j).direction + (T i).direction‖
          ≤ (Real.sqrt 2 * (176 / κ)) * (δ : ℝ) := by
      intro j hj
      have hjq : j ∈ q := (Finset.mem_filter.mp hj).1
      have hnd : ¬ _root_.IsEssentiallyDistinct ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3))) := (Finset.mem_filter.mp hj).2
      have hsub : (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ''
            ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ ((P i).toPrismNDim.dilation 11).carrier := by
        exact (himg j hjq).trans (large_overlap_plank_subset_dilation (P i) (P j) hnd)
      exact projective_cap_of_not_isEssentiallyDistinct W hκ hnorm ha
        hδ0 ha'def hb'def (P i) (T i) (T j)
        (abs_inner_direction_basis_le_of_subset W (T i) (hcarrier i hi))
        (halign i hi) (hortho i hi)
        (linear_ne_zero_of_affineEquiv_eq hF (fun h => by simpa [h] using (T i).norm_direction))
        hsub
    -- 3. compactness and measurability of K
    have hK_cpt : IsCompact K := by
      dsimp [K]
      exact isCompact_preimage_affineEquiv F ((P i).toPrismNDim.dilation 11).isCompact
    have hK_meas : MeasurableSet K := hK_cpt.isClosed.measurableSet
    -- 4. volume
    have hvolK : volume K = (innerPullbackVolumeConst κ : ENNReal) * (δ : ENNReal) ^ 2 := by
      dsimp [K]
      exact volume_preimage_dilation_inner_plank ha hb hκ ha'def hb'def (P i) hJ hJab hvolf
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1 = 2 := by
      rw [finrank_euclideanSpace_fin]
    have hK_vol : volume K ≤ ENNReal.ofReal (((innerPullbackVolumeConst κ : ℝ≥0) : ℝ)) *
        (δ : ENNReal) ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) := by
      rw [hfin]
      rw [ENNReal.ofReal_coe_nnreal]
      exact le_of_eq hvolK
    -- 5. badness
    have hbad : ∀ j ∈ s,
        volume ((T j).carrier ∩ K) ≥ ENNReal.ofReal 1 * volume (T j).carrier := by
      intro j hj
      have hjq : j ∈ q := (Finset.mem_filter.mp hj).1
      have hnd : ¬ _root_.IsEssentiallyDistinct ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3))) := (Finset.mem_filter.mp hj).2
      have hsub : (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ''
            ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ ((P i).toPrismNDim.dilation 11).carrier := by
        exact (himg j hjq).trans (large_overlap_plank_subset_dilation (P i) (P j) hnd)
      have hsubK : ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ K := by
        dsimp [K]
        intro x hx
        rw [Set.mem_preimage]
        have hfx : f x ∈ ((P i).toPrismNDim.dilation 11).carrier := hsub ⟨x, hx, rfl⟩
        simpa [hF x] using hfx
      rw [Set.inter_eq_left.mpr hsubK]
      simp [ENNReal.ofReal_one]
    -- apply hcount
    have hcount' : s.card ≤ d₀ := by
      refine hcount (δ := δ) hδ0 hδle (s := s) (T := T) ?_ (e := (T i).direction) ?_ ?_
        (K := K) ?_ ?_ ?_ ?_
      · exact hED_s
      · exact (T i).norm_direction
      · exact hcap
      · exact hK_meas
      · exact hK_cpt
      · exact hK_vol
      · exact hbad
    have hs_le : s.card ≤ max d₀ 1 := le_trans hcount' (le_max_left d₀ 1)
    have hs : edConflictDegree q (fun j => ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) i
        = s.card := by
      unfold edConflictDegree
      congr 1
    exact hs ▸ hs_le

/-- **Alignment, restated on the linear part.**

`Kakeya.innerShadedPlankFamily` exports the long-axis alignment in terms of the affine displacement
`f T.y - f T.x`, while `Kakeya.exists_inner_plank_conflict_degree_bound` consumes it in terms of
`f.linear T.direction`.  The two agree: an affine map sends a difference to its linear part applied
to the difference, and a tube's core direction is `T.y - T.x` by definition. -/
theorem align_linear_of_align_sub
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)}
    {δ : ℝ≥0} (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1} (P : Plank a' b' ha'b' hb'1)
    (h : P.basis 2 = (‖f T.y - f T.x‖)⁻¹ • (f T.y - f T.x)) :
    P.basis 2 = (‖f.linear T.direction‖)⁻¹ • (f.linear T.direction) := by
  have hkey : f T.y - f T.x = f.linear T.direction := by
    simpa [Tube.direction] using (AffineMap.linearMap_vsub f T.y T.x).symm
  rw [← hkey]
  exact h

end Kakeya

end

end
