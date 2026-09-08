/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabFibreGeometry

/-!
# The concrete normalised tube family of a slab fibre

`Plank.slabFibreTubes` is *the* family of shaded `b/8`-tubes attached to a slab fibre: the
`Kakeya/DimensionThree/Plank/SlabTube` family `Plank.slabTubeFamily` run at the fibre's own
conversion constant `Plank.fibreTubeConst`, with the fibre itself as index set and the identity as
the plank map. Off the fibre it is the fixed shadeless `Plank.defaultShadedTube`, which is what lets
the unit-ball clause be stated for *every* index — the form
`Kakeya.FrostmanEstimate.multiplicity_bound` demands.

Making the family concrete (rather than existentially quantified inside
`Plank.normaliseSlabFamilyToTubes`) is what lets the anisotropic ED-packing bridge of
`Kakeya.DimensionThree.Plank.SlabTubeSelection` — which is stated for
`Q.slabTube S (fibreTubeConst Cfib) …` — be applied to it: `Plank.slabFibreTubes_toTube` says the
two agree on the fibre, definitionally.

Each clause of the normalisation is proved here as a separate lemma, so that
`Plank.normaliseSlabFamilyToTubes` is a short assembly.
-/

@[expose] public section

open MeasureTheory Kakeya
open scoped NNReal Real Classical

noncomputable section

namespace Plank

variable {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}

/-- The affine equivalence normalising a slab fibre: `Slab.normalizeScaled` at the fibre's own
conversion constant `Plank.fibreTubeConst`. -/
def slabFibreNormalisation (Cfib : ℝ≥0) (S : Slab θ hθ1) (hθ0 : 0 < θ) :
    EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  Slab.normalizeScaled S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)

/-- The concrete family of shaded `b/8`-tubes attached to a slab fibre. -/
def slabFibreTubes (Cfib : ℝ≥0) (fibre : Finset (ThickenedPlank θ b hθ1 hb1))
    (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (S : Slab θ hθ1) (hθ0 : 0 < θ) :
    ThickenedPlank θ b hθ1 hb1 → ShadedTube (b / 8) (EuclideanSpace ℝ (Fin 3)) :=
  slabTubeFamily fibre (fun Q => Q) Yθ S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)

/-- The fixed fullness/volume loss of the slab-fibre normalisation:
`40 (1 + 3 Cfib)³ (1 + Cfib)³`, the constant of `Plank.fullness'_le_ktTubeFamily` at
`Cang = 3 Cfib`, `Cset = Cdil = Cfib`. -/
def fibreTubeLoss (Cfib : ℝ≥0) : ℝ≥0 := 40 * (1 + 3 * Cfib) ^ 3 * (1 + Cfib) ^ 3

/-- `Plank.fibreTubeLoss` is at least one. -/
theorem one_le_fibreTubeLoss (Cfib : ℝ≥0) : 1 ≤ fibreTubeLoss Cfib := by
  unfold fibreTubeLoss
  have h1 : (1 : ℝ≥0) ≤ 1 + 3 * Cfib := le_self_add
  have h2 : (1 : ℝ≥0) ≤ 1 + Cfib := le_self_add
  have h40 : (1 : ℝ≥0) ≤ 40 := by norm_num
  have hpow1 : (1 : ℝ≥0) ≤ (1 + 3 * Cfib) ^ 3 := one_le_pow₀ h1
  have hpow2 : (1 : ℝ≥0) ≤ (1 + Cfib) ^ 3 := one_le_pow₀ h2
  have hpow : (1 : ℝ≥0) ≤ (1 + 3 * Cfib) ^ 3 * (1 + Cfib) ^ 3 := one_le_mul hpow1 hpow2
  calc
    (1 : ℝ≥0) ≤ 40 * ((1 + 3 * Cfib) ^ 3 * (1 + Cfib) ^ 3) := one_le_mul h40 hpow
    _ = 40 * (1 + 3 * Cfib) ^ 3 * (1 + Cfib) ^ 3 := by ring

variable {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
  {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
  {S : Slab θ hθ1} {Cfib : ℝ≥0}

/-- **On the fibre, the concrete family's underlying tube is `Plank.slabTube`.** This is what makes
the anisotropic ED-packing bridge of `Kakeya.DimensionThree.Plank.SlabTubeSelection`, stated for
`Q.slabTube S (fibreTubeConst Cfib) …`, applicable to `Plank.slabFibreTubes`. -/
theorem slabFibreTubes_toTube (hθ0 : 0 < θ) {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre) :
    (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toTube
      = Q.slabTube S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib) := by
  rw [slabFibreTubes, slabTubeFamily, if_pos hQ]
  rfl

/-- Carrier form of `Plank.slabFibreTubes_toTube`. -/
theorem slabFibreTubes_carrier (hθ0 : 0 < θ) {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre) :
    ((slabFibreTubes Cfib fibre Yθ S hθ0 Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((Q.slabTube S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) := by
  rw [← slabFibreTubes_toTube (Cfib := Cfib) hθ0 hQ]

/-- The `Cfib`-dilated shading body of a fibre prism is the `Cfib`-dilation of its `θ`-thickening —
the form the `Kakeya/DimensionThree/Plank/DilatedSlabTube` interface consumes. -/
theorem slabFibre_shade_body_thickened (h : SlabFibreGeometry fibre Yθ S Cfib)
    {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre) :
    ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (((Q.thickened θ hθ1).toPrismNDim.dilation Cfib).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) := by
  rw [Plank.dilation_thickened_self_eq]
  exact h.shade_body Q hQ

/-- **(1)** Every tube of the concrete family lies in the closed unit ball — at *every* index, not
only on the fibre, because off the fibre the family is `Plank.defaultShadedTube`. -/
theorem slabFibreTubes_carrier_subset_closedBall (h : SlabFibreGeometry fibre Yθ S Cfib)
    (hCfib : 1 ≤ Cfib) (hθ0 : 0 < θ) (Q : ThickenedPlank θ b hθ1 hb1) :
    ((slabFibreTubes Cfib fibre Yθ S hθ0 Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1 := by
  have hmem : ∀ P ∈ fibre, P ∈ inSlabFamilyC Cfib (3 * Cfib) fibre (fun Q => Q) S :=
    fun P hP => h.mem_slabFamilyC hP
  simpa [slabFibreTubes, fibreTubeConst] using
    ktTubeFamily_carrier_subset_closedBall (Cset := Cfib) (Cang := 3 * Cfib) (Cdil := Cfib)
      (s := fibre) (V := fun Q => Q) (Y := Yθ) (S := S) hθ0 hCfib hmem Q

/-- **(2)** On the fibre the tubes carry exactly the transported shadings. -/
theorem slabFibreTubes_shade (h : SlabFibreGeometry fibre Yθ S Cfib) (hCfib : 1 ≤ Cfib)
    (hθ0 : 0 < θ) {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre) :
    (slabFibreTubes Cfib fibre Yθ S hθ0 Q).shade
      = slabFibreNormalisation Cfib S hθ0 '' (Yθ Q).shade := by
  have hmem : ∀ P ∈ fibre, P ∈ inSlabFamilyC Cfib (3 * Cfib) fibre (fun Q => Q) S :=
    fun P hP => h.mem_slabFamilyC hP
  have hcar : ∀ P ∈ fibre, ((Yθ P).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (((P.thickened θ hθ1).toPrismNDim.dilation Cfib).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) :=
    fun P hP => (slabFibre_shade_body_thickened h hP).le
  simpa [slabFibreTubes, slabFibreNormalisation, fibreTubeConst] using
    ktTubeFamily_shade (Cset := Cfib) (Cang := 3 * Cfib) (Cdil := Cfib)
      (s := fibre) (V := fun Q => Q) (Y := Yθ) (S := S) hθ0 hCfib hmem hcar hQ

/-- **(3)** The normalised core sits inside its own tube. -/
theorem slabFibreTubes_core_subset (h : SlabFibreGeometry fibre Yθ S Cfib) (hCfib : 1 ≤ Cfib)
    (hθ0 : 0 < θ) {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre) :
    slabFibreNormalisation Cfib S hθ0 '' (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ((slabFibreTubes Cfib fibre Yθ S hθ0 Q).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  rw [slabFibreTubes_carrier hθ0 hQ]
  change Slab.normalizeScaled S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib) ''
      (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
    ⊆ (Q.slabTube S (fibreTubeConst Cfib) hθ0 (fibreTubeConst_pos Cfib)).carrier
  exact SlabFibreGeometry.image_subset_slabTube h hCfib hθ0 hQ
    (PrismNDim.self_subset_dilation Q.toPrismNDim hCfib)

/-- **(4)** The normalised cores are pairwise essentially distinct: essential distinctness of the
undilated fibre prisms is an affine invariant. -/
theorem slabFibreTubes_pairwise_core_ED (h : SlabFibreGeometry fibre Yθ S Cfib) (hθ0 : 0 < θ) :
    (↑fibre : Set (ThickenedPlank θ b hθ1 hb1)).Pairwise
      (fun Q Q' => _root_.IsEssentiallyDistinct
        (slabFibreNormalisation Cfib S hθ0 '' (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))))
        (slabFibreNormalisation Cfib S hθ0 '' (Q'.carrier : Set (EuclideanSpace ℝ (Fin 3))))) := by
  intro Q hQ Q' hQ' hne
  have hED : _root_.IsEssentiallyDistinct (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      (Q'.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    simpa [PrismNDim.IsEssentiallyDistinct] using
      h.pairwise_essentiallyDistinct hQ hQ' hne
  exact IsEssentiallyDistinct.image_affineEquiv (slabFibreNormalisation Cfib S hθ0) hED

/-- **(5)** The multiplicity is preserved exactly. -/
theorem slabFibreTubes_multiplicity (h : SlabFibreGeometry fibre Yθ S Cfib) (hCfib : 1 ≤ Cfib)
    (hθ0 : 0 < θ) :
    ShadedBody.multiplicity fibre (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toShadedBody)
      = ShadedBody.multiplicity fibre Yθ := by
  have hmem : ∀ P ∈ fibre, P ∈ inSlabFamilyC Cfib (3 * Cfib) fibre (fun Q => Q) S :=
    fun P hP => h.mem_slabFamilyC hP
  have hcar : ∀ P ∈ fibre,
      ((Yθ P).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (((P.thickened θ hθ1).toPrismNDim.dilation Cfib).carrier :
            Set (EuclideanSpace ℝ (Fin 3))) :=
    fun P hP => (slabFibre_shade_body_thickened h hP).le
  simpa [slabFibreTubes, fibreTubeConst] using
    multiplicity_ktTubeFamily (Cset := Cfib) (Cang := 3 * Cfib) (Cdil := Cfib)
      (s := fibre) (V := fun Q => Q) (Y := Yθ) (S := S) hθ0 hCfib hmem hcar

/-- **(6)** Fullness is preserved up to the fixed loss `Plank.fibreTubeLoss`. -/
theorem slabFibreTubes_fullness (h : SlabFibreGeometry fibre Yθ S Cfib) (hCfib : 1 ≤ Cfib)
    (hθ0 : 0 < θ) (hb0 : 0 < b) :
    (fibreTubeLoss Cfib)⁻¹ * ShadedBody.fullness fibre Yθ
      ≤ ShadedBody.fullness fibre
          (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toShadedBody) := by
  let C : ENNReal :=
    40 * (1 + ((3 * Cfib : ℝ≥0) : ENNReal)) ^ 3 * (1 + ((Cfib : ℝ≥0) : ENNReal)) ^ 3
  let T : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toShadedBody
  have hkt : ShadedBody.fullness' fibre Yθ ≤ C * ShadedBody.fullness' fibre T := by
    change ShadedBody.fullness' fibre Yθ ≤
      (40 * (1 + ((3 * Cfib : ℝ≥0) : ENNReal)) ^ 3 * (1 + ((Cfib : ℝ≥0) : ENNReal)) ^ 3) *
        ShadedBody.fullness' fibre (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toShadedBody)
    simpa [slabFibreTubes, fibreTubeConst] using
      (fullness'_le_ktTubeFamily (Cset := Cfib) (Cang := 3 * Cfib) (Cdil := Cfib)
        (s := fibre) (V := fun Q => Q) (Y := Yθ) (S := S) hθ0 hb0 hCfib
          (fun Q hQ => h.mem_slabFamilyC hQ)
          (fun Q hQ => slabFibre_shade_body_thickened h hQ))
  have hC : ((fibreTubeLoss Cfib : ℝ≥0) : ENNReal) = C := by
    simp [C, fibreTubeLoss]
  have hC0' : (fibreTubeLoss Cfib : ℝ≥0) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_fibreTubeLoss Cfib))
  have hC0 : C ≠ 0 := by
    rw [← hC]
    exact ENNReal.coe_ne_zero.mpr hC0'
  have hCtop : C ≠ ⊤ := by
    rw [← hC]
    exact ENNReal.coe_ne_top
  have hdiv : C⁻¹ * ShadedBody.fullness' fibre Yθ ≤ ShadedBody.fullness' fibre T := by
    calc
      C⁻¹ * ShadedBody.fullness' fibre Yθ
          ≤ C⁻¹ * (C * ShadedBody.fullness' fibre T) := by
            gcongr
      _ = ShadedBody.fullness' fibre T := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hCtop, one_mul]
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.coe_mul]
  rw [ENNReal.coe_inv hC0']
  rw [hC]
  rw [ShadedBody.coe_fullness]
  rw [ShadedBody.coe_fullness]
  exact hdiv

/-- **(7)** The union of shades transports exactly, with the affine Jacobian. -/
theorem slabFibreTubes_volume_iUnion_shade (h : SlabFibreGeometry fibre Yθ S Cfib)
    (hCfib : 1 ≤ Cfib) (hθ0 : 0 < θ) :
    volume (⋃ Q ∈ fibre, (slabFibreTubes Cfib fibre Yθ S hθ0 Q).shade)
      = Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0)
          * volume (⋃ Q ∈ fibre, (Yθ Q).shade) := by
  have hU : (⋃ Q ∈ fibre, (slabFibreTubes Cfib fibre Yθ S hθ0 Q).shade)
      = (slabFibreNormalisation Cfib S hθ0) '' (⋃ Q ∈ fibre, (Yθ Q).shade) := by
    rw [Set.image_iUnion₂]
    exact Set.iUnion₂_congr fun Q hQ => slabFibreTubes_shade h hCfib hθ0 hQ
  rw [hU, Kakeya.volume_image_affineEquiv]

end Plank

end
