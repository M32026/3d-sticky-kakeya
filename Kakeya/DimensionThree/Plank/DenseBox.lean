/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabIntersection
public import Kakeya.DimensionThree.Plank.BoxRescaling
public import Kakeya.DimensionThree.Slab.Incidence

/-!
# Dense-box estimates for GWZ Lemma 6.13

The public interface consists of three estimates, in increasing distance from the geometry:

* `denseBox_core_raw` — the choice-free geometric core, stated for an **arbitrary**
  `Q : ThetaBox θ b hθ1`;
* `denseBoxEstimate_boxNormalised_raw` — the same estimate with the base points constructed from
  tangentiality, before any exponent cancellation;
* `denseBoxEstimate_boxNormalised` and `denseBoxEstimate_boxNormalised_combined` — the two
  Lemma 6.13-facing corollaries, obtained by applying different exponent cancellations to that one
  output.

Nothing here is specialised to `Plank.shiftedSlabBox`: the grid box is only ever an instance of the
generic `ThetaBox`.  The construction/algebra machinery (rescaled outer shaded-slab construction,
slab-angle/plank-angle identity, fullness scaling, typical-intersection transfer, `rpow` algebra) is
private.  The downstream refinements, thickened-shading density, assembly package, and multiplicity
algebra live in the companion file `Kakeya.DimensionThree.Plank.ShadingTransport`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real

noncomputable section

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}

/-! ## Dense boxes and dense balls (`def:denseBoxLayerAPI`, `lem:denseBoxEstimate`) -/

/-- **`a^{2η}·M ≤ 1` from the multiplicity bound** (internal algebra step of the weighted
dense-box estimate).  Pure exponent arithmetic: `a^{2η}·M ≤ a^{2η}·a^{-2η} = a^0 = 1`. -/
private theorem aRpow_two_mul_M_le_one {a : ℝ≥0} {η : ℝ} (hη : 0 < η) (M : ENNReal)
    (hM : M ≤ (a : ENNReal) ^ (-(2 * η))) :
    (a : ENNReal) ^ (2 * η) * M ≤ 1 := by
  by_cases ha0 : a = 0
  · subst ha0
    have h2ηpos : 0 < 2 * η := by nlinarith
    simp [ENNReal.zero_rpow_of_pos h2ηpos]
  · have ha_ne_zero : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha0
    have ha_ne_top : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    calc
      (a : ENNReal) ^ (2 * η) * M
          ≤ (a : ENNReal) ^ (2 * η) * ((a : ENNReal) ^ (-(2 * η))) := mul_le_mul_right hM _
      _ = (a : ENNReal) ^ ((2 * η) + (-(2 * η))) := by
        rw [ENNReal.rpow_add (2 * η) (-(2 * η)) ha_ne_zero ha_ne_top]
      _ = (a : ENNReal) ^ (0 : ℝ) := by norm_num
      _ = 1 := by simp

/-- **`a^η·M ≤ K` from a product bound `M ≤ K·a^{-η}`** (internal algebra step of the *combined*
dense-box estimate).  The single-exponent analogue of `Plank.aRpow_two_mul_M_le_one`, used with
`M := Cstar·Mtyp`: only one factor `a^η` is spent, because the honest datum coming out of the
angular concentration bounds the *product* `Cstar·Mtyp` by `K·a^{-η}` rather than bounding `Mtyp`
alone by `a^{-2η}`. -/
private theorem aRpow_mul_prod_le {a : ℝ≥0} {η : ℝ} (hη : 0 < η) (K : ℝ≥0) (M : ENNReal)
    (hM : M ≤ (K : ENNReal) * (a : ENNReal) ^ (-η)) :
    (a : ENNReal) ^ η * M ≤ (K : ENNReal) := by
  by_cases ha0 : a = 0
  · subst ha0
    have hηpos : 0 < η := hη
    simp [ENNReal.zero_rpow_of_pos hηpos]
  · have ha_ne_zero : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha0
    have ha_ne_top : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    calc
      (a : ENNReal) ^ η * M
          ≤ (a : ENNReal) ^ η * ((K : ENNReal) * (a : ENNReal) ^ (-η)) := mul_le_mul_right hM _
      _ = (K : ENNReal) * ((a : ENNReal) ^ η * (a : ENNReal) ^ (-η)) := by ring
      _ = (K : ENNReal) * ((a : ENNReal) ^ (η + (-η))) := by
        rw [ENNReal.rpow_add η (-η) ha_ne_zero ha_ne_top]
      _ = (K : ENNReal) * ((a : ENNReal) ^ (0 : ℝ)) := by ring_nf
      _ = (K : ENNReal) * 1 := by simp
      _ = (K : ENNReal) := by simp

/-- **Rescaled outer shaded slab from a plank–box intersection** (`lem:denseBoxOuterShadedSlabs`
combined with the isotropic rescaling, steps A–B), *parameterised by the dilation constant* `D`.
For any `D > 0`, the homothety `h := homothety Q.center (D·b)⁻¹` sends the enlarged outer model
`σ.dilation D` (a `Da × Db × Db` prism sharing `P`'s axes) *onto* a genuine `Slab (a/b)` — its
`1 × 1` cross-section coming from `(D·b)⁻¹ · D·b = 1`, independently of `D` — and carries any shade
`sh ⊆ (σ.dilation D).carrier` into that slab.  The dilation `D` is exactly the `Cset` produced
(existentially) by `plankBoxIntersectionIsSlab`, so `D` is the abstract `Cset` seen by the
consumer.  It packages the pushforward as an honest
`ShadedSlab (a/b)` whose carrier is the image slab, whose shade is `h '' sh`, and whose axes are
`P`'s axes (so pairwise slab angles reduce to plank plane angles). -/
private theorem exists_rescaled_shadedSlab_dilation (P : Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1)
    (Q : ThetaBox θ b hθ1) (hb : 0 < b) (hδ1 : a / b ≤ 1)
    (D : ℝ≥0) (hD : 0 < D)
    (x₀ : EuclideanSpace ℝ (Fin 3))
    (sh : Set (EuclideanSpace ℝ (Fin 3))) (hshmeas : MeasurableSet sh)
    (hshsub : sh ⊆ ((plankSlabModel P x₀).dilation D).carrier) :
    ∃ T : ShadedSlab (a / b) hδ1,
      (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) =
        (AffineMap.homothety (Q.center : EuclideanSpace ℝ (Fin 3)) (((D : ℝ)) * (b : ℝ))⁻¹) ''
          ((plankSlabModel P x₀).dilation D).carrier ∧
      T.shade =
        (AffineMap.homothety (Q.center : EuclideanSpace ℝ (Fin 3)) (((D : ℝ)) * (b : ℝ))⁻¹) '' sh ∧
      T.basis = P.basis := by
  set r := (((D:ℝ)) * (b : ℝ))⁻¹ with hr_def
  have hr_pos : 0 < r := by
    dsimp [r]; refine inv_pos.mpr ?_
    have : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
    have : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
    positivity
  have hr_ne_zero : r ≠ 0 := ne_of_gt hr_pos
  set h := AffineMap.homothety (Q.center : EuclideanSpace ℝ (Fin 3)) r with hh_def
  set σ := (plankSlabModel P x₀).dilation D with hσ_def
  have hcenter : σ.center = x₀ := by
    dsimp [σ, hσ_def, PrismNDim.dilation]; simp [PrismNDim.center_mk']
  have hbasis : σ.basis = P.basis := by
    dsimp [σ, hσ_def, PrismNDim.dilation]; simp [PrismNDim.basis_mk']
  have hthick_σ : σ.thicknesses = fun i : Fin 3 => D * (![a, b, b] : Fin 3 → ℝ≥0) i := by
    dsimp [σ, hσ_def]; ext i; simp [plankSlabModel, PrismNDim.thicknesses_mk', PrismNDim.dilation]
  have hcarrier_eq : h '' σ.carrier =
      (PrismNDim.mk' (h x₀) P.basis (fun i : Fin 3 => Real.toNNReal r * σ.thicknesses
          i)).carrier := by
    calc h '' σ.carrier
          = (PrismNDim.mk' (h σ.center) σ.basis (fun i : Fin 3 => Real.toNNReal r *
              σ.thicknesses i)).carrier :=
            homothety_image_prism_carrier_of_center σ (Q.center : EuclideanSpace ℝ (Fin 3)) r hr_pos
      _ = (PrismNDim.mk' (h x₀) P.basis (fun i : Fin 3 => Real.toNNReal r * σ.thicknesses
          i)).carrier := by
            simp [hcenter, hbasis]
  have hthick_eq : (fun i : Fin 3 => Real.toNNReal r * σ.thicknesses i) = ![a / b, 1, 1] := by
    ext i; fin_cases i
    · -- component 0 gives a/b, components 1,2 give 1; prove each by casting to ℝ
      have htemp : (Real.toNNReal r : ℝ) = r := by simp [hr_pos.le]
      have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne.symm
      have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne.symm
      calc
        (Real.toNNReal r : ℝ) * (σ.thicknesses 0 : ℝ) = r * (σ.thicknesses 0 : ℝ) := by rw [htemp]
        _ = r * ((D * ![a, b, b] 0 : ℝ≥0) : ℝ) := by rw [hthick_σ]
        _ = r * ((D * a : ℝ≥0) : ℝ) := by simp [Matrix.cons_val_zero]
        _ = r * ((D : ℝ) * (a : ℝ)) := by simp
        _ = ((D * b : ℝ)⁻¹) * ((D : ℝ) * (a : ℝ)) := by rw [hr_def]
        _ = (a : ℝ) / (b : ℝ) := by field_simp [hD0, hb0]
        _ = (![a / b, 1, 1] 0 : ℝ) := by simp
    · -- component 1 gives 1
      have htemp : (Real.toNNReal r : ℝ) = r := by simp [hr_pos.le]
      have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne.symm
      have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne.symm
      calc
        (Real.toNNReal r : ℝ) * (σ.thicknesses 1 : ℝ) = r * (σ.thicknesses 1 : ℝ) := by rw [htemp]
        _ = r * ((D * ![a, b, b] 1 : ℝ≥0) : ℝ) := by rw [hthick_σ]
        _ = r * ((D * b : ℝ≥0) : ℝ) := by simp [Matrix.cons_val_one]
        _ = r * ((D : ℝ) * (b : ℝ)) := by simp
        _ = ((D * b : ℝ)⁻¹) * ((D : ℝ) * (b : ℝ)) := by rw [hr_def]
        _ = 1 := by field_simp [hD0, hb0]
        _ = (![a / b, 1, 1] 1 : ℝ) := by simp
    · -- component 2 gives 1
      have htemp : (Real.toNNReal r : ℝ) = r := by simp [hr_pos.le]
      have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne.symm
      have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne.symm
      calc
        (Real.toNNReal r : ℝ) * (σ.thicknesses 2 : ℝ) = r * (σ.thicknesses 2 : ℝ) := by rw [htemp]
        _ = r * ((D * ![a, b, b] 2 : ℝ≥0) : ℝ) := by rw [hthick_σ]
        _ = r * ((D * b : ℝ≥0) : ℝ) := by simp [Matrix.cons_val]
        _ = r * ((D : ℝ) * (b : ℝ)) := by simp
        _ = ((D * b : ℝ)⁻¹) * ((D : ℝ) * (b : ℝ)) := by rw [hr_def]
        _ = 1 := by field_simp [hD0, hb0]
        _ = (![a / b, 1, 1] 2 : ℝ) := by simp
  let Sl : Slab (a / b) hδ1 :=
    { toPrismNDim := PrismNDim.mk' (h x₀) P.basis ![a / b, 1, 1]
      thicknesses_eq := PrismNDim.thicknesses_mk' _ _ _ }
  have hcarrier_Sl : (Sl.carrier : Set (EuclideanSpace ℝ (Fin 3))) = h '' σ.carrier := by
    calc (Sl.carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = (PrismNDim.mk' (h x₀) P.basis ![a / b, 1, 1]).carrier := rfl
      _ = (PrismNDim.mk' (h x₀) P.basis (fun i : Fin 3 => Real.toNNReal r * σ.thicknesses
          i)).carrier := by rw [hthick_eq]
      _ = h '' σ.carrier := by symm; exact hcarrier_eq
  have hmeas : MeasurableSet (h '' sh) :=
    measurableSet_homothety_image (Q.center : EuclideanSpace ℝ (Fin 3)) r hr_ne_zero hshmeas
  have hsub : h '' sh ⊆ Sl.carrier := by rw [hcarrier_Sl]; exact Set.image_mono hshsub
  let T : ShadedSlab (a / b) hδ1 :=
    { Sl with
      shade := h '' sh
      measurableSet_shade := hmeas
      shade_subset := hsub }
  refine ⟨T, ?_, ?_, ?_⟩
  · simp [T, hcarrier_Sl, hh_def, hr_def, hσ_def]
  · rfl
  · simp [T, Sl, PrismNDim.basis_mk']

/-- **Slab angle equals plank plane angle** (angle-transfer helper, step C).  Two slabs whose axes
are the axes of planks `P₁, P₂` have `Slab.angle` (the quantity governing `triAtAngle`) equal to the
plank plane angle `P₁.planeAngle P₂`, because both are `arccos |⟪·.basis 0, ·.basis 0⟫|` and the
isotropic rescaling keeps `basis 0`.  Combined with `plankSlabAngleComparable`, this transfers the
typical *plank* angle to a typical *slab* intersection angle without coordinate distortion. -/
private theorem slab_angle_eq_plank_planeAngle {δ₁ δ₂ : ℝ≥0} {hδ₁ : δ₁ ≤ 1} {hδ₂ : δ₂ ≤ 1}
    (S₁ : Slab δ₁ hδ₁) (S₂ : Slab δ₂ hδ₂) (P₁ P₂ : Plank a b hab hb1)
    (hb1' : S₁.basis = P₁.basis) (hb2' : S₂.basis = P₂.basis) :
    Slab.angle S₁ S₂ = P₁.planeAngle P₂ := by
  unfold Slab.angle
  rw [Prism3D.angle_def]
  unfold Prism3D.planeAngle
  rw [hb1', hb2']

/-- **Fullness under uniform volume scaling** (step 5 core).  If a second shaded family `Y'` has
every shade volume a fixed multiple `kE` of the corresponding `Y` shade volume, and every carrier
volume a fixed multiple `ρ` of the corresponding `Y` carrier volume (`ρ` positive and finite), then
the (ENNReal) fullness scales by `kE/ρ`:
`fullness' s Y' = (kE/ρ) · fullness' s Y`.  Applied with `kE = |r|³` (the homothety Jacobian) and
`ρ = |slab carrier|/|plank carrier|`, this transfers the fullness lower bound to the rescaled slab
family up to a fixed factor. -/
theorem fullness'_of_scaled {ι : Type*} (s : Finset ι)
    (Y Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (kE ρ : ENNReal) (hρ : ρ ≠ 0) (hρtop : ρ ≠ ⊤)
    (hshade : ∀ i ∈ s, volume (Y' i).shade = kE * volume (Y i).shade)
    (hcar : ∀ i ∈ s, volume (Y' i).carrier = ρ * volume (Y i).carrier) :
    ShadedBody.fullness' s Y' = (kE / ρ) * ShadedBody.fullness' s Y := by
  unfold ShadedBody.fullness'
  have hsum_shade : (∑ i ∈ s, volume (Y' i).shade) = kE * (∑ i ∈ s, volume (Y i).shade) := by
    calc
      (∑ i ∈ s, volume (Y' i).shade) = (∑ i ∈ s, kE * volume (Y i).shade) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hshade i hi]
      _ = kE * (∑ i ∈ s, volume (Y i).shade) := by rw [Finset.mul_sum]
  have hsum_carrier : (∑ i ∈ s, volume (Y' i).carrier) = ρ * (∑ i ∈ s, volume (Y i).carrier) := by
    calc
      (∑ i ∈ s, volume (Y' i).carrier) = (∑ i ∈ s, ρ * volume (Y i).carrier) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hcar i hi]
      _ = ρ * (∑ i ∈ s, volume (Y i).carrier) := by rw [Finset.mul_sum]
  rw [hsum_shade, hsum_carrier]
  set S := ∑ i ∈ s, volume (Y i).shade with hS
  set T := ∑ i ∈ s, volume (Y i).carrier with hT
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (Or.inl hρ) (Or.inl hρtop)]
  simp [mul_assoc, mul_comm, mul_left_comm]

/-- **Typical intersection angle from a plank incidence concentration** (step 4 transfer).  The
rescaled slab family `Σ`, whose shades are the images `h '' (Y i).shade` of a single homothety `h`
(ratio `r ≠ 0`) and whose axes are the plank axes (`(Σ i).basis = (V i).basis`), inherits the
typical-intersection-angle predicate `tri ≤ Mtyp · triAtAngle` from the corresponding concentration
of the *plank* shade-intersection mass at plank angle window `[θ⋆ - a/b, 2θ⋆]`.  The homothety
Jacobian `|r|³` is common to `tri` and `triAtAngle` (via `volume_inter_homothety_image`) and
cancels, and the slab angle equals the plank plane angle (`slab_angle_eq_plank_planeAngle`),
so the window matches.  This isolates the *only* geometric input to the dense-box estimate: the
plank
incidence concentration `hconc` (GWZ Lemma 6.8 typical angle), which is established upstream by the
angular-cap packing argument and is supplied as a hypothesis. -/
private theorem denseBox_typicalIntersection_transfer {ι : Type*}
    (s : Finset ι) (V : ι → Plank a b hab hb1) (hδ1 : a / b ≤ 1)
    (T : ι → ShadedSlab (a / b) hδ1)
    (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : r ≠ 0)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hshade : ∀ i ∈ s, (T i).shade = (AffineMap.homothety c r) '' (Y i).shade)
    (hbasis : ∀ i ∈ s, (T i).basis = (V i).basis)
    (θ0 : ℝ) (Mtyp : ℝ≥0)
    (hconc : (∑ i ∈ s, ∑ j ∈ s, volume ((Y i).shade ∩ (Y j).shade))
      ≤ (Mtyp : ENNReal) *
        (∑ i ∈ s, ∑ j ∈ s with
            (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
              Prism3D.angle (V i) (V j) ≤ 2 * θ0),
          volume ((Y i).shade ∩ (Y j).shade))) :
    ShadedSlab.IsTypicalIntersectionAngle s T θ0 (Mtyp : ENNReal) := by
  unfold ShadedSlab.IsTypicalIntersectionAngle
  set K := ENNReal.ofReal (|r| ^ 3) with hK
  have hKvol : ∀ (A B : Set (EuclideanSpace ℝ (Fin 3))),
      volume ((AffineMap.homothety c r) '' A ∩ (AffineMap.homothety c r) '' B) = K * volume (A ∩
          B) := by
    intro A B
    rw [volume_inter_homothety_image c r hr A B, hK]
  set LHS := ∑ i ∈ s, ∑ j ∈ s, volume ((Y i).shade ∩ (Y j).shade) with hLHS
  set RHS := ∑ i ∈ s, ∑ j ∈ s with
    (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
      Prism3D.angle (V i) (V j) ≤ 2 * θ0),
    volume ((Y i).shade ∩ (Y j).shade) with hRHS
  have hangle_eq (i j : ι) (hi : i ∈ s) (hj : j ∈ s) :
      Slab.angle (T i).toPrism3D (T j).toPrism3D = Prism3D.angle (V i) (V j) := by
    have hcast := slab_angle_eq_plank_planeAngle ((T i).toPrism3D : Slab (a / b) hδ1) ((T
        j).toPrism3D : Slab (a / b) hδ1) (V i) (V j)
      (by simpa using hbasis i hi) (by simpa using hbasis j hj)
    simpa [Prism3D.angle_def, Prism3D.planeAngle] using hcast
  -- Step 1: tri s T = K * LHS
  have htri : ShadedSlab.tri s T = K * LHS := by
    unfold ShadedSlab.tri
    calc
      ∑ i ∈ s, ∑ j ∈ s, volume ((T i).shade ∩ (T j).shade)
          = ∑ i ∈ s, ∑ j ∈ s, K * volume ((Y i).shade ∩ (Y j).shade) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hshade i hi, hshade j hj, hKvol]
      _ = K * (∑ i ∈ s, ∑ j ∈ s, volume ((Y i).shade ∩ (Y j).shade)) := by
        simp [Finset.mul_sum]
      _ = K * LHS := by rfl
  -- Step 2: triAtAngle s T θ0 = K * RHS
  have htriAtAngle : ShadedSlab.triAtAngle s T θ0 = K * RHS := by
    unfold ShadedSlab.triAtAngle
    -- Replace the filter predicate
    have hfilter_eq : ∀ i ∈ s, (Finset.filter (fun j =>
        θ0 - (a / b : ℝ) ≤ Slab.angle (T i).toPrism3D (T j).toPrism3D ∧
          Slab.angle (T i).toPrism3D (T j).toPrism3D ≤ 2 * θ0) s) =
      (Finset.filter (fun j =>
        θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
          Prism3D.angle (V i) (V j) ≤ 2 * θ0) s) := by
      intro i hi
      refine Finset.filter_congr fun j hj => ?_
      have hδ_eq : (a / b : ℝ) = ((a / b : ℝ≥0) : ℝ) := by simp
      constructor
      · intro h
        rcases h with ⟨hleft, hright⟩
        have hangle_eq' := hangle_eq i j hi hj
        rw [hangle_eq', hδ_eq] at hleft
        rw [hangle_eq'] at hright
        exact ⟨hleft, hright⟩
      · intro h
        rcases h with ⟨hleft, hright⟩
        have hangle_eq' := hangle_eq i j hi hj
        rw [← hangle_eq', ← hδ_eq] at hleft
        rw [← hangle_eq'] at hright
        exact ⟨hleft, hright⟩
    calc
      ∑ i ∈ s, ∑ j ∈ s with (θ0 - (a / b : ℝ) ≤ Slab.angle (T i).toPrism3D (T j).toPrism3D ∧
          Slab.angle (T i).toPrism3D (T j).toPrism3D ≤ 2 * θ0),
        volume ((T i).shade ∩ (T j).shade)
          = ∑ i ∈ s, ∑ j ∈ s with (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
              Prism3D.angle (V i) (V j) ≤ 2 * θ0),
            volume ((T i).shade ∩ (T j).shade) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hfilter_eq i hi]
      _ = ∑ i ∈ s, ∑ j ∈ s with (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
            Prism3D.angle (V i) (V j) ≤ 2 * θ0),
          K * volume ((Y i).shade ∩ (Y j).shade) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j ∈ s := (Finset.mem_filter.mp hj).1
        rw [hshade i hi, hshade j hj', hKvol]
      _ = K * (∑ i ∈ s, ∑ j ∈ s with (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
              Prism3D.angle (V i) (V j) ≤ 2 * θ0),
            volume ((Y i).shade ∩ (Y j).shade)) := by
        simp [Finset.mul_sum]
      _ = K * RHS := by rfl
  -- Step 3: Combine
  rw [htri, htriAtAngle]
  calc
    K * LHS ≤ K * ((Mtyp : ENNReal) * RHS) := by
      apply mul_le_mul_right hconc
    _ = (Mtyp : ENNReal) * (K * RHS) := by ring

/-- **Weighted exponent cancellation** (step 7 of the *weighted* dense-box assembly).
From the pulled-back inequality `lam²·X ≤ C₁·M·Y`, the multiplicity bound `M ≤ a^{-2η}` and the
fullness threshold `cLam·a^η ≤ lam`, one obtains

`C₁⁻¹ · cLam · a^{3η} · lam · X ≤ Y`.

The point is that only **one** copy of `lam` is spent against `cLam·a^η`; the other is kept.  Taking
`cLam = 1` and `lam = a^η` recovers the unweighted `a^{4η}` bound, so nothing is lost.  Concretely
`cLam·a^{3η}·lam = a^{2η}·((cLam·a^η)·lam) ≤ a^{2η}·lam²`, and `a^{2η}·M ≤ 1` kills the
multiplicity.

The uniform factor `cLam` is carried because the threshold that the *deletion layer* can actually
certify is `cLam·a^η` for a constant `cLam < 1` fixed before the configuration, never `a^η` on the
nose. -/
private theorem denseBox_exponent_cancel_weighted {a : ℝ≥0} {η : ℝ} (hη : 0 < η)
    (C1 : ℝ≥0) (hC1 : 0 < C1) (Mtyp : ENNReal) (cLam lam : ℝ≥0) (X Y : ENNReal)
    (hM : Mtyp ≤ (a : ENNReal) ^ (-(2 * η)))
    (hlam_lb : cLam * a ^ η ≤ lam)
    (hkey : ((lam : ℝ≥0) : ENNReal) ^ 2 * X ≤ (C1 : ENNReal) * Mtyp * Y) :
    (((C1⁻¹ : ℝ≥0) * cLam * a ^ (3 * η) * lam : ℝ≥0) : ENNReal) * X ≤ Y := by
  have h2η_nonneg : (0 : ℝ) ≤ 2 * η := by nlinarith
  -- Step 1: cLam·a^{3η}·lam ≤ a^{2η}·lam² in ℝ≥0
  have hstep1 : cLam * a ^ (3 * η) * lam ≤ a ^ (2 * η) * lam ^ 2 := by
    have hsplit : a ^ (3 * η) = a ^ (2 * η) * a ^ η := by
      by_cases ha0 : a = 0
      · subst ha0
        have h3 : (3 : ℝ) * η ≠ 0 := by positivity
        have h2 : (2 : ℝ) * η ≠ 0 := by positivity
        simp [NNReal.zero_rpow, h3, h2, hη.ne']
      · rw [← NNReal.rpow_add ha0]
        ring_nf
    calc cLam * a ^ (3 * η) * lam = a ^ (2 * η) * ((cLam * a ^ η) * lam) := by
          rw [hsplit]; ring
      _ ≤ a ^ (2 * η) * (lam * lam) :=
        mul_le_mul_right (mul_le_mul_left hlam_lb lam) (a ^ (2 * η) : ℝ≥0)
      _ = a ^ (2 * η) * lam ^ 2 := by ring
  -- Step 2: pass to ENNReal and cancel
  have hcoe : ((cLam * a ^ (3 * η) * lam : ℝ≥0) : ENNReal)
      ≤ ((a ^ (2 * η) : ℝ≥0) : ENNReal) * ((lam : ℝ≥0) : ENNReal) ^ 2 := by
    calc ((cLam * a ^ (3 * η) * lam : ℝ≥0) : ENNReal)
        ≤ ((a ^ (2 * η) * lam ^ 2 : ℝ≥0) : ENNReal) := ENNReal.coe_le_coe.mpr hstep1
      _ = ((a ^ (2 * η) : ℝ≥0) : ENNReal) * ((lam : ℝ≥0) : ENNReal) ^ 2 := by push_cast; ring
  have haE : ((a ^ (2 * η) : ℝ≥0) : ENNReal) = (a : ENNReal) ^ (2 * η) :=
    (ENNReal.coe_rpow_of_nonneg a h2η_nonneg)
  have hMone : (a : ENNReal) ^ (2 * η) * Mtyp ≤ 1 := aRpow_two_mul_M_le_one hη Mtyp hM
  have hC1_ne_zero : (C1 : ENNReal) ≠ 0 := by exact_mod_cast hC1.ne'
  have hC1_ne_top : (C1 : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- Main chain: cLam·a^{3η}·lam·X ≤ C1 · Y
  have hmain : ((cLam * a ^ (3 * η) * lam : ℝ≥0) : ENNReal) * X ≤ (C1 : ENNReal) * Y := by
    calc ((cLam * a ^ (3 * η) * lam : ℝ≥0) : ENNReal) * X
        ≤ ((a : ENNReal) ^ (2 * η) * ((lam : ℝ≥0) : ENNReal) ^ 2) * X := by
          refine mul_le_mul_left ?_ X
          rw [← haE]; exact hcoe
      _ = (a : ENNReal) ^ (2 * η) * (((lam : ℝ≥0) : ENNReal) ^ 2 * X) := by ring
      _ ≤ (a : ENNReal) ^ (2 * η) * ((C1 : ENNReal) * Mtyp * Y) :=
        mul_le_mul_right hkey ((a : ENNReal) ^ (2 * η))
      _ = (C1 : ENNReal) * (((a : ENNReal) ^ (2 * η) * Mtyp) * Y) := by ring
      _ ≤ (C1 : ENNReal) * (1 * Y) :=
        mul_le_mul_right (mul_le_mul_left hMone Y) (C1 : ENNReal)
      _ = (C1 : ENNReal) * Y := by ring
  -- Multiply by C1⁻¹
  have hfin : (C1 : ENNReal)⁻¹ * (((cLam * a ^ (3 * η) * lam : ℝ≥0) : ENNReal) * X) ≤ Y := by
    calc (C1 : ENNReal)⁻¹ * (((cLam * a ^ (3 * η) * lam : ℝ≥0) : ENNReal) * X)
        ≤ (C1 : ENNReal)⁻¹ * ((C1 : ENNReal) * Y) :=
          mul_le_mul_right hmain ((C1 : ENNReal)⁻¹)
      _ = ((C1 : ENNReal)⁻¹ * (C1 : ENNReal)) * Y := by ring
      _ = 1 * Y := by rw [ENNReal.inv_mul_cancel hC1_ne_zero hC1_ne_top]
      _ = Y := by simp
  calc (((C1⁻¹ : ℝ≥0) * cLam * a ^ (3 * η) * lam : ℝ≥0) : ENNReal) * X
      = ((C1⁻¹ : ℝ≥0) : ENNReal) * (((cLam * a ^ (3 * η) * lam : ℝ≥0) : ENNReal) * X) := by
        push_cast; ring
    _ = (C1 : ENNReal)⁻¹ * (((cLam * a ^ (3 * η) * lam : ℝ≥0) : ENNReal) * X) := by
        rw [ENNReal.coe_inv (ne_of_gt hC1)]
    _ ≤ Y := hfin

/-- **Combined exponent cancellation** (step 7 of the *combined* dense-box assembly).
Identical in role to `Plank.denseBox_exponent_cancel_weighted`, but fed the *honest* datum coming
out of the angular concentration: not the crude `Mtyp ≤ a^{-2η}` together with a `Cstar` fixed
before the configuration, but the single product bound

`Cstar · Mtyp ≤ K · a^{-η}`.

From `lam² · X ≤ (C₁·Cstar) · Mtyp · Y` one then obtains

`(C₁·K)⁻¹ · cLam · a^{2η} · lam · X ≤ Y`,

recovering one factor `a^η` relative to the weighted form.  The arithmetic is the same shape as in
the weighted version, with `a^{2η}` in place of `a^{3η}`: only one copy of `lam` is spent against
`cLam·a^η`, and one factor `a^η` is spent against the product bound via
`Plank.aRpow_mul_prod_le`.

Why the product and not the two factors separately: the concentration lemma
`Plank.exists_typicalIntersectionAngle_of_stableFibres` returns `Cstar = 8·Cstab` with
`Cstab = Kakeya.plankAngleScaleB a`, which *depends on* `a`, so `Cstar` cannot be quantified before
the configuration; only `Cstar·Mtyp = exp(O((log a⁻¹)^{3/4}))` admits a bound with a uniform
constant `K`.  See `Plank.exists_combined_absorption`. -/
private theorem denseBox_exponent_cancel_combined {a : ℝ≥0} {η : ℝ} (hη : 0 < η)
    (C1 : ℝ≥0) (hC1 : 0 < C1) (K : ℝ≥0) (hK : 0 < K)
    (Mtyp Cstar cLam lam : ℝ≥0) (X Y : ENNReal)
    (hprod : (Cstar : ENNReal) * (Mtyp : ENNReal) ≤ (K : ENNReal) * (a : ENNReal) ^ (-η))
    (hlam_lb : cLam * a ^ η ≤ lam)
    (hkey : ((lam : ℝ≥0) : ENNReal) ^ 2 * X
      ≤ ((C1 * Cstar : ℝ≥0) : ENNReal) * (Mtyp : ENNReal) * Y) :
    ((((C1 * K)⁻¹ : ℝ≥0) * cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal) * X ≤ Y := by
  have hη_nonneg : (0 : ℝ) ≤ η := by nlinarith
  -- Step 1: cLam·a^{2η}·lam ≤ a^η·lam² in ℝ≥0
  have hstep1 : cLam * a ^ (2 * η) * lam ≤ a ^ η * lam ^ 2 := by
    have hsplit : a ^ (2 * η) = a ^ η * a ^ η := by
      by_cases ha0 : a = 0
      · subst ha0
        have h2 : (2 : ℝ) * η ≠ 0 := by positivity
        have h1 : η ≠ 0 := by nlinarith
        simp [NNReal.zero_rpow, h2, h1]
      · rw [← NNReal.rpow_add ha0]
        ring_nf
    calc cLam * a ^ (2 * η) * lam = a ^ η * ((cLam * a ^ η) * lam) := by
          rw [hsplit]; ring
      _ ≤ a ^ η * (lam * lam) :=
        mul_le_mul_right (mul_le_mul_left hlam_lb lam) (a ^ η : ℝ≥0)
      _ = a ^ η * lam ^ 2 := by ring
  -- Step 2: pass to ENNReal
  have hcoe : ((cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal)
      ≤ ((a ^ η : ℝ≥0) : ENNReal) * ((lam : ℝ≥0) : ENNReal) ^ 2 := by
    calc ((cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal)
        ≤ ((a ^ η * lam ^ 2 : ℝ≥0) : ENNReal) := ENNReal.coe_le_coe.mpr hstep1
      _ = ((a ^ η : ℝ≥0) : ENNReal) * ((lam : ℝ≥0) : ENNReal) ^ 2 := by push_cast; ring
  have haE : ((a ^ η : ℝ≥0) : ENNReal) = (a : ENNReal) ^ η :=
    ENNReal.coe_rpow_of_nonneg a hη_nonneg
  -- Step 3: the product bound
  have hMone : (a : ENNReal) ^ η * ((Cstar : ENNReal) * (Mtyp : ENNReal)) ≤ (K : ENNReal) :=
    aRpow_mul_prod_le hη K ((Cstar : ENNReal) * (Mtyp : ENNReal)) hprod
  have hC1K_ne_zero' : (C1 : ENNReal) * (K : ENNReal) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hC1.ne') (by exact_mod_cast hK.ne')
  have hC1K_ne_top' : (C1 : ENNReal) * (K : ENNReal) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hC1K_nz : (C1 * K : ℝ≥0) ≠ 0 := mul_ne_zero (ne_of_gt hC1) (ne_of_gt hK)
  -- Main chain: ((cLam * a^(2η) * lam : ℝ≥0) : ENNReal) * X ≤ (C1 * K : ENNReal) * Y
  have hmain : ((cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal) * X ≤ ((C1 : ENNReal) * (K :
      ENNReal)) * Y := by
    calc ((cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal) * X
        ≤ ((a : ENNReal) ^ η * ((lam : ℝ≥0) : ENNReal) ^ 2) * X := by
          refine mul_le_mul_left ?_ X
          rw [← haE]; exact hcoe
      _ = (a : ENNReal) ^ η * (((lam : ℝ≥0) : ENNReal) ^ 2 * X) := by ring
      _ ≤ (a : ENNReal) ^ η * (((C1 * Cstar : ℝ≥0) : ENNReal) * (Mtyp : ENNReal) * Y) :=
        mul_le_mul_right hkey ((a : ENNReal) ^ η)
      _ = (a : ENNReal) ^ η * (((C1 : ENNReal) * (Cstar : ENNReal)) * (Mtyp : ENNReal) * Y) := by
        push_cast; ring
      _ = (C1 : ENNReal) * (((a : ENNReal) ^ η * ((Cstar : ENNReal) * (Mtyp : ENNReal))) * Y) :=
          by ring
      _ ≤ (C1 : ENNReal) * (((K : ENNReal)) * Y) :=
        mul_le_mul_right (mul_le_mul_left hMone Y) (C1 : ENNReal)
      _ = ((C1 : ENNReal) * (K : ENNReal)) * Y := by ring
  -- Multiply by (C1 * K)⁻¹
  have hfin : ((C1 : ENNReal) * (K : ENNReal))⁻¹ * (((cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal)
      * X) ≤ Y := by
    calc ((C1 : ENNReal) * (K : ENNReal))⁻¹ * (((cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal) * X)
        ≤ ((C1 : ENNReal) * (K : ENNReal))⁻¹ * (((C1 : ENNReal) * (K : ENNReal)) * Y) :=
          mul_le_mul_right hmain (((C1 : ENNReal) * (K : ENNReal))⁻¹)
      _ = (((C1 : ENNReal) * (K : ENNReal))⁻¹ * ((C1 : ENNReal) * (K : ENNReal))) * Y := by ring
      _ = 1 * Y := by rw [ENNReal.inv_mul_cancel hC1K_ne_zero' hC1K_ne_top']
      _ = Y := by simp
  calc ((((C1 * K)⁻¹ : ℝ≥0) * cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal) * X
      = (((C1 * K)⁻¹ : ℝ≥0) : ENNReal) * (((cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal) * X) := by
        push_cast; ring
    _ = ((C1 : ENNReal) * (K : ENNReal))⁻¹ * (((cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal) * X)
        := by
      rw [ENNReal.coe_inv hC1K_nz, ENNReal.coe_mul]
    _ ≤ Y := hfin

/-- **Volume rearrangement for the dense-box pullback** (step 7 setup, pure `ENNReal`/`ofReal`
algebra).  Feeds the slab-estimate output `(lam/216)²·θ₀ ≤ M·(jac·|U|)·40` (with the homothety
Jacobian `jac = (6b)⁻³`) together with `θ ≤ Cstar·θ₀` and the box volume `|Q| = 8θb³` into the clean
form `lam²·|Q| ≤ (8·Cstar·216·40)·M·|U|`.  The constants are tuned so the `b³` and the two `216`
factors cancel exactly; the only inequality used is `θ ≤ Cstar·θ₀`.

The threshold `lam` is a parameter rather than `a^η`, so that one copy of the fullness survives
into the conclusion. -/
private theorem denseBox_rearrange {b : ℝ≥0}
    (hb : 0 < b)
    (Cstar Mtyp lam : ℝ≥0) (θ : ℝ≥0) (θ0 : ℝ) (volU volQ : ENNReal)
    (hθθ0 : (θ : ℝ) ≤ (Cstar : ℝ) * θ0)
    (hboxvol : volQ = 8 * (θ : ENNReal) * (b : ENNReal) ^ 3)
    (hslab : (((lam / 216 : ℝ≥0)) : ENNReal) ^ 2 * ENNReal.ofReal θ0
      ≤ (Mtyp : ENNReal) * (((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) * volU) * 40) :
    ((lam : ℝ≥0) : ENNReal) ^ 2 * volQ
      ≤ ((8 * Cstar * 216 * 40 : ℝ≥0) : ENNReal) * Mtyp * volU := by
  set L := (((lam / 216 : ℝ≥0)) : ENNReal) ^ 2 with hL
  set jac := ((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) with hjac
  set Cbig := ((8 * Cstar * 216 * 40 : ℝ≥0) : ENNReal) with hCbig
  set κ : ℝ≥0 := 8 * (216 : ℝ≥0)^2 * b^3 with hκ
  have hb_nonneg_nnreal : 0 ≤ (b : ℝ≥0) := b.2
  have hCstar_nonneg : 0 ≤ (Cstar : ℝ) := Cstar.2
  have h6b_nz : (6 : ℝ) * (b : ℝ) ≠ 0 := by
    have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    nlinarith
  -- IDENTITY (i): (κ : ENNReal) * L = ((8 * b^3 : ℝ≥0) : ENNReal) * (lam : ENNReal) ^ 2
  have h_identity_i : (κ : ENNReal) * L
      = ((8 * b ^ 3 : ℝ≥0) : ENNReal) * ((lam : ℝ≥0) : ENNReal) ^ 2 := by
    have h_temp_nnreal : κ * ((lam / 216)^2 : ℝ≥0) = (8 * b ^ 3 : ℝ≥0) * (lam ^ 2 : ℝ≥0) := by
      simp only [hκ]
      apply NNReal.eq
      push_cast
      field_simp
    calc
      (κ : ENNReal) * L = (κ : ENNReal) * (((lam / 216 : ℝ≥0)) : ENNReal) ^ 2 := rfl
      _ = ((κ : ℝ≥0) : ENNReal) * (((lam / 216)^2 : ℝ≥0) : ENNReal) := by simp
      _ = ((κ * ((lam / 216)^2 : ℝ≥0) : ℝ≥0) : ENNReal) := by simp
      _ = (((8 * b ^ 3 : ℝ≥0) * (lam ^ 2 : ℝ≥0) : ℝ≥0) : ENNReal) := by rw [h_temp_nnreal]
      _ = ((8 * b ^ 3 : ℝ≥0) : ENNReal) * ((lam ^ 2 : ℝ≥0) : ENNReal) := by simp
      _ = ((8 * b ^ 3 : ℝ≥0) : ENNReal) * ((lam : ℝ≥0) : ENNReal) ^ 2 := by simp
  -- IDENTITY (ii): (κ : ENNReal) * jac = ((8 * 216 : ℝ≥0) : ENNReal)
  have h_identity_ii : (κ : ENNReal) * jac = ((8 * 216 : ℝ≥0) : ENNReal) := by
    have h_temp_jac_nnreal : κ * ((((6 : ℝ≥0) * b)⁻¹)^3 : ℝ≥0) = (8 * 216 : ℝ≥0) := by
      apply NNReal.eq
      simp [hκ]
      field_simp [h6b_nz]
      ring
    calc
      (κ : ENNReal) * jac = (κ : ENNReal) * ((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) := rfl
      _ = ((κ * ((((6 : ℝ≥0) * b)⁻¹)^3 : ℝ≥0) : ℝ≥0) : ENNReal) := by simp
      _ = ((8 * 216 : ℝ≥0) : ENNReal) := by rw [h_temp_jac_nnreal]
  -- IDENTITY (iii): (lam : ENNReal)^2 * volQ = (κ : ENNReal) * L * (θ : ENNReal)
  have h_identity_iii : ((lam : ℝ≥0) : ENNReal) ^ 2 * volQ = (κ : ENNReal) * L * (θ : ENNReal) := by
    calc
      ((lam : ℝ≥0) : ENNReal) ^ 2 * volQ =
          ((lam : ℝ≥0) : ENNReal) ^ 2 * (8 * (θ : ENNReal) * (b : ENNReal) ^ 3) := by rw [hboxvol]
      _ = ((8 * (b : ENNReal) ^ 3) * ((lam : ℝ≥0) : ENNReal) ^ 2) * (θ : ENNReal) := by ring
      _ = (((8 * b ^ 3 : ℝ≥0) : ENNReal) * ((lam : ℝ≥0) : ENNReal) ^ 2) * (θ : ENNReal) := by
        simp [ENNReal.coe_mul, ENNReal.coe_pow]
      _ = (κ : ENNReal) * L * (θ : ENNReal) := by rw [h_identity_i]
  -- Bound for (θ : ENNReal) in terms of Cstar and θ0
  have h_theta_bound : (θ : ENNReal) ≤ (Cstar : ENNReal) * ENNReal.ofReal θ0 := by
    calc
      (θ : ENNReal) = ENNReal.ofReal (θ : ℝ) := by simp
      _ ≤ ENNReal.ofReal ((Cstar : ℝ) * θ0) := ENNReal.ofReal_le_ofReal hθθ0
      _ = ENNReal.ofReal (Cstar : ℝ) * ENNReal.ofReal θ0 := by
        rw [ENNReal.ofReal_mul (by exact_mod_cast Cstar.2 : 0 ≤ (Cstar : ℝ))]
      _ = (Cstar : ENNReal) * ENNReal.ofReal θ0 := by simp
  -- Chain everything together
  calc
    ((lam : ℝ≥0) : ENNReal) ^ 2 * volQ = (κ : ENNReal) * L * (θ : ENNReal) := h_identity_iii
    _ ≤ (κ : ENNReal) * L * ((Cstar : ENNReal) * ENNReal.ofReal θ0) :=
      mul_le_mul_right h_theta_bound ((κ : ENNReal) * L)
    _ = ((κ : ENNReal) * (Cstar : ENNReal)) * (L * ENNReal.ofReal θ0) := by ring
    _ ≤ ((κ : ENNReal) * (Cstar : ENNReal)) * ((Mtyp : ENNReal) * (jac * volU) * 40) := by
      have htemp : L * ENNReal.ofReal θ0 ≤ (Mtyp : ENNReal) * (jac * volU) * 40 := by
        simpa [hL, hjac] using hslab
      exact mul_le_mul_right htemp ((κ : ENNReal) * (Cstar : ENNReal))
    _ = ((κ : ENNReal) * jac * 40 * (Cstar : ENNReal)) * Mtyp * volU := by ring
    _ = Cbig * Mtyp * volU := by
      rw [hCbig, h_identity_ii]
      simp [mul_assoc, mul_comm, mul_left_comm]

/-- **Slab fullness lower bound** (step 5).  If each slab shade volume is `kE = (6b)⁻³` times the
plank shade volume, each slab carrier has the fixed volume `8·(a/b)`, and each plank carrier has the
fixed volume `8·(a·b)`, then the fullness of the slab family is *exactly* `(kE/ρ)` times the plank
fullness with `ρ = (a/b)/(a·b) = b⁻²`, i.e. `(216·b)⁻¹` times it, so `lam ≤ λ` gives

`lam / (216·b) ≤ λ(s, T')`.

The rescaling factor `(216·b)⁻¹` is kept in full: discarding the `1/b` by `b ≤ 1` would force the
dense-box chain to run at the *plank* normalisation and make hypothesis (4) of the local estimate
unsatisfiable (a tangential family in a box always has `8 λ ≤ c_tan · b`).  Keeping the `1/b` is
consistent,
since `λ ≤ 1` always, so the conclusion already encodes `lam ≲ b`.

The threshold `lam` is kept as a *parameter* rather than specialised to `a^η`, so that one copy of
the input fullness survives into the conclusion of the dense-box estimate. -/
private theorem denseBox_fullness_lb {ι : Type*} (s : Finset ι)
    (Y T' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (a b lam : ℝ≥0) (hb : 0 < b)
    (hshv : ∀ i ∈ s, volume (T' i).shade
      = ((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) * volume (Y i).shade)
    (hcv : ∀ i ∈ s, volume (T' i).carrier = 8 * ((a / b : ℝ≥0) : ENNReal))
    (hYcv : ∀ i ∈ s, volume (Y i).carrier = 8 * ((a * b : ℝ≥0) : ENNReal))
    (hlam : lam ≤ ShadedBody.fullness s Y) :
    (lam / (216 * b) : ℝ≥0) ≤ ShadedBody.fullness s T' := by
  have hb0 : b ≠ 0 := hb.ne'
  set kE : ENNReal := ((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) with hkE
  set ρ : ENNReal := (((b ^ 2)⁻¹ : ℝ≥0) : ENNReal) with hρ
  have hρ0 : ρ ≠ 0 := by
    rw [hρ]; exact ENNReal.coe_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hb0))
  have hρtop : ρ ≠ ⊤ := by rw [hρ]; exact ENNReal.coe_ne_top
  -- carrier scaling
  have hcv' : ∀ i ∈ s, volume (T' i).carrier = ρ * volume (Y i).carrier := by
    intro i hi
    have key : (8 : ℝ≥0) * (a / b) = (b ^ 2)⁻¹ * (8 * (a * b)) := by
      apply NNReal.eq; push_cast; field_simp
    calc
      volume (T' i).carrier = 8 * ((a / b : ℝ≥0) : ENNReal) := hcv i hi
      _ = (((8 : ℝ≥0) * (a / b) : ℝ≥0) : ENNReal) := by push_cast; ring
      _ = (((b ^ 2)⁻¹ * (8 * (a * b)) : ℝ≥0) : ENNReal) := by rw [key]
      _ = (((b ^ 2)⁻¹ : ℝ≥0) : ENNReal) * ((8 * (a * b) : ℝ≥0) : ENNReal) := by push_cast; ring
      _ = (((b ^ 2)⁻¹ : ℝ≥0) : ENNReal) * (8 * ((a * b : ℝ≥0) : ENNReal)) := by push_cast; ring
      _ = ρ * volume (Y i).carrier := by rw [hρ, hYcv i hi]
  have hfs : ShadedBody.fullness' s T' = (kE / ρ) * ShadedBody.fullness' s Y :=
    fullness'_of_scaled s Y T' kE ρ hρ0 hρtop hshv hcv'
  -- kE / ρ = ((216*b)⁻¹ : ℝ≥0) as ENNReal
  have h_rho_inv : (((b ^ 2)⁻¹ : ℝ≥0) : ENNReal)⁻¹ = ((b ^ 2 : ℝ≥0) : ENNReal) := by
    rw [ENNReal.coe_inv (pow_ne_zero 2 hb0), inv_inv]
  have hkr : kE / ρ = ((((216 : ℝ≥0) * b)⁻¹ : ℝ≥0) : ENNReal) := by
    calc
      kE / ρ = ((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) * (((b ^ 2)⁻¹ : ℝ≥0) : ENNReal)⁻¹ := by
        rw [hkE, hρ, div_eq_mul_inv]
      _ = ((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) * ((b ^ 2 : ℝ≥0) : ENNReal) := by rw [h_rho_inv]
      _ = ((((6 : ℝ≥0) * b)⁻¹ ^ 3 * (b ^ 2) : ℝ≥0) : ENNReal) := by push_cast; ring
      _ = ((((216 : ℝ≥0) * b)⁻¹ : ℝ≥0) : ENNReal) := by
        apply congrArg (fun (x : ℝ≥0) => (x : ENNReal))
        apply NNReal.eq; push_cast; field_simp; norm_num
  -- fullness' s Y ≥ lam
  have h_eta : ((lam : ℝ≥0) : ENNReal) ≤ ShadedBody.fullness' s Y := by
    rw [← ShadedBody.coe_fullness s Y]; exact ENNReal.coe_le_coe.mpr hlam
  have h_lower : ((lam / (216 * b) : ℝ≥0) : ENNReal) ≤ ShadedBody.fullness' s T' := by
    have hcalc : ((lam / (216 * b) : ℝ≥0) : ENNReal)
        ≤ ((((216 : ℝ≥0) * b)⁻¹ : ℝ≥0) : ENNReal) * ShadedBody.fullness' s Y := by
      calc
        ((lam / (216 * b) : ℝ≥0) : ENNReal) = ((((216 : ℝ≥0) * b)⁻¹ * lam : ℝ≥0) : ENNReal) := by
          rw [div_eq_inv_mul]
        _ = ((((216 : ℝ≥0) * b)⁻¹ : ℝ≥0) : ENNReal) * ((lam : ℝ≥0) : ENNReal) := by push_cast; ring
        _ ≤ ((((216 : ℝ≥0) * b)⁻¹ : ℝ≥0) : ENNReal) * ShadedBody.fullness' s Y :=
          mul_le_mul_of_nonneg_left h_eta (by positivity)
    rw [hfs, hkr]
    exact hcalc
  rw [← ENNReal.coe_le_coe, ShadedBody.coe_fullness s T']
  exact h_lower

/-- **Choice-free analytic core of the dense-box estimate** (steps 4–6).  Given the rescaled
slab family `T` supplied explicitly, the typical-intersection concentration `hconc`, the
box-normalised fullness `b·lam ≤ λ(s,Y)` and the comparability `θ ≤ Cstar·θ₀`, it concludes

`lam² · |Q| ≤ (8·Cstar·216·40) · Mtyp · |⋃ shade|`.

No exponent `η`, no multiplicity bound `Mtyp ≤ a^{-2η}`, no fullness threshold `cLam·a^η ≤ lam` and
no lower bound `1 ≤ Cstar` is used: those enter only in the exponent-cancellation step, which is
applied to this single output in two different ways downstream.

The box `Q` is an arbitrary `ThetaBox θ b hθ1`; nothing here refers to a grid, so the estimate
applies verbatim to `Plank.shiftedSlabBox` at any shift. -/
theorem denseBox_core_raw {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
    (hδ1 : a / b ≤ 1)
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (θ : ℝ≥0) (hθ1 : θ ≤ 1) (Q : ThetaBox θ b hθ1)
    (θ0 : ℝ) (Mtyp Cstar lam : ℝ≥0)
    (T : ι → ShadedSlab (a / b) hδ1)
    (ha : 0 < a) (hb : 0 < b) (hne : s.Nonempty)
    (hshadeT : ∀ i ∈ s, (T i).shade
      = (AffineMap.homothety ((Q).center : EuclideanSpace ℝ (Fin 3))
          ((6 : ℝ) * (b : ℝ))⁻¹) '' (Y i).shade)
    (hbasisT : ∀ i ∈ s, (T i).basis = (V i).basis)
    (hcarT : ∀ i ∈ s,
      volume ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3))) = 8 * ((a / b : ℝ≥0) : ENNReal))
    (hcar : ∀ i ∈ s, (Y i).carrier = (V i).carrier)
    (habθ0 : ((a / b : ℝ≥0) : ℝ) ≤ θ0) (hθ01 : θ0 ≤ 1) (hθθ0 : (θ : ℝ) ≤ (Cstar : ℝ) * θ0)
    (hlam : b * lam ≤ ShadedBody.fullness s Y)
    (hconc : (∑ i ∈ s, ∑ j ∈ s, volume ((Y i).shade ∩ (Y j).shade))
      ≤ (Mtyp : ENNReal) *
        (∑ i ∈ s, ∑ j ∈ s with
            (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
              Prism3D.angle (V i) (V j) ≤ 2 * θ0),
          volume ((Y i).shade ∩ (Y j).shade))) :
    ((lam : ℝ≥0) : ENNReal) ^ 2 * volume (Q).carrier
      ≤ ((8 * Cstar * 216 * 40 : ℝ≥0) : ENNReal) * (Mtyp : ENNReal)
        * volume (⋃ i ∈ s, (Y i).shade) := by
  set c := ((Q).center : EuclideanSpace ℝ (Fin 3)) with hc
  set r : ℝ := ((6 : ℝ) * (b : ℝ))⁻¹ with hr
  have hrpos : 0 < r := by
    dsimp [r]
    refine inv_pos.mpr ?_
    have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    positivity
  have hrne : r ≠ 0 := ne_of_gt hrpos
  -- KEY CONVERSION: hjac
  have hjac : ENNReal.ofReal (|r| ^ 3) = ((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) := by
    calc
      ENNReal.ofReal (|r| ^ 3) = ENNReal.ofReal (r ^ 3) := by rw [abs_of_nonneg hrpos.le]
      _ = ENNReal.ofReal ((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ℝ) := by
        dsimp [r]
      _ = ((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) := by rw [ENNReal.ofReal_coe_nnreal]
  -- STEP A: typical intersection
  have htyp : ShadedSlab.IsTypicalIntersectionAngle s T θ0 (Mtyp : ENNReal) :=
    denseBox_typicalIntersection_transfer s V hδ1 T c r hrne Y hshadeT hbasisT θ0 Mtyp hconc
  -- STEP B: per-i shade volume
  have hshv : ∀ i ∈ s, volume ((T i).shade) = ((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) * volume
      ((Y i).shade) := by
    intro i hi
    calc
      volume ((T i).shade) = volume ((AffineMap.homothety c r) '' (Y i).shade) := by
        rw [hshadeT i hi]
      _ = ENNReal.ofReal (|r| ^ 3) * volume ((Y i).shade) := by
        rw [MeasureTheory.Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
        simp [abs_pow]
      _ = ((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) * volume ((Y i).shade) := by rw [hjac]
  -- STEP C: Y carrier volume
  have hYcv : ∀ i ∈ s, volume ((Y i).carrier) = 8 * ((a * b : ℝ≥0) : ENNReal) := by
    intro i hi
    rw [hcar i hi, Prism3D.volume_carrier (V i)]
    simp [mul_assoc]
  -- STEP D: fullness lower bound
  -- The box normalisation `b * lam ≤ λ(s, Y)` is exactly what the exact factor `(216 b)⁻¹` of
  -- `denseBox_fullness_lb` converts into the clean slab threshold `lam / 216`.
  have hfull : (lam / 216 : ℝ≥0) ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody) := by
    have hraw := denseBox_fullness_lb s Y (fun i => (T i).toShadedBody) a b (b * lam) hb hshv
      (fun i hi => by simpa using hcarT i hi) hYcv hlam
    have heq : (b * lam) / (216 * b) = lam / 216 := by
      have hb0 : (b : ℝ≥0) ≠ 0 := hb.ne'
      field_simp
    rwa [heq] at hraw
  -- STEP E: slab estimate
  have hδpos_nn : 0 < (a / b : ℝ≥0) := by
    exact_mod_cast div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hslab_raw := ShadedSlab.fullness_sq_angle_le_volume_union s T θ0 (Mtyp : ENNReal) htyp
    (by exact_mod_cast habθ0) hθ01 hδpos_nn hne (lam / 216 : ℝ≥0) hfull
  have hCval : (ShadedSlab.fullness_sq_angle_le_volume_union.C : ENNReal) = (40 : ENNReal) := by
    norm_num [ShadedSlab.fullness_sq_angle_le_volume_union.C,
      ShadedSlab.triAtAngle_le_card_sq_theta.C]
  have hslab : (((lam / 216 : ℝ≥0) : ENNReal) ^ 2 * ENNReal.ofReal θ0)
      ≤ (Mtyp : ENNReal) * volume (⋃ i ∈ s, (T i).shade) * (40 : ENNReal) := by
    simpa [hCval] using hslab_raw
  -- STEP F: union volume under homothety
  have hUvol : volume (⋃ i ∈ s, (T i).shade) = ((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) *
      volume (⋃ i ∈ s, (Y i).shade) := by
    calc
      volume (⋃ i ∈ s, (T i).shade) = volume (⋃ i ∈ s, (AffineMap.homothety c r) '' (Y i).shade)
          := by
        refine congrArg volume (Set.iUnion₂_congr fun i hi => ?_)
        rw [hshadeT i hi]
      _ = ENNReal.ofReal (|r| ^ 3) * volume (⋃ i ∈ s, (Y i).shade) := by
        rw [volume_iUnion_homothety_image c r s (fun i => (Y i).shade)]
      _ = ((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) * volume (⋃ i ∈ s, (Y i).shade) := by rw [hjac]
  -- STEP G: combine hslab and hUvol
  have hslab2 : (((lam / 216 : ℝ≥0) : ENNReal) ^ 2 * ENNReal.ofReal θ0)
      ≤ (Mtyp : ENNReal) * (((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) * volume (⋃ i ∈ s, (Y
          i).shade)) * 40 := by
    calc
      (((lam / 216 : ℝ≥0) : ENNReal) ^ 2 * ENNReal.ofReal θ0)
          ≤ (Mtyp : ENNReal) * volume (⋃ i ∈ s, (T i).shade) * (40 : ENNReal) := hslab
      _ = (Mtyp : ENNReal) * (((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) * volume (⋃ i ∈ s, (Y
          i).shade)) * (40 : ENNReal) := by rw [hUvol]
      _ = (Mtyp : ENNReal) * (((((6 : ℝ≥0) * b)⁻¹ ^ 3 : ℝ≥0) : ENNReal) * volume (⋃ i ∈ s, (Y
          i).shade)) * 40 := by norm_num
  -- STEP H: box volume
  have hbox : volume (Q).carrier = 8 * (θ : ENNReal) * (b : ENNReal) ^ 3 := by
    rw [Prism3D.volume_carrier (Q)]
    simp [mul_assoc, ENNReal.coe_mul, pow_three]
  -- STEP I: apply denseBox_rearrange (weighted form)
  have hkey : ((lam : ℝ≥0) : ENNReal) ^ 2 * volume (Q).carrier
      ≤ ((8 * Cstar * 216 * 40 : ℝ≥0) : ENNReal) * (Mtyp : ENNReal) * volume (⋃ i ∈ s, (Y
          i).shade) :=
    denseBox_rearrange hb Cstar Mtyp lam θ θ0 (volume (⋃ i ∈ s, (Y i).shade))
      (volume (Q).carrier) hθθ0 hbox hslab2
  exact hkey

/-- **Box-normalised dense-box estimate, raw form.**  The geometry of
`Plank.denseBoxEstimate_boxNormalised` with the exponent cancellation removed: it builds the
rescaled slab family from the tangential comparability hypothesis `htan` (which makes each
`Vᵢ ∩ Q` nonempty, hence supplies a base point) and returns the step-I inequality

`lam² · |Q| ≤ (8·Cstar·216·40) · Mtyp · |⋃ᵢ (Y i).shade|`.

The hypotheses are exactly those of `Plank.denseBoxEstimate_boxNormalised` minus `η`, `hη`, the
multiplicity bound `Mtyp ≤ a^{-2η}`, the fullness constant `cLam` with `cLam·a^η ≤ lam`, and
`1 ≤ Cstar`; and `Cstar` is an ordinary argument rather than an outer parameter, since nothing here
inverts it.  Both `Plank.denseBoxEstimate_boxNormalised` (whose statement is unchanged) and
`Plank.denseBoxEstimate_boxNormalised_combined` are derived from this one output by applying a
different exponent cancellation to it. -/
theorem denseBoxEstimate_boxNormalised_raw (cTan : ℝ≥0)
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (θ : ℝ≥0) (hθ1 : θ ≤ 1) (Q : ThetaBox θ b hθ1)
    (θ0 : ℝ) (Mtyp Cstar lam : ℝ≥0)
    (ha : 0 < a) (hb : 0 < b) (hθ : a / b ≤ θ) (hne : s.Nonempty)
    (hsh : ∀ i ∈ s, (Y i).shade ⊆ (V i).carrier ∩ Q.carrier)
    (htan : ∀ i ∈ s, Kakeya.ComparableScalars cTan
      (volume ((V i).carrier ∩ Q.carrier)).toNNReal (a * b ^ 2))
    (hcar : ∀ i ∈ s, (Y i).carrier = (V i).carrier)
    (habθ0 : ((a / b : ℝ≥0) : ℝ) ≤ θ0) (hθ01 : θ0 ≤ 1) (hθθ0 : (θ : ℝ) ≤ (Cstar : ℝ) * θ0)
    (hlam : b * lam ≤ ShadedBody.fullness s Y)
    (hconc : (∑ i ∈ s, ∑ j ∈ s, volume ((Y i).shade ∩ (Y j).shade))
      ≤ (Mtyp : ENNReal) *
        (∑ i ∈ s, ∑ j ∈ s with
            (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
              Prism3D.angle (V i) (V j) ≤ 2 * θ0),
          volume ((Y i).shade ∩ (Y j).shade))) :
    ((lam : ℝ≥0) : ENNReal) ^ 2 * volume Q.carrier
      ≤ ((8 * Cstar * 216 * 40 : ℝ≥0) : ENNReal) * (Mtyp : ENNReal)
        * volume (⋃ i ∈ s, (Y i).shade) := by
  -- hδ1 : a / b ≤ 1 follows from a/b ≤ θ and θ ≤ 1
  have hδ1 : a / b ≤ 1 := by
    calc
      a / b ≤ θ := hθ
      _ ≤ 1 := hθ1
  set c₀ := (Q.center : EuclideanSpace ℝ (Fin 3)) with hc₀_def
  -- Construct a default slab for indices not in s
  obtain ⟨i₀, hi₀⟩ := hne
  have hTan₀ : Kakeya.ComparableScalars cTan
      (volume ((V i₀).carrier ∩ Q.carrier)).toNNReal (a * b ^ 2) := htan i₀ hi₀
  rcases hTan₀ with ⟨hTan₀_le1, hTan₀_le2⟩
  have hpos_ab2 : 0 < a * b ^ 2 := by positivity
  have hpos_volNN₀ : 0 < (volume ((V i₀).carrier ∩ Q.carrier)).toNNReal := by
    have hpos_ab2' : (0 : ℝ≥0) < a * b ^ 2 := hpos_ab2
    by_contra! hle
    have hzero : (volume ((V i₀).carrier ∩ Q.carrier)).toNNReal = 0 :=
      le_antisymm hle (by positivity)
    have hzero_prod : cTan * (volume ((V i₀).carrier ∩ Q.carrier)).toNNReal = (0 : ℝ≥0) := by
      simp [hzero]
    have : (a * b ^ 2 : ℝ≥0) ≤ (0 : ℝ≥0) := by
      simpa [hzero_prod] using hTan₀_le2
    exact not_lt.mpr this hpos_ab2'
  have hnei₀ : ((V i₀).carrier ∩ Q.carrier : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    by_contra! hempty
    -- hempty :... = ∅ (by_contra! applies push_neg to ¬Set.Nonempty)
    have hvol0 : volume ((V i₀).carrier ∩ Q.carrier) = 0 := by
      simp [hempty]
    have hvolNN0 : (volume ((V i₀).carrier ∩ Q.carrier)).toNNReal = 0 := by
      simp [hvol0]
    exact hpos_volNN₀.ne' hvolNN0
  obtain ⟨x₀, hx₀⟩ := hnei₀
  have hx₀P : x₀ ∈ (V i₀).carrier := hx₀.1
  have hx₀Q : x₀ ∈ Q.carrier := hx₀.2
  have hsh₀ : (Y i₀).shade ⊆ (V i₀).carrier ∩ Q.carrier := hsh i₀ hi₀
  have hsub₀ : (Y i₀).shade ⊆ ((plankSlabModel (V i₀) x₀).dilation 6).carrier :=
    hsh₀.trans (plankSlabModel_inter_subset (V i₀) θ hθ1 Q hx₀P hx₀Q)
  have hmeas₀ : MeasurableSet ((Y i₀).shade) := (Y i₀).measurableSet_shade
  obtain ⟨Tdflt, _, hshTdflt, hbasTdflt⟩ :=
    exists_rescaled_shadedSlab_dilation (V i₀) θ hθ1 Q hb hδ1 (6 : ℝ≥0) (by norm_num) x₀
      ((Y i₀).shade) hmeas₀ hsub₀
  haveI : Nonempty (ShadedSlab (a / b) hδ1) := ⟨Tdflt⟩
  -- For each i, construct a ShadedSlab (a / b) hδ1
  have hex : ∀ i, ∃ Ti : ShadedSlab (a / b) hδ1, i ∈ s → ((Ti.shade = (AffineMap.homothety c₀
      ((6 : ℝ) * (b : ℝ))⁻¹) '' (Y i).shade) ∧ (Ti.basis = (V i).basis)) := by
    intro i
    by_cases hi : i ∈ s
    · -- i ∈ s: construct from htan i hi
      have hTani : Kakeya.ComparableScalars cTan
          (volume ((V i).carrier ∩ Q.carrier)).toNNReal (a * b ^ 2) := htan i hi
      rcases hTani with ⟨hTani_le1, hTani_le2⟩
      have hpos_volNN_i : 0 < (volume ((V i).carrier ∩ Q.carrier)).toNNReal := by
        have hpos_ab2' : (0 : ℝ≥0) < a * b ^ 2 := hpos_ab2
        by_contra! hle
        have hzero : (volume ((V i).carrier ∩ Q.carrier)).toNNReal = 0 :=
          le_antisymm hle (by positivity)
        have hzero_prod : cTan * (volume ((V i).carrier ∩ Q.carrier)).toNNReal = (0 : ℝ≥0) := by
          simp [hzero]
        have : (a * b ^ 2 : ℝ≥0) ≤ (0 : ℝ≥0) := by
          simpa [hzero_prod] using hTani_le2
        exact not_lt.mpr this hpos_ab2'
      have hnei : ((V i).carrier ∩ Q.carrier : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
        by_contra! hempty
        -- hempty :... = ∅ (by_contra! applies push_neg to ¬Set.Nonempty)
        have hvol0 : volume ((V i).carrier ∩ Q.carrier) = 0 := by
          simp [hempty]
        have hvolNN0 : (volume ((V i).carrier ∩ Q.carrier)).toNNReal = 0 := by
          simp [hvol0]
        exact hpos_volNN_i.ne' hvolNN0
      obtain ⟨xi, hxi⟩ := hnei
      have hxiP : xi ∈ (V i).carrier := hxi.1
      have hxiQ : xi ∈ Q.carrier := hxi.2
      have hshi : (Y i).shade ⊆ (V i).carrier ∩ Q.carrier := hsh i hi
      have hsubi : (Y i).shade ⊆ ((plankSlabModel (V i) xi).dilation 6).carrier :=
        hshi.trans (plankSlabModel_inter_subset (V i) θ hθ1 Q hxiP hxiQ)
      have hmeasi : MeasurableSet ((Y i).shade) := (Y i).measurableSet_shade
      obtain ⟨Ti, hcarTi, hshTi, hbasTi⟩ :=
        exists_rescaled_shadedSlab_dilation (V i) θ hθ1 Q hb hδ1 (6 : ℝ≥0) (by norm_num) xi
          ((Y i).shade) hmeasi hsubi
      refine ⟨Ti, fun _ => ⟨?_, hbasTi⟩⟩
      simpa [hc₀_def] using hshTi
    · -- i ∉ s: use the default slab
      refine ⟨Tdflt, fun hi' => (hi hi').elim⟩
  choose T hTprops using hex
  have hshadeT : ∀ i ∈ s, (T i).shade = (AffineMap.homothety c₀ ((6 : ℝ) * (b : ℝ))⁻¹) '' (Y
      i).shade :=
    fun i hi => (hTprops i hi).1
  have hbasisT : ∀ i ∈ s, (T i).basis = (V i).basis :=
    fun i hi => (hTprops i hi).2
  have hcarT : ∀ i ∈ s, volume ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3))) = 8 * ((a / b :
      ℝ≥0) : ENNReal) := by
    intro i hi
    simpa using Slab.volume_carrier ((T i).toPrism3D : Slab (a / b) hδ1)
  exact denseBox_core_raw hδ1 s V Y θ hθ1 Q θ0 Mtyp Cstar lam T ha hb ⟨i₀, hi₀⟩
    hshadeT hbasisT hcarT hcar habθ0 hθ01 hθθ0 hlam hconc

/-- **Box-normalised dense-box estimate.**  A local family of tangential plank pieces inside *any*
`θb × b × b` box `Q` obeys

`cDense · cLam · a^{3η} · lamBox · |Q| ≤ |⋃ᵢ (Y i).shade|`

for every threshold `lamBox` with `cLam · a^η ≤ lamBox` and `b · lamBox ≤ λ(s,Y)`.  The uniform
factor `cLam` is carried because the deletion layer certifies the local fullness only at a threshold
`cLam·a^η` with `cLam < 1` fixed before the configuration; taking `cLam = 1` gives the plain form
`a^η ≤ lamBox`.

**Why the `b`.**  The chain rescales the plank family by the homothety of ratio `(6b)⁻¹` centred at
the box, and `denseBox_fullness_lb` computes the resulting fullness *exactly*: it is multiplied by
`(216 b)⁻¹`, not merely by `216⁻¹`.  Retaining that `1/b` is what makes the estimate usable for a
*tangential* family in a box, where the shade lives in `Vᵢ ∩ Q` (volume `≲ a b²`) while the carrier
coherence forces the denominator to be the whole plank `|Vᵢ| = 8ab`; such a family always has
`8 λ ≤ c_tan · b`, so a
threshold hypothesis of the form `a^η ≤ λ` is unsatisfiable while `b·a^η ≤ λ` is not.  Both the
strengthened conclusion and the obstruction say the same thing: the estimate must be run at the box
normalisation.

One copy of the input fullness is retained in the conclusion; this is what the aggregate Item 2 of
Lemma 6.13 needs, because the box count already spends one factor `a^η`.

The box is an arbitrary `ThetaBox θ b hθ1`, not a grid box, so the statement applies verbatim to
`Plank.shiftedSlabBox` at any shift; no shifted or half-box variant is needed.

**Angle input.**  The slab estimate `ShadedSlab.fullness_sq_angle_le_volume_union` needs a typical
*intersection* angle, not a typical plank angle: the pairwise shade-incidence mass concentrated at a
single angle scale `θ₀ ∼ θ` with a sub-polynomial multiplicity `M ≤ a^{-2η}` (GWZ Lemma 6.8).
Deriving that concentration from the pointwise fibre-angle bound is the angular-cap *packing*
argument (blueprint `slabMassCap*` cluster), a separate development, so the concentration (`hconc`),
the comparability scale `Cstar` and the carrier coherence `(Y i).carrier = (V i).carrier` are
hypotheses here.  The constants are quantified before the configuration;
`cDense = (8·Cstar·216·40)⁻¹`. -/
theorem denseBoxEstimate_boxNormalised (cTan Cstar : ℝ≥0) (hCstar : 1 ≤ Cstar) :
    ∃ cDense : ℝ≥0, 0 < cDense ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (θ : ℝ≥0) (hθ1 : θ ≤ 1) (Q : ThetaBox θ b hθ1)
        (η : ℝ) (θ0 : ℝ) (Mtyp cLam lam : ℝ≥0),
        0 < a → 0 < b → 0 < η → a / b ≤ θ → s.Nonempty →
        (∀ i ∈ s, (Y i).shade ⊆ (V i).carrier ∩ Q.carrier) →
        (∀ i ∈ s, Kakeya.ComparableScalars cTan
          (volume ((V i).carrier ∩ Q.carrier)).toNNReal (a * b ^ 2)) →
        (∀ i ∈ s, (Y i).carrier = (V i).carrier) →
        ((a / b : ℝ≥0) : ℝ) ≤ θ0 → θ0 ≤ 1 → (θ : ℝ) ≤ (Cstar : ℝ) * θ0 →
        (Mtyp : ENNReal) ≤ (a : ENNReal) ^ (-(2 * η)) →
        cLam * a ^ η ≤ lam →
        b * lam ≤ ShadedBody.fullness s Y →
        ((∑ i ∈ s, ∑ j ∈ s, volume ((Y i).shade ∩ (Y j).shade))
          ≤ (Mtyp : ENNReal) *
            (∑ i ∈ s, ∑ j ∈ s with
                (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
                  Prism3D.angle (V i) (V j) ≤ 2 * θ0),
              volume ((Y i).shade ∩ (Y j).shade))) →
        ((cDense * cLam * a ^ (3 * η) * lam : ℝ≥0) : ENNReal) * volume Q.carrier ≤
          volume (⋃ i ∈ s, (Y i).shade) := by
  set cDense := (8 * Cstar * 216 * 40 : ℝ≥0)⁻¹ with hcDense_def
  have hcDense_pos : 0 < cDense := by
    dsimp [cDense]
    have hCstar_pos : 0 < Cstar := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < (1 : ℝ≥0)) hCstar
    have hprod_pos : 0 < (8 : ℝ≥0) * Cstar * (216 : ℝ≥0) * (40 : ℝ≥0) := by positivity
    exact inv_pos.mpr hprod_pos
  refine ⟨cDense, hcDense_pos, ?_⟩
  intro a b hab hb1 ι s V Y θ hθ1 Q η θ0 Mtyp cLam lam ha hb hη hθ hne hsh htan hcar habθ0 hθ01
    hθθ0 hMtyp hlam_lb hlam hconc
  have hkey : ((lam : ℝ≥0) : ENNReal) ^ 2 * volume Q.carrier
      ≤ ((8 * Cstar * 216 * 40 : ℝ≥0) : ENNReal) * (Mtyp : ENNReal) * volume (⋃ i ∈ s, (Y
          i).shade) :=
    denseBoxEstimate_boxNormalised_raw cTan s V Y θ hθ1 Q θ0 Mtyp Cstar lam ha hb hθ hne hsh htan
      hcar habθ0 hθ01 hθθ0 hlam hconc
  have hC1pos : (0 : ℝ≥0) < 8 * Cstar * 216 * 40 := by
    have hCstar_pos : 0 < Cstar := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < (1 : ℝ≥0)) hCstar
    positivity
  have hcancel := denseBox_exponent_cancel_weighted hη (8 * Cstar * 216 * 40 : ℝ≥0) hC1pos
    (Mtyp : ENNReal) cLam lam (volume Q.carrier) (volume (⋃ i ∈ s, (Y i).shade)) hMtyp hlam_lb hkey
  simpa [cDense] using hcancel

/-- **Box-normalised dense-box estimate from the combined product bound.**  The same geometry as
`Plank.denseBoxEstimate_boxNormalised`, fed the *honest* sub-polynomial datum instead of the crude
one, and consequently one factor `a^η` stronger:

`cDense · cLam · a^{2η} · lam · |Q| ≤ |⋃ᵢ (Y i).shade|`,  `cDense = (8·216·40·Ceta)⁻¹`.

**What changed, and why it had to.**  `Plank.denseBoxEstimate_boxNormalised` charges its two
sub-polynomial losses separately: the comparability scale `Cstar` is an *outer* parameter absorbed
into `cDense = (8·Cstar·216·40)⁻¹`, and the multiplicity is charged the crude bound
`Mtyp ≤ a^{-2η}`.  That split weakens what the angular concentration actually produces.
`Plank.exists_typicalIntersectionAngle_of_stableFibres` returns `Mtyp = 2(N+1)` with
`N = O((log a⁻¹)^{3/4})` *and* `Cstar = 8·Cstab` with `Cstab = Kakeya.plankAngleScaleB a`; neither
factor is uniform in `a`, but their product is `exp(O((log a⁻¹)^{3/4})) ≤ Ceta·a^{-η}` for `a` below
a threshold depending on `η` and `Cang` (`Plank.exists_combined_absorption`).  So the honest uniform
datum is the single product bound `Cstar·Mtyp ≤ Ceta·a^{-η}`, with exponent `-η`, and spending it
costs only one factor `a^η` instead of two.

**`Cstar` is bound with the configuration, not before it.**  This is required, not cosmetic: since
`Cstar = 8·Kakeya.plankAngleScaleB a` depends on `a`, it cannot be fixed before the geometric data;
only the product admits a bound whose constant `Ceta` is quantified first.  Correspondingly
`1 ≤ Cstar` is not assumed — `Plank.denseBoxEstimate_boxNormalised_raw` never inverts `Cstar`, and
the inversion in `cDense` now involves only the numeral `8·216·40` and the uniform `Ceta`.

The price is that the estimate is available only where the product bound holds, i.e. for `a` small
in terms of `η` and `Cang`.  Under the crude hypothesis the same restriction was hidden one layer up
inside `Plank.exists_bandCount_le_rpow`; here it is explicit.  Nothing is weakened:
`Plank.denseBoxEstimate_boxNormalised` is kept verbatim and all its consumers are untouched. -/
theorem denseBoxEstimate_boxNormalised_combined (cTan Ceta : ℝ≥0) (hCeta : 0 < Ceta) :
    ∃ cDense : ℝ≥0, 0 < cDense ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (θ : ℝ≥0) (hθ1 : θ ≤ 1) (Q : ThetaBox θ b hθ1)
        (η : ℝ) (θ0 : ℝ) (Mtyp Cstar cLam lam : ℝ≥0),
        0 < a → 0 < b → 0 < η → a / b ≤ θ → s.Nonempty →
        (∀ i ∈ s, (Y i).shade ⊆ (V i).carrier ∩ Q.carrier) →
        (∀ i ∈ s, Kakeya.ComparableScalars cTan
          (volume ((V i).carrier ∩ Q.carrier)).toNNReal (a * b ^ 2)) →
        (∀ i ∈ s, (Y i).carrier = (V i).carrier) →
        ((a / b : ℝ≥0) : ℝ) ≤ θ0 → θ0 ≤ 1 → (θ : ℝ) ≤ (Cstar : ℝ) * θ0 →
        (Cstar : ENNReal) * (Mtyp : ENNReal) ≤ (Ceta : ENNReal) * (a : ENNReal) ^ (-η) →
        cLam * a ^ η ≤ lam →
        b * lam ≤ ShadedBody.fullness s Y →
        ((∑ i ∈ s, ∑ j ∈ s, volume ((Y i).shade ∩ (Y j).shade))
          ≤ (Mtyp : ENNReal) *
            (∑ i ∈ s, ∑ j ∈ s with
                (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
                  Prism3D.angle (V i) (V j) ≤ 2 * θ0),
              volume ((Y i).shade ∩ (Y j).shade))) →
        ((cDense * cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal) * volume Q.carrier ≤
          volume (⋃ i ∈ s, (Y i).shade) := by
  set cDense := ((8 * 216 * 40 : ℝ≥0) * Ceta)⁻¹ with hcDense_def
  have hcDense_pos : 0 < cDense := by
    dsimp [cDense]
    have hprod_pos : 0 < (8 * 216 * 40 : ℝ≥0) * Ceta := by positivity
    exact inv_pos.mpr hprod_pos
  refine ⟨cDense, hcDense_pos, ?_⟩
  intro a b hab hb1 ι s V Y θ hθ1 Q η θ0 Mtyp Cstar cLam lam ha hb hη hθ hne hsh htan hcar habθ0
    hθ01 hθθ0 hprod hlam_lb hlam hconc
  set C1 : ℝ≥0 := (8 * 216 * 40 : ℝ≥0) with hC1_def
  have hC1pos : 0 < C1 := by
    dsimp [C1]; norm_num
  -- Use denseBoxEstimate_boxNormalised_raw to get lam²·|Q| ≤ (8·Cstar·216·40)·Mtyp·|U|
  have hraw : ((lam : ℝ≥0) : ENNReal) ^ 2 * volume Q.carrier
      ≤ ((8 * Cstar * 216 * 40 : ℝ≥0) : ENNReal) * (Mtyp : ENNReal) * volume (⋃ i ∈ s, (Y
          i).shade) :=
    denseBoxEstimate_boxNormalised_raw cTan s V Y θ hθ1 Q θ0 Mtyp Cstar lam ha hb hθ hne hsh htan
      hcar habθ0 hθ01 hθθ0 hlam hconc
  -- Note: (8 * Cstar * 216 * 40 : ℝ≥0) = (C1 * Cstar : ℝ≥0) because C1 = 8*216*40
  have hCstar_eq : ((8 * Cstar * 216 * 40 : ℝ≥0) : ENNReal) = ((C1 * Cstar : ℝ≥0) : ENNReal) := by
    dsimp [C1]; ring
  have hkey' : ((lam : ℝ≥0) : ENNReal) ^ 2 * volume Q.carrier
      ≤ ((C1 * Cstar : ℝ≥0) : ENNReal) * (Mtyp : ENNReal) * volume (⋃ i ∈ s, (Y i).shade) := by
    rw [hCstar_eq] at hraw; exact hraw
  -- Now apply denseBox_exponent_cancel_combined with K := Ceta, C1 := C1
  have h_cancel := denseBox_exponent_cancel_combined hη C1 hC1pos Ceta hCeta Mtyp Cstar cLam lam
    (volume Q.carrier) (volume (⋃ i ∈ s, (Y i).shade)) hprod hlam_lb hkey'
  -- The conclusion of h_cancel is:
  -- ((((C1 * Ceta)⁻¹ : ℝ≥0) * cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal) * volume Q.carrier ≤
  -- volume (⋃ i ∈ s, (Y i).shade)
  -- But we need ((cDense * cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal) * volume Q.carrier ≤...
  -- where cDense = (C1 * Ceta)⁻¹
  have h_cDense_eq : (cDense : ℝ≥0) = (C1 * Ceta)⁻¹ := by
    rfl
  simpa [h_cDense_eq] using h_cancel

end Plank

end
