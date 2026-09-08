/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThinConfig
public import Kakeya.DimensionThree.MainLemma2.ThinEstimates
public import Kakeya.DimensionThree.MainLemma2.Goals
public import Kakeya.DimensionThree.Slab.Multiplicity

/-!
# The slab case of the thin case of Main Lemma 2

This file formalizes the slab-case subsubsection of the blueprint
(`blueprint/src/GWZAdapted/section9_slab.tex`): the case `b ≥ δ^{exscal} r₁ = δ^{2·exscal}` of
the very-not-sticky configuration, where `b` is the middle affine thickness of the factoring
bodies. In this case each `W ∈ 𝕎'_B` is a giant slab, with affine thicknesses
`τ₀(W) ∼ r₁ = δ^{exscal}`, `τ₁(W) ≳ δ^{2 exscal}` and `τ₂(W) ∼ a`, and GWZ Lemma 6.9 —
`ShadedPrism3D.multiplicity_le_rpow` — applies to the rescaled family.

The chain of estimates is:

* `Kakeya.VeryNotSticky.slabPrismEnclosure` turns a family of convex bodies whose affine
  thicknesses are only *comparable* to `(r₁, b, a)`, with a given constant, into a family of
  `ShadedPrism3D` objects with *exact* half-widths `a/r₁ × b/r₁ × 1`, which is the shape
  `ShadedPrism3D.multiplicity_le_rpow` demands (blueprint `lem:ml2slabPrismEnclosure`). It is
  generic in that constant.
* `Kakeya.VeryNotSticky.slabCarrierEnclosure` instantiates it at the family the shading
  `(tc.thinBall hB).W` actually shades, namely the *enlarged carriers*
  `fun j ↦ ((tc.thinBall hB).W j).toConvexSpaceBody`, and therefore at the doubled constant
  `2 C₀`, which is the profile those carriers have by
  `Kakeya.ThinCase.ThinBall.hasThicknesses_W` (blueprint `lem:ml2slabCarrierEnclosure`).
* `Kakeya.VeryNotSticky.slabEpsChoice` fixes the parameter `ε` with `(a/r₁)^ε = δ^{exscal}`
  and the two half-width hypotheses (blueprint `lem:ml2slabEpsChoice`), while
  `Kakeya.VeryNotSticky.slabPrismDensity` and
  `Kakeya.VeryNotSticky.slabPrismAntiClustering` discharge the density and anti-clustering
  hypotheses of GWZ Lemma 6.9 against (S1) and (S2) (blueprint `lem:ml2slabPrismDensity`,
  `lem:ml2slabPrismAntiClustering`). The second of those is where `Δ_max` is carried from the
  geometric bodies `bd.Wb`, which (C4) controls, to the enlarged carriers, which the enclosure
  consumes, by `Kakeya.ThinCase.ThinBall.isVolumeControlledEnlargement` composed with
  `ConvexSpaceBody.IsVolumeControlledEnlargement.maxDensity_le`.
* `Kakeya.VeryNotSticky.slabMultBound` assembles those four and reads the gain back at the
  coarse scale: `μ(𝕎'_B, Y_{𝕎'_B}) ≤ C_{slabMultBound}(exscal) δ^{-8 exscal}` (blueprint
  `lem:ml2slabMultBound`).
* `Kakeya.VeryNotSticky.slabUnionFromMult` converts the multiplicity bound into a lower bound
  for `|U(𝕋_B, Y'_B)|`, through `Kakeya.ThinCase.unionLower_thin` (blueprint
  `lem:ml2slabUnionFromMult`), and `Kakeya.VeryNotSticky.slabUnion` substitutes the former
  into the latter (blueprint `lem:ml2slabUnion`).
* `Kakeya.VeryNotSticky.slabDensity` compares the mass of the retained tube segments with the
  mass of the factoring bodies (blueprint `lem:ml2slabDensity`), giving the per-ball estimate
  `Kakeya.VeryNotSticky.slabPerBall` (blueprint `lem:ml2slabPerBall`).
* Summing over `B ∈ 𝔅` — the per-ball unions being pairwise disjoint
  (`Kakeya.VeryNotSticky.slabUnionDisjoint`) and contained in `U(𝕋, Y)`
  (`Kakeya.VeryNotSticky.slabUnionSum`) — and applying
  `Kakeya.VeryNotSticky.slabVolumeGoal` gives the volume form of the goal with gain `β/2`,
  which `Kakeya.VeryNotSticky.goalMult_of_goalUnion` converts into `Kakeya.goalMult_of_b_ge`.

Eight facts used by this chain are collected once, as `Kakeya.VeryNotSticky.SlabInputs`
(blueprint `hyp:ml2slabinputs`), and every lemma of the chain that consumes one of them carries
the bundle as an explicit hypothesis. They are *produced*, not accepted:
`Kakeya.VeryNotSticky.slabInputs` builds the bundle from the standing configuration together
with the thresholds `Kakeya.VeryNotSticky.SlabScale`. Four of the eight are items of
the standing configuration — `Kakeya.VeryNotSticky.BallData.bodies_antiClustering` of (C4),
`Kakeya.VeryNotSticky.BallData.segs_dilation` of (C3), `Kakeya.VeryNotSticky.tube_count` of (C1)
and `Kakeya.VeryNotSticky.ThinConfig.segment_mass` of (T7) — and the remaining four, `δ < 1`
and the three threshold inequalities, are the fields of `SlabScale`, which is the `tc`-aware
companion of `Kakeya.VeryNotSticky.CaseScale`: two of them mention the thin-case comparison
constant `tc.C`, which `CaseScale` is stated before and therefore does not see.
`Kakeya.goalMult_of_b_ge` accordingly takes `SlabScale` as an extra hypothesis, at the cost of
one argument at its unique call site inside `Kakeya.goalMult_of_a_le`.

All the per-ball data is read off the bundles: `𝕎'_B` is `(tc.thinBall hB).bodies'`, its
shading `Y_{𝕎'_B}` is `(tc.thinBall hB).W`, the two shaded unions `U(𝕎'_B, Y_{𝕎'_B})` and
`U(𝕋_B, Y'_B)` are `(tc.thinBall hB).UW` and `(tc.thinBall hB).U`, and the geometric bodies
themselves are `bd.Wb`.

The shaded bodies `(tc.thinBall hB).W` do *not* carry `bd.Wb` as their carrier: they carry a
controlled enlargement of it. All that is recorded about the two is the sandwich
`Kakeya.ThinCase.ThinBall.Wb_le_W` / `Kakeya.ThinCase.ThinBall.W_le_cthickening`, and the
slab case reaches the geometric bodies from the carriers only through the transfer lemmas
derived from it — `Kakeya.ThinCase.ThinBall.sum_volume_Wb_le` in
`Kakeya.VeryNotSticky.slabBodyMassBound`,
`Kakeya.ThinCase.ThinBall.isVolumeControlledEnlargement` in
`Kakeya.VeryNotSticky.slabPrismAntiClustering`, and
`Kakeya.ThinCase.ThinBall.hasThicknesses_W` in
`Kakeya.VeryNotSticky.slabCarrierEnclosure`. The statements of the chain from
`slabBodyMassBound` onwards are all phrased in `bd.Wb`, which is the currency the rest of the
argument and the final Main Lemma 2 bound speak in; only the bridging is about the carriers.

Nothing is taken as a free argument, exactly as in
`Kakeya.DimensionThree.MainLemma2.NonSlabCase`: with free data the branch hypotheses would be
satisfiable vacuously by the empty family.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody

universe u

/-! ### From convex bodies to exact prisms -/

/-- **Constant in Lemma `lem:ml2slabPrismEnclosure`** (blueprint
`def:ml2slabPrismEnclosureConstant`).

`C_{lem:ml2slabPrismEnclosure}(C₀)` is a constant with the following property: whenever
`V ⊆ ℝ³` is a convex body whose affine thicknesses are comparable, with constant `C₀`, to
`(1, b', a')` with `0 < a' ≤ b' ≤ 1`, the `C₀`-dilate of the exact `a' × b' × 1` box aligned
with the John ellipsoid of `V` contains `V` and has volume at most
`C_{lem:ml2slabPrismEnclosure}(C₀) |V|`.

It is a function of `C₀` alone: not of `δ`, not of `a` or `b`, not of the ball `B`, and not of
the family. As for `Kakeya.ThinCase.factoringApplyConstant` it is a constant *by choice*
rather than by a formula — an admissible value is read off the John-ellipsoid comparison of
`Kakeya.HasThicknesses`, as a fixed power of `C₀` times an absolute constant — and no later
step uses its value; what is used is the volume comparison of
`Kakeya.VeryNotSticky.slabPrismEnclosure` and the fact that one such constant serves every
body of every `𝕎'_B`. The displayed value is provisional. -/
noncomputable def slabPrismEnclosureConstant (C₀ : NNReal) : NNReal := max 1 (2 ^ 20 * C₀ ^ 6)

lemma one_le_slabPrismEnclosureConstant (C₀ : NNReal) : 1 ≤ slabPrismEnclosureConstant C₀ :=
  le_max_left _ _

/-- **Enclosing one rescaled body in an exact prism** (blueprint
`lem:ml2slabPrismEnclosureBody`).

The per-body step of `Kakeya.VeryNotSticky.slabPrismEnclosure`. The body `K`, whose affine
thicknesses are comparable to `(r₁, b, a)` with constant `C₀`, is enclosed in the box aligned
with its John ellipsoid, of exact half-widths `C₀ a × C₀ b × C₀ r₁`
(`Prism3D.exists_superset_volume_le_of_hasThicknesses`), and the whole picture is then dilated
by the ratio `ρ` about the origin (`Prism3D.homothety`, `ConvexSpaceBody.homothety`,
`ShadedBody.homothety`). The three equations `ha'`, `hb'`, `hone` say that this dilation turns
the half-widths into `a' × b' × 1`; at the call site `ρ = (C₀ r₁)⁻¹`, which is exactly what
makes the third one hold.

The volume loss is `Prism3D.enclosureVolumeConstant C₀ = 48 C₀⁶`, absorbed into the larger
`Kakeya.VeryNotSticky.slabPrismEnclosureConstant C₀`; the dilation multiplies both volumes by
`ρ³` and therefore does not change it. The shading is carried along unchanged as a set, which
is why the shading of the prism is literally that of `V.homothety`. -/
theorem slabPrismEnclosureBody {a b r₁ C₀ a' b' ρ : NNReal} (hC₀ : 1 ≤ C₀)
    (hρ0 : (ρ : ℝ) ≠ 0)
    (ha' : a' = ρ * (C₀ * a)) (hb' : b' = ρ * (C₀ * b)) (hone : (1 : NNReal) = ρ * (C₀ * r₁))
    (hab' : a' ≤ b') (hb1' : b' ≤ 1)
    (hCab : C₀ * a ≤ C₀ * b) (hCbr : C₀ * b ≤ C₀ * r₁)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (V : ShadedBody (EuclideanSpace ℝ (Fin 3))) (hVK : V.toConvexSpaceBody = K)
    (hthick : HasThicknesses (K.carrier) C₀ ![(r₁ : ℝ), (b : ℝ), (a : ℝ)]) :
    ∃ P : ShadedPrism3D a' b' 1 hab' hb1' le_rfl,
      K.homothety 0 (ρ : ℝ) ≤ P.toConvexSpaceBody ∧
      volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ≤ (slabPrismEnclosureConstant C₀ : ENNReal)
            * volume ((K.homothety 0 (ρ : ℝ)).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∧
      P.shade = (V.homothety 0 hρ0).shade := by
  have hρne : ρ ≠ 0 := by exact_mod_cast hρ0
  have hρpos : (0 : NNReal) < ρ := pos_iff_ne_zero.mpr hρne
  -- STEP 1: enclose K in the exact prism Q at the original scale.
  obtain ⟨Q, hKQ, hQvol⟩ :=
    Prism3D.exists_superset_volume_le_of_hasThicknesses (A := C₀ * a) (B := C₀ * b) (C := C₀ * r₁)
      (hAB := hCab) (hBC := hCbr) hC₀ K hthick
      (by rw [NNReal.coe_mul]) (by rw [NNReal.coe_mul]) (by rw [NNReal.coe_mul])
  -- STEP 2: dilate Q by ρ about the origin.
  let Qρ : Prism3D a' b' 1 hab' hb1' :=
    Q.homothety (0 : EuclideanSpace ℝ (Fin 3)) ρ hab' hb1' ha' hb' hone
  have hQρ_carrier :
      (Qρ.carrier : Set (EuclideanSpace ℝ (Fin 3))) =
        AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) '' Q.carrier :=
    Prism3D.carrier_homothety Q (0 : EuclideanSpace ℝ (Fin 3)) hρpos hab' hb1' ha' hb' hone
  -- shadings
  have hVh : (V.homothety 0 hρ0).toConvexSpaceBody = K.homothety 0 (ρ : ℝ) := by
    rw [ShadedBody.homothety_toConvexSpaceBody, hVK]
  have hKQ_image : (K.homothety 0 (ρ : ℝ)).carrier ⊆
      AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) '' Q.carrier := by
    change (K.homothety 0 (ρ : ℝ) : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) '' Q.carrier
    rw [ConvexSpaceBody.coe_homothety]
    exact Set.image_mono hKQ
  have hKQimg : (K.homothety 0 (ρ : ℝ)).carrier ⊆ Qρ.carrier :=
    hKQ_image.trans (by rw [← hQρ_carrier])
  have hcarrier_contain : (V.homothety 0 hρ0).carrier ⊆ Qρ.carrier := by
    calc
      (V.homothety 0 hρ0).carrier ⊆ (K.homothety 0 (ρ : ℝ)).carrier := by rw [hVh]
      _ ⊆ Qρ.carrier := hKQimg
  have hsub : (V.homothety 0 hρ0).shade ⊆ Qρ.carrier :=
    (V.homothety 0 hρ0).shade_subset.trans hcarrier_contain
  have hm : MeasurableSet ((V.homothety 0 hρ0).shade) :=
    (V.homothety 0 hρ0).measurableSet_shade
  let P : ShadedPrism3D a' b' 1 hab' hb1' le_rfl :=
    ShadedPrism3D.ofPrism3D Qρ ((V.homothety 0 hρ0).shade) hm hsub le_rfl
  -- first conclusion
  have hPtoQ : (P.toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3))) = Qρ.carrier := by
    simp [P]
    rfl
  have hFirst : K.homothety 0 (ρ : ℝ) ≤ P.toConvexSpaceBody := by
    change (K.homothety 0 (ρ : ℝ) : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (P.toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3)))
    rw [hPtoQ]
    exact hKQimg
  -- volume comparison
  have hQρvol : volume (Qρ.carrier : Set (EuclideanSpace ℝ (Fin 3))) =
      ENNReal.ofReal |(ρ : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))| *
        volume (Q.carrier : Set _) := by
    rw [hQρ_carrier]
    exact MeasureTheory.Measure.addHaar_image_homothety
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
  have hKhvol : volume ((K.homothety 0 (ρ : ℝ)).carrier : Set _) =
      ENNReal.ofReal |(ρ : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))| *
        volume (K.carrier : Set _) :=
    ConvexSpaceBody.volume_homothety K 0 (ρ : ℝ)
  have hvolMain : volume (Qρ.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ (Prism3D.enclosureVolumeConstant C₀ : ENNReal) *
          volume ((K.homothety 0 (ρ : ℝ)).carrier : Set _) := by
    calc
      volume (Qρ.carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = ENNReal.ofReal |(ρ : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))| *
              volume (Q.carrier : Set _) := hQρvol
      _ ≤ ENNReal.ofReal |(ρ : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))| *
              ((Prism3D.enclosureVolumeConstant C₀ : ENNReal) * volume (K.carrier : Set _)) :=
          mul_le_mul' le_rfl hQvol
      _ = (Prism3D.enclosureVolumeConstant C₀ : ENNReal) *
              (ENNReal.ofReal |(ρ : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))| *
                volume (K.carrier : Set _)) := by
          ac_rfl
      _ = (Prism3D.enclosureVolumeConstant C₀ : ENNReal) *
              volume ((K.homothety 0 (ρ : ℝ)).carrier : Set _) := by
          rw [hKhvol]
  have hConst : Prism3D.enclosureVolumeConstant C₀ ≤ slabPrismEnclosureConstant C₀ := by
    unfold Prism3D.enclosureVolumeConstant slabPrismEnclosureConstant
    calc
      (48 : NNReal) * C₀ ^ 6 ≤ 2 ^ 20 * C₀ ^ 6 :=
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg (by positivity) 6)
      _ ≤ max 1 (2 ^ 20 * C₀ ^ 6) := le_max_right _ _
  have hSecond : volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ (slabPrismEnclosureConstant C₀ : ENNReal) *
          volume ((K.homothety 0 (ρ : ℝ)).carrier : Set _) := by
    simpa [P] using
      hvolMain.trans (mul_le_mul' (ENNReal.coe_le_coe.mpr hConst) le_rfl)
  -- third conclusion
  have hThird : P.shade = (V.homothety 0 hρ0).shade := rfl
  exact ⟨P, hFirst, hSecond, hThird⟩

/-- **Enclosing the rescaled bodies in exact prisms** (blueprint
`lem:ml2slabPrismEnclosure`, absorbing blueprint `lem:ml2slabRescaleTransport`).

`ShadedPrism3D.multiplicity_le_rpow` (GWZ Lemma 6.9) is stated for prisms with *exact*
half-widths, whereas by (C4) the bodies of `𝕎'_B` are convex bodies whose affine thicknesses
are only comparable to `(r₁, b, a)`, with the constant `C₀`. This lemma performs the passage,
with its loss written out: for each body take the box of
`Kakeya.VeryNotSticky.slabPrismEnclosureConstant` aligned with its John ellipsoid, whose exact
half-widths are `C₀ a × C₀ b × C₀ r₁`, and apply the dilation `x ↦ (C₀ r₁)⁻¹ • x` to the whole
configuration. The resulting prisms have exact half-widths `a' × b' × 1` with `a' = a / r₁`
and `b' = b / r₁`.

The three conclusions are ratios of volumes, hence unaffected by the dilation. The shadings
are unchanged as sets, so `μ` is unchanged. For `λ` the numerator is unchanged and the
denominator grows by at most `C_{lem:ml2slabPrismEnclosure}(C₀)`. For `Δ_max`, if `K` is a
convex body then `K_P ⊆ K` forces `P ⊆ K`, so the sum over the enclosed prisms is at most
`C_{lem:ml2slabPrismEnclosure}(C₀)` times the sum over the enclosed bodies.

The blueprint states the enclosure (`lem:ml2slabPrismEnclosure`) and the transport of the three
ratios across the affine rescaling `L_B` (`lem:ml2slabRescaleTransport`) as two lemmas, the
second one relative to the plank presentation of blueprint `lem:ml2plankpresentation` (Lean
`Kakeya.VeryNotSticky.plankPresentation`, which lives in the non-slab file and is therefore not
available here without an import cycle). Both are folded into this single statement, which is
stated directly for the bodies of `𝕎'_B`: the intermediate plank family never has to be named,
and the transport of `λ`, `μ` and `Δ_max` across a homothety is already available as
`ShadedBody.multiplicity_homothety`, `Kakeya.maxDensity_homothety` and their translation
companions.

The normalization by `(C₀ r₁)⁻¹` rather than by `r₁⁻¹` is what keeps the small half-width
*exactly* `a / r₁`. Enclosing without renormalizing would give prisms of small half-width
`C₀ a / r₁`, and then the exponent `ε` of `Kakeya.VeryNotSticky.slabEpsRange`, which is read
off that half-width, would acquire a `δ`-dependent shift of size `log C₀ / log δ⁻¹`; the
window of `slabEpsRange` would no longer have endpoints depending on `exscal` alone, and
`Kakeya.VeryNotSticky.slabMultBoundConstant` would not be a function of `exscal` alone.

Unlike `Kakeya.VeryNotSticky.plankPresentation`, this statement needs no sharpened middle-scale
hypothesis. That lemma *produces* its `a'` and `b'`, so it has to prove `b' ≤ 1` itself, and
since the middle half-width of the transported body is only known to be at most `C₀ (b / r₁)`
it assumes `C₀ * b ≤ r₁` for that purpose. Here `a'` and `b'` are *given*, pinned to `a / r₁`
and `b / r₁` by `ha'` and `hb'`, and the two order relations `a' ≤ b' ≤ 1` that the type
`ShadedPrism3D a' b' 1` requires are the hypotheses `hab'` and `hb1'`; the renormalization by
`(C₀ r₁)⁻¹` rather than by `r₁⁻¹` is exactly what removes the factor `C₀` from the half-widths,
so `b ≤ r₁` — that is, `hb1'` — is all that is needed. At the call site both `hab'` and `hb1'`
come from `δ ≤ a ≤ b ≤ δ^{exscal} = r₁` of (C4), the field
`Kakeya.VeryNotSticky.hdims`, with no smallness condition on `δ`. -/
theorem slabPrismEnclosure {ω : Type*} (t : Finset ω)
    (Wb : ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Wsh : ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {a b r₁ C₀ a' b' : NNReal} (hC₀ : 1 ≤ C₀) (ha : 0 < a) (hr₁ : 0 < r₁)
    (ha' : a' = a / r₁) (hb' : b' = b / r₁) (hab' : a' ≤ b') (hb1' : b' ≤ 1)
    (hshade : ∀ j ∈ t, (Wsh j).toConvexSpaceBody = Wb j)
    (hthick : ∀ j ∈ t, HasThicknesses (Wb j).carrier C₀ ![(r₁ : ℝ), (b : ℝ), (a : ℝ)]) :
    ∃ P : ω → ShadedPrism3D a' b' 1 hab' hb1' le_rfl,
      multiplicity t (fun j ↦ (P j).toShadedBody) = multiplicity t Wsh ∧
      fullness t Wsh ≤
        slabPrismEnclosureConstant C₀ * fullness t (fun j ↦ (P j).toShadedBody) ∧
      maxDensity t (fun j ↦ (P j).toConvexSpaceBody) ≤
        (slabPrismEnclosureConstant C₀ : ENNReal) * maxDensity t Wb := by
  let ρ : NNReal := (C₀ * r₁)⁻¹
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hC₀
  have hC₀r₁ : 0 < C₀ * r₁ := mul_pos hC₀pos hr₁
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact inv_pos.mpr hC₀r₁
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  have hρ0 : (ρ : ℝ) ≠ 0 := by exact_mod_cast hρne
  have hC0ne : (C₀ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hC₀pos)
  have hr1ne : (r₁ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr₁)
  have ha'' : a' = ρ * (C₀ * a) := by
    rw [ha']
    dsimp [ρ]
    rw [← NNReal.coe_inj]
    push_cast
    field_simp [hC0ne, hr1ne]
  have hb'' : b' = ρ * (C₀ * b) := by
    rw [hb']
    dsimp [ρ]
    rw [← NNReal.coe_inj]
    push_cast
    field_simp [hC0ne, hr1ne]
  have hone : (1 : NNReal) = ρ * (C₀ * r₁) := by
    dsimp [ρ]
    rw [← NNReal.coe_inj]
    push_cast
    field_simp [hC0ne, hr1ne]
  have hab : a ≤ b := by
    have h' : a / r₁ ≤ b / r₁ := by simpa [ha', hb'] using hab'
    exact (div_le_div_iff_of_pos_right hr₁).mp h'
  have hCab : C₀ * a ≤ C₀ * b := mul_le_mul' (le_refl C₀) hab
  have hbr : b ≤ r₁ := by
    have h' : b / r₁ ≤ 1 := by simpa [hb'] using hb1'
    exact (div_le_one hr₁).mp h'
  have hCbr : C₀ * b ≤ C₀ * r₁ := mul_le_mul' (le_refl C₀) hbr
  -- STEP 1: the family, by choice.
  have key : ∀ j : ω, ∃ P : ShadedPrism3D a' b' 1 hab' hb1' le_rfl,
      j ∈ t →
        ((Wb j).homothety 0 (ρ : ℝ) ≤ P.toConvexSpaceBody ∧
         volume (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
           ≤ (slabPrismEnclosureConstant C₀ : ENNReal)
               * volume (((Wb j).homothety 0 (ρ : ℝ)).carrier : Set _) ∧
         P.shade = ((Wsh j).homothety 0 hρ0).shade) := by
    intro j
    by_cases hj : j ∈ t
    · obtain ⟨P, h1, h2, h3⟩ :=
        slabPrismEnclosureBody hC₀ hρ0 ha'' hb'' hone hab' hb1' hCab hCbr
          (Wb j) (Wsh j) (hshade j hj) (hthick j hj)
      exact ⟨P, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨Classical.arbitrary _, fun h => absurd h hj⟩
  choose P hP using key
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [← ShadedBody.multiplicity_homothety t Wsh (0 : EuclideanSpace ℝ (Fin 3)) hρ0]
    exact ShadedBody.multiplicity_eq_of_forall_shade_eq t (fun j => (P j).toShadedBody)
      (fun j => (Wsh j).homothety (0 : EuclideanSpace ℝ (Fin 3)) hρ0)
      (fun j hj => (hP j hj).2.2)
  · rw [← ShadedBody.fullness_homothety t Wsh (0 : EuclideanSpace ℝ (Fin 3)) hρ0]
    have hCpos : 0 < slabPrismEnclosureConstant C₀ :=
      lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) (one_le_slabPrismEnclosureConstant C₀)
    have hsh : ∀ j ∈ t, ((Wsh j).homothety (0 : EuclideanSpace ℝ (Fin 3)) hρ0).shade =
        ((P j).toShadedBody).shade := by
      intro j hj
      exact ((hP j hj).2.2).symm
    have hvol : ∀ j ∈ t, volume ((P j).toShadedBody).carrier ≤
        (slabPrismEnclosureConstant C₀ : ENNReal) *
          volume (((Wsh j).homothety (0 : EuclideanSpace ℝ (Fin 3)) hρ0).carrier) := by
      intro j hj
      have hcar : ((Wsh j).homothety (0 : EuclideanSpace ℝ (Fin 3)) hρ0).toConvexSpaceBody =
          (Wb j).homothety 0 (ρ : ℝ) := by
        rw [ShadedBody.homothety_toConvexSpaceBody, hshade j hj]
      rw [hcar]
      simpa using (hP j hj).2.1
    exact ShadedBody.fullness_le_of_volume_carrier_le t
      (fun j => (Wsh j).homothety (0 : EuclideanSpace ℝ (Fin 3)) hρ0)
      (fun j => (P j).toShadedBody) hCpos hsh hvol
  · have hsub : ∀ j ∈ t, (Wb j).homothety 0 (ρ : ℝ) ≤ (P j).toConvexSpaceBody := by
      intro j hj
      exact (hP j hj).1
    have hvol' : ∀ j ∈ t, volume ((P j).toConvexSpaceBody).carrier ≤
        (slabPrismEnclosureConstant C₀ : ENNReal) *
          volume (((Wb j).homothety 0 (ρ : ℝ)).carrier) := by
      intro j hj
      simpa using (hP j hj).2.1
    have hmd := Kakeya.maxDensity_le_of_carrier_subset t
      (fun j => (Wb j).homothety 0 (ρ : ℝ)) (fun j => (P j).toConvexSpaceBody)
      hsub hvol'
    rwa [maxDensity_homothety t Wb (0 : EuclideanSpace ℝ (Fin 3)) hρ0] at hmd

/-! ### The scales and the exponent of GWZ Lemma 6.9 -/

/-- **The retained family of factoring bodies is non-empty** (blueprint
`lem:ml2slabBodiesNonempty`).

For the empty family both sums defining `λ` vanish, so `λ(∅, ·) = 0`, whereas the density
bound (T2) — the field `Kakeya.ThinCase.ThinBall.fullness_bodies`, read at the `tb` index `2η`
of `Kakeya.VeryNotSticky.ThinConfig.tb` — asserts `δ^{6η} ≤ C λ(𝕎'_B, Y_{𝕎'_B})` with
`δ^{6η} > 0`, since `δ > 0` by `cfg.hδ`.

This is what supplies the hypothesis `hs : s.Nonempty` of
`ShadedPrism3D.multiplicity_le_rpow`. -/
theorem slabBodiesNonempty (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs) :
    (tc.thinBall hB).bodies'.Nonempty := by
  by_contra h
  have hemp : (tc.thinBall hB).bodies' = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hδposE : (0 : ENNReal) < (cfg.δ : ENNReal) := ENNReal.coe_pos.mpr cfg.hδ
  have hδtopE : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hpowpos : (0 : ENNReal) < (cfg.δ : ENNReal) ^ (3 * (2 * cfg.η)) :=
    ENNReal.rpow_pos hδposE hδtopE
  have hfull0 : ShadedBody.fullness ∅ (tc.thinBall hB).W = 0 := by
    simp [ShadedBody.fullness, ShadedBody.fullness']
  have hfb0 : (cfg.δ : ENNReal) ^ (3 * (2 * cfg.η)) ≤ (0 : ENNReal) := by
    have hfb := (tc.thinBall hB).fullness_bodies
    rw [hemp] at hfb
    simpa [hfull0] using hfb
  exact (not_lt_of_ge hfb0) hpowpos

/-- **The rescaled thicknesses** (blueprint `lem:ml2slabScaleBounds`).

Substituting `r₁ = δ^{exscal}` into `a' = a / r₁` and `b' = b / r₁`: the chain
`δ ≤ a ≤ δ^{1-τ}` of (C4) and of the thin case gives the two-sided bound
`δ^{1-exscal} ≤ a' ≤ δ^{1-τ-exscal}`, and the slab hypothesis `b ≥ δ^{2 exscal}` gives
`b' ≥ δ^{exscal}`, which is the middle-thickness hypothesis of
`ShadedPrism3D.multiplicity_le_rpow` at the parameter `ε` of
`Kakeya.VeryNotSticky.slabEpsRange`. -/
theorem slabScaleBounds (cfg : VeryNotSticky.{u}) {τ : ℝ}
    (hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    (hslab : cfg.δ ^ (2 * cfg.exscal) ≤ cfg.b) :
    cfg.δ ^ (1 - cfg.exscal) ≤ cfg.a / cfg.r₁ ∧
      cfg.a / cfg.r₁ ≤ cfg.δ ^ (1 - τ - cfg.exscal) ∧
      cfg.δ ^ cfg.exscal ≤ cfg.b / cfg.r₁ := by
  have hr₁ : 0 < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hr₁]
    calc
      cfg.δ ^ (1 - cfg.exscal) * cfg.r₁ = cfg.δ ^ ((1 - cfg.exscal) + cfg.exscal) := by
        rw [NNReal.rpow_add cfg.hδ.ne']; rfl
      _ = cfg.δ := by rw [sub_add_cancel, NNReal.rpow_one]
      _ ≤ cfg.a := cfg.hdims.1
  · rw [div_le_iff₀ hr₁]
    calc
      cfg.a ≤ cfg.δ ^ (1 - τ) := hthin
      _ = cfg.δ ^ ((1 - τ - cfg.exscal) + cfg.exscal) := by rw [sub_add_cancel]
      _ = cfg.δ ^ (1 - τ - cfg.exscal) * cfg.r₁ := by
        rw [NNReal.rpow_add cfg.hδ.ne']; rfl
  · rw [le_div_iff₀ hr₁]
    calc
      cfg.δ ^ cfg.exscal * cfg.r₁ = cfg.δ ^ (cfg.exscal + cfg.exscal) := by
        rw [NNReal.rpow_add cfg.hδ.ne']; rfl
      _ = cfg.δ ^ (2 * cfg.exscal) := by
        rw [show cfg.exscal + cfg.exscal = 2 * cfg.exscal by ring]
      _ ≤ cfg.b := hslab

/-- **The window of the exponent `ε`** (blueprint `lem:ml2slabEpsRange`).

Write `a' = δ^θ` with `θ = log a' / log δ`. Since `0 < δ < 1` the map `s ↦ δ^s` is strictly
decreasing, so the two hypotheses read `1 - τ - exscal ≤ θ ≤ 1 - exscal`, and `θ > 0` because
`τ + exscal < 1` (the field `Kakeya.VeryNotSticky.CaseParams.thinScale`); hence `a' < 1`. The
defining equation `(a')^ε = δ^{exscal}` is `ε θ = exscal`, so `ε = exscal / θ`, and the
displayed window is the image of the window for `θ` under the decreasing map
`θ ↦ exscal / θ` on `θ > 0`.

The exponent is bound *existentially*, and `0 < a' < 1` is part of the conclusion rather than
of the hypotheses. This is what makes the lemma usable: the caller
(`Kakeya.VeryNotSticky.slabMultBound`) has the two-sided bound on `a'` and nothing else, and
cannot exhibit an `ε` with `(a')^ε = δ^{exscal}` before knowing `0 < a' < 1` — for `a' = 1` no
such `ε` exists. The same two facts are, in addition, two of the four side conditions of
`ShadedPrism3D.multiplicity_le_rpow`, applied to a prism family whose small half-width is `a'`.

The defining equation is stated in `ℝ≥0∞`, which is the currency of
`ShadedPrism3D.multiplicity_le_rpow` and of `Kakeya.VeryNotSticky.slabRpowIdentity`, the two
declarations that consume it; the two-sided bound on `a'` is stated in `ℝ≥0`, which is the
currency of `Kakeya.VeryNotSticky.slabScaleBounds`, the declaration that produces it.

Only the lower bound of the window is consumed, by `Kakeya.VeryNotSticky.slabMultBound` through
`Kakeya.VeryNotSticky.slab1Constant_antitone`; the upper bound is recorded because it is what
shows the window is a window, and because it makes visible that `ε ≈ exscal`. -/
theorem slabEpsRange {δ a' : NNReal} {exscal τ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hexscal : 0 < exscal) (hthinScale : τ + exscal < 1)
    (hlo : δ ^ (1 - exscal) ≤ a') (hhi : a' ≤ δ ^ (1 - τ - exscal)) :
    0 < a' ∧ a' < 1 ∧ ∃ ε : ℝ, (a' : ENNReal) ^ ε = (δ : ENNReal) ^ exscal ∧
      exscal / (1 - exscal) ≤ ε ∧ ε ≤ exscal / (1 - τ - exscal) := by
  let d : ℝ := (δ : ℝ)
  let x : ℝ := (a' : ℝ)
  have hd : 0 < d := by exact_mod_cast hδ
  have hd1 : d < 1 := by exact_mod_cast hδ1
  have hlogd_neg : Real.log d < 0 := Real.log_neg hd hd1
  have hlogd_ne : Real.log d ≠ 0 := ne_of_lt hlogd_neg
  let θ : ℝ := Real.log x / Real.log d
  have hlo' : d ^ (1 - exscal) ≤ x := by exact_mod_cast hlo
  have hhi' : x ≤ d ^ (1 - τ - exscal) := by exact_mod_cast hhi
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.rpow_pos_of_pos hd (1 - exscal)) hlo'
  have hcond_pos : 0 < 1 - τ - exscal := by linarith
  have hθ_ge : 1 - τ - exscal ≤ θ := by
    have hlog : Real.log x ≤ Real.log (d ^ (1 - τ - exscal)) :=
      Real.log_le_log hx_pos hhi'
    rw [Real.log_rpow hd] at hlog
    rw [le_div_iff_of_neg hlogd_neg]
    exact hlog
  have hθ_ge_pos : 0 < θ := lt_of_lt_of_le hcond_pos hθ_ge
  have hθ_ne : θ ≠ 0 := ne_of_gt hθ_ge_pos
  have hθ_le : θ ≤ 1 - exscal := by
    have hlog : Real.log (d ^ (1 - exscal)) ≤ Real.log x :=
      Real.log_le_log (Real.rpow_pos_of_pos hd (1 - exscal)) hlo'
    rw [Real.log_rpow hd] at hlog
    rw [div_le_iff_of_neg hlogd_neg]
    exact hlog
  have h1e_pos : 0 < 1 - exscal := lt_of_lt_of_le hθ_ge_pos hθ_le
  have hx_eq : x = d ^ θ := by
    have hmult : Real.log d * (Real.log x / Real.log d) = Real.log x := by
      field_simp [hlogd_ne]
    rw [Real.rpow_def_of_pos hd, hmult]
    exact (Real.exp_log hx_pos).symm
  have hx_lt_one : x < 1 := by
    rw [hx_eq]
    simpa [Real.rpow_zero] using (Real.rpow_lt_rpow_left_iff_of_base_lt_one hd hd1).2 hθ_ge_pos
  let ε : ℝ := exscal / θ
  have hε_eq_real : x ^ ε = d ^ exscal := by
    dsimp [ε]
    rw [hx_eq, ← Real.rpow_mul (le_of_lt hd)]
    congr 1
    field_simp [hθ_ne]
  have ha'_pos : 0 < a' := by exact_mod_cast hx_pos
  have ha'_lt_one : a' < 1 := by exact_mod_cast hx_lt_one
  have hafter_NN : a' ^ ε = δ ^ exscal := by
    rw [← NNReal.coe_inj]
    simpa [NNReal.coe_rpow, ε, x, d] using hε_eq_real
  have ha'_ne : a' ≠ 0 := ne_of_gt ha'_pos
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ
  have henn : (a' : ENNReal) ^ ε = (δ : ENNReal) ^ exscal := by
    rw [← ENNReal.coe_rpow_of_ne_zero ha'_ne, ← ENNReal.coe_rpow_of_ne_zero hδ_ne]
    exact congrArg (fun t : NNReal ↦ (t : ENNReal)) hafter_NN
  have hlow_win : exscal / (1 - exscal) ≤ exscal / θ := by
    rw [div_le_div_iff₀ h1e_pos hθ_ge_pos]
    exact mul_le_mul_of_nonneg_left hθ_le (le_of_lt hexscal)
  have hhigh_win : exscal / θ ≤ exscal / (1 - τ - exscal) := by
    rw [div_le_div_iff₀ hθ_ge_pos hcond_pos]
    exact mul_le_mul_of_nonneg_left hθ_ge (le_of_lt hexscal)
  refine ⟨ha'_pos, ha'_lt_one, ε, henn, ?_, ?_⟩
  · simpa [ε] using hlow_win
  · simpa [ε] using hhigh_win

/-- **The gain of GWZ Lemma 6.9 is read at the coarse scale** (blueprint
`lem:ml2slabRpowIdentity`).

Raising `(a')^ε = δ^{exscal}` to the power `-8`: `ENNReal.rpow_mul` gives
`(a')^{-8ε} = ((a')^ε)^{-8}` and `(δ^{exscal})^{-8} = δ^{-8 exscal}`, and the hypothesis
identifies the two middle terms.

No positivity or finiteness side condition is needed: `ENNReal.rpow_mul` holds for every base
in `[0, ∞]`, the degenerate cases `0` and `∞` being interchanged rather than lost by a negative
exponent. Both `a'` and `δ` are nevertheless positive where the lemma is applied.

The identity is separated out because it is the only point at which the conclusion of
`ShadedPrism3D.multiplicity_le_rpow`, which is expressed in the small half-width `a'` of the
prisms, is rewritten in the scale `δ` of the ambient configuration; keeping the `ℝ≥0∞` power
arithmetic out of the proof of `Kakeya.VeryNotSticky.slabMultBound` keeps that proof to the
four hypothesis checks it is really about. -/
theorem slabRpowIdentity {δ a' : NNReal} {exscal ε : ℝ}
    (heps : (a' : ENNReal) ^ ε = (δ : ENNReal) ^ exscal) :
    (a' : ENNReal) ^ (-8 * ε) = (δ : ENNReal) ^ (-8 * exscal) := by
  rw [mul_comm (-8) ε, mul_comm (-8) exscal]
  rw [ENNReal.rpow_mul, ENNReal.rpow_mul, heps]

/-- **The constant of GWZ Lemma 6.9 is at least one** (blueprint `lem:slab1ConstantAntitone`).

`C_{6.9}(η) = 2695 (2 + 1/(2 η log 2)) ≥ 2695 · 2 ≥ 1` for `η > 0`. -/
lemma one_le_slab1Constant {η : ℝ} (hη : 0 < η) :
    1 ≤ ShadedPrism3D.multiplicity_le_rpow.C η := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hnn : (0 : ℝ) ≤ 1 / (2 * η * Real.log 2) := by positivity
  have hreal : (1 : ℝ) ≤ 2695 * (2 + 1 / (2 * η * Real.log 2)) := by nlinarith
  rw [ShadedPrism3D.multiplicity_le_rpow.C, Real.one_le_toNNReal]
  exact hreal

/-- **Monotonicity of the constant of GWZ Lemma 6.9** (blueprint `lem:slab1ConstantAntitone`).

On `(0, ∞)` the map `η ↦ 1 / (2 η log 2)` is positive and decreasing, since `log 2 > 0`;
adding `2` and multiplying by `2695 > 0` preserves both properties. Consequently, if
`0 < η₀ ≤ η` then `C_{6.9}(η) ≤ C_{6.9}(η₀)`.

This is what lets `Kakeya.VeryNotSticky.slabMultBoundConstant` be evaluated at the *left*
endpoint `exscal / (1 - exscal)` of the window of `Kakeya.VeryNotSticky.slabEpsRange`, which
depends only on the exponents fixed once and for all, while the parameter `ε` at which GWZ
Lemma 6.9 is actually applied moves with `δ`. -/
lemma slab1Constant_antitone {η₀ η : ℝ} (hη₀ : 0 < η₀) (hle : η₀ ≤ η) :
    ShadedPrism3D.multiplicity_le_rpow.C η ≤ ShadedPrism3D.multiplicity_le_rpow.C η₀ := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hη : 0 < η := lt_of_lt_of_le hη₀ hle
  have hpos : (0 : ℝ) < 2 * η * Real.log 2 := by positivity
  have hpos₀ : (0 : ℝ) < 2 * η₀ * Real.log 2 := by positivity
  have hmul : 2 * η₀ * Real.log 2 ≤ 2 * η * Real.log 2 := by gcongr
  have hdiv : (1 : ℝ) / (2 * η * Real.log 2) ≤ 1 / (2 * η₀ * Real.log 2) :=
    (one_div_le_one_div hpos hpos₀).mpr hmul
  have hreal :
      (2695 * (2 + 1 / (2 * η * Real.log 2)) : ℝ) ≤
       2695 * (2 + 1 / (2 * η₀ * Real.log 2)) := by
    nlinarith
  rw [ShadedPrism3D.multiplicity_le_rpow.C, ShadedPrism3D.multiplicity_le_rpow.C]
  exact Real.toNNReal_le_toNNReal hreal

/-- **Constant in Lemma `lem:ml2slabMultBound`** (blueprint `def:ml2slabMultBoundConstant`).

`C_{lem:ml2slabMultBound}(exscal) = C_{6.9}(exscal / (1 - exscal))`, where `C_{6.9}` is
`ShadedPrism3D.multiplicity_le_rpow.C`. It is a function of the coarse-scale exponent `exscal`
alone: not of `δ`, not of the ball `B`, not of the family or its factoring, not of the
thin-case exponent `τ`, and not of `C₀`.

The value at the *left* endpoint of the window of `Kakeya.VeryNotSticky.slabEpsRange` is the
right one. GWZ Lemma 6.9 is applied in `Kakeya.VeryNotSticky.slabMultBound` to the prism family
of `Kakeya.VeryNotSticky.slabPrismEnclosure`, whose small half-width is `a' = a / r₁`, with the
parameter `ε` determined by `(a')^ε = δ^{exscal}`; by `slabEpsRange`,
`ε ∈ [exscal/(1-exscal), exscal/(1-τ-exscal)]`. So `ε` is not a fixed number: it moves with
`a'`, hence with `δ`, and `C_{6.9}(ε)` moves with it. What does not move is the left endpoint.
Since `C_{6.9}` is decreasing (`Kakeya.VeryNotSticky.slab1Constant_antitone`) and
`ε ≥ exscal/(1-exscal)`, we get `C_{6.9}(ε) ≤ C_{lem:ml2slabMultBound}(exscal)` for every
admissible `ε`, uniformly in `δ`. Evaluating at the right endpoint would not do: it is the
smaller of the two values, so not an upper bound, and it would carry a spurious dependence
on `τ`. -/
noncomputable def slabMultBoundConstant (exscal : ℝ) : NNReal :=
  ShadedPrism3D.multiplicity_le_rpow.C (exscal / (1 - exscal))

lemma one_le_slabMultBoundConstant {exscal : ℝ} (h0 : 0 < exscal) (h1 : exscal < 1) :
    1 ≤ slabMultBoundConstant exscal :=
  one_le_slab1Constant (div_pos h0 (by linarith))

/-- **Constant in Lemma `lem:ml2slabUnionFromMult`** (blueprint
`def:ml2slabUnionFromMultConstant`).

`C_{lem:ml2slabUnionFromMult}(C, C₀) = C · C_{lem:ml2thinUnionLower}(C, C₀)`, the product of
the two losses `Kakeya.VeryNotSticky.slabUnionFromMult` composes: the first is the loss in the
density bound (T2), the second is the loss of `Kakeya.ThinCase.unionLower_thin` when the
estimate is transported from the factoring bodies to the tube segments. It is therefore *not*
the constant of either.

Like both of its factors it depends on `C` and on `C₀` only: not on `δ`, and not on the ball
`B`. Ball-independence is what makes the resulting estimate summable over `B ∈ 𝔅` in
`Kakeya.goalMult_of_b_ge`, where a per-ball constant would have to be replaced by a supremum
over `𝔅` that no hypothesis controls. -/
noncomputable def slabUnionFromMultConstant (C C₀ : NNReal) : NNReal :=
  C * ThinCase.unionLowerConstant C C₀

lemma one_le_slabUnionFromMultConstant {C C₀ : NNReal} (hC : 1 ≤ C) :
    1 ≤ slabUnionFromMultConstant C C₀ := by
  simpa [slabUnionFromMultConstant] using
    mul_le_mul' hC (ThinCase.one_le_unionLowerConstant C C₀)

/-- **Constant in Lemma `lem:ml2slabUnion`** (blueprint `def:ml2slabUnionConstant`).

`C_{lem:ml2slabUnion}(C, C₀, exscal) = C_{lem:ml2slabUnionFromMult}(C, C₀) ·
C_{lem:ml2slabMultBound}(exscal)`.

`Kakeya.VeryNotSticky.slabUnion` substitutes the multiplicity bound of
`Kakeya.VeryNotSticky.slabMultBound` into `Kakeya.VeryNotSticky.slabUnionFromMult`, and the
multiplicity enters the latter through the factor `M` on the right-hand side; so the two
losses multiply and this constant is their product, and is *not* the constant of either
lemma. It depends on `C`, on `C₀` and on `exscal` only, and in particular neither on `δ` nor
on the ball `B`. -/
noncomputable def slabUnionConstant (C C₀ : NNReal) (exscal : ℝ) : NNReal :=
  slabUnionFromMultConstant C C₀ * slabMultBoundConstant exscal

lemma one_le_slabUnionConstant {C C₀ : NNReal} {exscal : ℝ} (hC : 1 ≤ C) (h0 : 0 < exscal)
    (h1 : exscal < 1) : 1 ≤ slabUnionConstant C C₀ exscal := by
  simpa [slabUnionConstant] using
    mul_le_mul' (one_le_slabUnionFromMultConstant (C₀ := C₀) hC)
      (one_le_slabMultBoundConstant h0 h1)

/-! ### What the slab case assumes -/

/-- **The segments retained by the factoring** (blueprint `def:ml2slabRetainedSegments`).

`𝕋_B^{𝕎'} = {T_B ∈ 𝕋_B : W(T_B) ∈ 𝕎'_B}`, the set of tube segments of the ball `B` whose
block was retained by the factoring proposition. The block of a segment is `bd.blk`, which is
well defined because the decomposition `𝕋_B = ⨆_{W ∈ 𝕎_B} 𝕋_{B,W}` of (C4) is a partition.

The restriction is necessary and costs nothing: a segment whose block was discarded by the
factoring is not contained in any body of `𝕎'_B`, so it cannot be counted on the right-hand
side of `Kakeya.VeryNotSticky.slabSegmentSumSplit`, while by (T3)
(`Kakeya.ThinCase.ThinBall.shade_containment`) every segment carrying any of the final shading
`Y'_B` has its block in `𝕎'_B`. -/
def retainedSegments {cfg : VeryNotSticky.{u}} {bd : BallData cfg} (tc : ThinConfig cfg bd)
    {B : bd.bι} (hB : B ∈ bd.bs) : Finset bd.σ :=
  (bd.segs B).filter fun p ↦ bd.blk p ∈ (tc.thinBall hB).bodies'

/-- **Constant in Definition `hyp:ml2slabinputs`** (blueprint `def:ml2slabInputsConstant`).

`C_{hyp:ml2slabinputs}(C₀) = max(1, C_{lem:ml2slabPrismEnclosure}(2 C₀) ·
volume_comparison.C 3)`, with `volume_comparison.C 3 = 4³ · 3! = 384` the dimensional volume
comparison constant. It is written as `Metric.volume_comparison.C 3` rather than as the
blueprint's `C_{lem:outerFactoringVolumeControlled}(3)`, which is
`ShadedBody.outerFactoringFamily_volumeControlled.C 3`, because the latter is by definition the
former and lives in a module this file does not import; the same choice is made by
`Kakeya.ThinCase.factoringApplyConstant`.

Two factors, and each is one of the two losses that separate the *geometric* bodies `bd.Wb j`
of `𝕎'_B`, which are what (C4) controls, from the exact prisms to which GWZ Lemma 6.9 is
finally applied.

*The first factor is the enclosure, evaluated at `2 C₀` and not at `C₀`.* The family that
carries the shading `Y_{𝕎'_B}` — and hence the family whose fullness and whose maximal density
GWZ Lemma 6.9 is asked about — is not `bd.Wb` but the family of enlarged carriers
`fun j ↦ ((tc.thinBall hB).W j).toConvexSpaceBody` (blueprint `def:ml2slabCarriers`), the
upper half of the sandwich `Kakeya.ThinCase.ThinBall.Wb_le_W` /
`Kakeya.ThinCase.ThinBall.W_le_cthickening`. By
`Kakeya.ThinCase.ThinBall.hasThicknesses_W` those carriers inherit the thickness profile
`(r₁, b, a)` of the bodies with the comparison constant *doubled*, and with nothing better
available, the enlargement being by `τ₂(Wb j)`, which is of the same order as the shortest
thickness itself. So `Kakeya.VeryNotSticky.slabPrismEnclosure` has to be run at comparison
constant `2 C₀`. That is the only effect the enlargement has on this factor: the half-widths of
the prisms it produces are still exactly `a' × b' × 1` with `a' = a / r₁` and `b' = b / r₁`,
because `Kakeya.VeryNotSticky.slabPrismEnclosureBody` normalizes by whichever comparison
constant it is handed, so the doubling cancels and the window of
`Kakeya.VeryNotSticky.slabEpsRange` is untouched.

*The second factor is what the passage between the two families costs in `Δ_max`.* The
anti-clustering hypothesis of (C4) is a statement about the geometric bodies, whereas the
enclosure consumes one about the carriers, and `Δ_max` is not monotone in either direction
under an enlargement of the members of a family. What bridges the two is
`Kakeya.ThinCase.ThinBall.isVolumeControlledEnlargement`, which makes the carriers a
`volume_comparison.C 3`-volume-controlled enlargement of `bd.Wb` in the sense of
`ConvexSpaceBody.IsVolumeControlledEnlargement`, together with
`ConvexSpaceBody.IsVolumeControlledEnlargement.maxDensity_le`, which transfers the bound at the
cost of exactly that factor. Nothing more is charged, and in particular no property of the
factoring construction is used, only the sandwich.

On the density side the second factor is not needed: `λ(𝕎'_B, Y_{𝕎'_B})` is already the
fullness of the *shaded* family, whose denominator is the sum of the volumes of the carriers, so
(S1) would run with `C_{lem:ml2slabPrismEnclosure}(2 C₀)` alone. It is charged the product all
the same, because one constant serves both items of the bundle and because
`volume_comparison.C 3 ≥ 1` makes the larger value an admissible threshold for the smaller
requirement; the cost is a fixed numerical factor in a threshold on `δ`, and the exponent
budgets of `Kakeya.VeryNotSticky.CaseParams` are untouched by it.

It is a function of `C₀` alone: not of `δ`, not of `a` or `b`, not of the ball `B`, not of the
family, and not of the exponent parameters. The truncation at `1` is inactive, both factors
being at least `1`, so it changes no value; it is written so that
`Kakeya.VeryNotSticky.one_le_slabInputsConstant` is available without an argument, and to match
the shape of the other constants of this file. -/
noncomputable def slabInputsConstant (C₀ : NNReal) : NNReal :=
  max 1 (slabPrismEnclosureConstant (2 * C₀) * volume_comparison.C 3)

lemma one_le_slabInputsConstant (C₀ : NNReal) : 1 ≤ slabInputsConstant C₀ :=
  le_max_left _ _

/-- **The fibre-mass constant of the canonical-capsule core**.  Refined
`eqvnsfibresize` (l.5377): a capsule fibre of a family of maximal density `A` has at most
`320 · A · r₁^{-2}` members, the `320` coming from the enclosing capsule's volume `316π(δ/r₁)²`
against `|T| ≥ πδ²` (l.5411–5416).  With `r₁ = δ^{exscal}` and `Δ_max ≤ δ^{-η}` this is exactly
the tree's fibre budget `δ^{-(η + 2 exscal)}` times this constant — the exponent is the source's,
the constant is what  adds to it.  A `δ`-free absolute, `cfg`- and `bd`-free, its
own symbol; NOT `Kakeya.VeryNotSticky.fibreCountConstant`, which is the
split fibre count's constant.  The value is the tree's own compiled bound
`#fibre · c₃ δ² ≤ Δ_max · |fibreBody|` (`CanonicalCapsulesFibre.lean`): at `ε = δ`,
`L = r₁/8`, `δ ≤ r₁/16`, `r₁ ≤ 1` it reads
`#fibre ≤ (4356/c₃) · Δ_max · r₁^{-2} = (9801/π) · Δ_max · r₁^{-2} ≈ 3120 · Δ_max · r₁^{-2}`,
over-estimated by `Real.pi_gt_three` to `9801/3 = 3267`; at the producer's actual half-length
`L = r₁/4` (`CoverData.capsuleCore`, `CanonicalCapsulesProducer.lean`, `card_fib_le_fibreMass`)
the compiled bound is `(1960/c₃) · Δ_max · r₁^{-2} ≈ 1403 · Δ_max · r₁^{-2}` — both sit under
`3267`, which therefore stands.  The refined `320` is the same shape at their sharper capsule
geometry.  The producer may raise it to any explicit `δ`-free numeral, and must record the
measurement.

It lives here and not in `MainLemma2/EDConstants.lean` because `EDConstants` transitively
imports this file (measured import closure at `37d9a4ab1`), while `SlabScale` below reads it. -/
def fibreMassConstant : NNReal := 3267

theorem one_le_fibreMassConstant : 1 ≤ fibreMassConstant := by
  unfold fibreMassConstant; norm_num

/-- **The degenerate fibre budget.**  At the pins `m = Cm = 1` of the T3 core the budget
`Cm · m ≤ fibreMassConstant · δ^{-(η + 2 exscal)}` holds outright:
`1 ≤ fibreMassConstant`, and `1 ≤ δ^{-(η + 2 exscal)}` since `δ ≤ 1` and `η + 2 exscal > 0`. -/
theorem fibreBudget_of_pins {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    (hm : bd.m = 1) (hCm : bd.Cm = 1) :
    (bd.Cm : ENNReal) * (bd.m : ENNReal) ≤
      (fibreMassConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) := by
  rw [hm, hCm]
  simp only [ENNReal.coe_one, mul_one]
  have h1 : (1 : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) :=
    ENNReal.one_le_rpow_of_pos_of_le_one_of_neg (ENNReal.coe_pos.mpr cfg.hδ)
      (ENNReal.coe_le_one_iff.mpr cfg.hδ1)
      (by have := cfg.hη; have := cfg.hexscal; linarith)
  calc (1 : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) := h1
    _ = 1 * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) := (one_mul _).symm
    _ ≤ (fibreMassConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) := by
        gcongr
        exact_mod_cast one_le_fibreMassConstant

/-- **Fixed-scale thresholds for the slab case** (blueprint `hyp:ml2slabscale`).

The `tc`-aware companion of `Kakeya.VeryNotSticky.CaseScale`: the strict inequality `δ < 1`
together with the four thresholds the slab case needs. It exists as a separate
structure for one reason: two of its assertions mention the thin-case comparison constant
`tc.C`, which `Kakeya.VeryNotSticky.CaseScale` does not see, being stated before the thin-case
data is constructed. Accordingly it takes `cfg`, `bd`, `tc` and `τ`.

No enlargement of the *data* of the standing configuration can supply these: `cfg` fixes `δ`
before the case split and `Kakeya.VeryNotSticky.CaseParams` deliberately records no condition
on `δ` at all, while `density` and `final` compare `δ` with `tc.C` and `bd.C₀`, and every field
of `Kakeya.ThinCase.ThinBall` is of the weakening shape `X ≤ C · Y` or `C⁻¹ · X ≤ Y`, so from
any `Kakeya.VeryNotSticky.ThinConfig` with constant `C` one obtains one with an arbitrarily
larger constant. A `δ`-free hypothesis therefore cannot imply them.

The first four assertions hold once the exponent parameters and the constants have been fixed
and `δ` is taken small enough. Each of the three fixed-scale thresholds is of the shape
`C ≤ δ^{-s}` with `s > 0`, the three gaps being `exscal - 6η > 0`
(`Kakeya.VeryNotSticky.CaseParams.slabDensity`), `exscal - 2ϱ > 0`
(`Kakeya.VeryNotSticky.CaseParams.slabBias`, whose separation constant is `2^20 ≥ 2`) and
`β/2 - (12η+12 exscal+3τ) > 0` (`Kakeya.VeryNotSticky.CaseParams.slab`). Each is spent exactly
once: `density` converts the density `δ^{6η}` of (T2) into the input `(a')^ε = δ^{exscal}` that
`ShadedPrism3D.multiplicity_le_rpow` demands, `antiClustering` converts the honest exponent
`2ϱ` of `Kakeya.VeryNotSticky.BallData.bodies_antiClustering` into the `exscal` the same lemma
demands, and `final` is the only place in the slab case where a `δ`-free comparison constant is
discharged — which is what allows the conclusion of `Kakeya.goalMult_of_b_ge` to be the
constant-free currency `Kakeya.VeryNotSticky.goalUnion`. The `δ`-free constants it absorbs are
`C_{lem:ml2slabUnion}(C, C₀, exscal)`, the thin-case constant `C` and the dilation constant
`bd.Cdil` that the repaired clauses (T7) and (C3) put on the right of
`Kakeya.VeryNotSticky.slabMassBound`.

The fifth assertion, `fibreMass`, is of a different kind: it bounds the fibre-count scale
`Cm · m` of (C5) — a datum of `bd`, not a `δ`-free constant — by the budgeted power
`δ^{-(η+2 exscal)}`. It is what the repaired (T7) costs beyond `δ^{2η}`: `m` is bounded only
through the size of the parent families `|𝕋(T_B)|`, so it is not absorbed by a fixed-scale
gap but budgeted, and its budget `η + 2 exscal` is the difference between the exponent
`12η + 12 exscal + 3τ` of `final` and the honest `11η + 10 exscal + 3τ` of
`Kakeya.VeryNotSticky.slabMassBound`, which `Kakeya.VeryNotSticky.slabVolumeGoal` takes with no
margin since F8 spent the former `4η`. Whoever produces the side data must arrange it.

`deltaLtOne` is grouped here rather than with the exponent budgets because it is a condition on
`δ`: `cfg` records only `δ ≤ 1`, whereas `ShadedPrism3D.multiplicity_le_rpow` and
`Kakeya.VeryNotSticky.slabEpsRange` both need strictness, since at `δ = 1` every scale
collapses and the exponent `ε` is not determined. -/
structure SlabScale (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (tc : ThinConfig cfg bd)
    (τ : ℝ) : Prop where
  /-- `δ < 1`, which `cfg` does not record. -/
  deltaLtOne : cfg.δ < 1
  /-- *Density threshold.* `C · C_{hyp:ml2slabinputs}(C₀) · δ^{exscal} ≤ δ^{6η}`.

  The exponent is `6η` because it is chained against
  `Kakeya.ThinCase.ThinBall.fullness_bodies`, which is asserted at `δ^{3η}` in the structure's
  own index `η` (see that field) and is read by `Kakeya.VeryNotSticky.ThinConfig.tb` at the
  index `2 · cfg.η` — the (C5) exponent in the density clause. The budget that
  discharges it is `Kakeya.VeryNotSticky.CaseParams.slabDensity`, `6η < exscal`, from the
  `η ≤ exscal/8` of `Kakeya.VeryNotSticky.exists_caseParams`. -/
  density : (tc.C : ENNReal) * (slabInputsConstant bd.C₀ : ENNReal) *
    (cfg.δ : ENNReal) ^ cfg.exscal ≤ (cfg.δ : ENNReal) ^ (6 * cfg.η)
  /-- *Anti-clustering threshold.* `C_{hyp:ml2slabinputs}(C₀) · C_bias · δ^{exscal} ≤ δ^{2ϱ}`,
  which converts the honest exponent `2ϱ` of
  `Kakeya.VeryNotSticky.BallData.bodies_antiClustering` into `exscal`. -/
  antiClustering : (slabInputsConstant bd.C₀ : ENNReal) * (bd.Cbias : ENNReal) *
    (cfg.δ : ENNReal) ^ cfg.exscal ≤ (cfg.δ : ENNReal) ^ (2 * cfg.ϱ)
  /-- *Final fixed-scale threshold.*
  `C_fib · C · Cdil · C_{lem:ml2slabUnion}(C, C₀, exscal) · δ^{β/2} ≤ δ^{12η+12 exscal+3τ}`.

  The exponent is the left-hand side of `Kakeya.VeryNotSticky.CaseParams.slab`, as before the
  repair (`9η+10 exscal+3τ` then); the two extra `δ`-free factors `C` and `Cdil` come from the
  repaired (T7) and (C3), and the third,
  `C_fib = Kakeya.VeryNotSticky.fibreMassConstant`, compensates the constant that `fibreMass`
  below now carries, so that `slabVolumeGoal`'s exponent chain
  keeps its zero slack. -/
  final : (fibreMassConstant : ENNReal) * (tc.C : ENNReal) * (bd.Cdil : ENNReal) *
      (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) * (cfg.δ : ENNReal) ^ (cfg.β / 2) ≤
    (cfg.δ : ENNReal) ^ (12 * cfg.η + 12 * cfg.exscal + 3 * τ)
  /-- *Fibre-count budget.* `Cm · m ≤ C_fib · δ^{-(η+2 exscal)}`: the fibre-count scale `m` of
  (C5), with its comparison constant `Cm`, is within the budget `η + 2 exscal` that the repaired
  (T7) charges the slab case for it, up to the `δ`-free
  `C_fib = Kakeya.VeryNotSticky.fibreMassConstant` of the canonical-capsule core. -/
  fibreMass : (bd.Cm : ENNReal) * (bd.m : ENNReal) ≤
    (fibreMassConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal))

/-- The quantitative fields of `SlabScale`, written explicitly.
The proof projects the two defining bounds, including the fixed fibre-mass
constant needed by the final exponent estimate. -/
example {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {tc : ThinConfig cfg bd} {τ : ℝ}
    (ss : SlabScale cfg bd tc τ) :
    ((fibreMassConstant : ENNReal) * (tc.C : ENNReal) * (bd.Cdil : ENNReal) *
        (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) * (cfg.δ : ENNReal) ^ (cfg.β / 2) ≤
      (cfg.δ : ENNReal) ^ (12 * cfg.η + 12 * cfg.exscal + 3 * τ)) ∧
    ((bd.Cm : ENNReal) * (bd.m : ENNReal) ≤
      (fibreMassConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal))) :=
  ⟨ss.final, ss.fibreMass⟩

/-- **Inputs of the slab case** (blueprint `hyp:ml2slabinputs`).

The eight facts used in the proof of `Kakeya.goalMult_of_b_ge`, collected once as a named
bundle rather than restated in each of the six lemmas that consume them.
`Kakeya.VeryNotSticky.slabInputs` produces the bundle, so nothing here is assumed.

They are of two kinds. `deltaLtOne`, `densityThreshold` (S1), `finalThreshold` (S6) and
`fibreMassThreshold` (S7) are *thresholds*: the first three are fixed-scale, of the shape
`C ≤ δ^{-s}` with `s > 0` and `C` independent of `δ`, and (S7) bounds the fibre-count datum
`Cm · m` of (C5) by its budgeted power; they are four of the five fields of
`Kakeya.VeryNotSticky.SlabScale` verbatim, and they are not derivable from `δ`-free data
because `δ` is fixed before the case split.
`bodiesAntiClustering` (S2), `segsDilation` (S3), `tubeCount` (S4) and `segmentMass` (S5) are
items of the standing configuration: (S3) is
`Kakeya.VeryNotSticky.BallData.segs_dilation` of (C3), (S4) is
`Kakeya.VeryNotSticky.tube_count` of (C1) and (S5) is
`Kakeya.VeryNotSticky.ThinConfig.segment_mass` of (T7), each verbatim, while (S2) is
`Kakeya.VeryNotSticky.BallData.bodies_antiClustering` of (C4) restricted to the retained
subfamily and with the two constants discharged against
`Kakeya.VeryNotSticky.SlabScale.antiClustering`.

Every estimate below is stated division-free, so no positivity or finiteness side condition is
needed:

* (S1) reads `C · C_{hyp:ml2slabinputs}(C₀) · δ^{exscal} ≤ δ^{6η}`; it is the only place where
  the budget `6η < exscal` of `Kakeya.VeryNotSticky.CaseParams.slabDensity` is spent, converting
  the density `δ^{6η}` of (T2) at the `tb` index `2η` into the input `(a')^ε = δ^{exscal}` that
  GWZ Lemma 6.9 demands.
* (S2) reads `C_{hyp:ml2slabinputs}(C₀) · Δ_max(𝕎'_B) ≤ δ^{-exscal}`, for every `B ∈ 𝔅`, the
  `Δ_max` being that of the *geometric* bodies `bd.Wb`.
* (S3) reads `r₁² Δ_max(𝕋_B) ≤ Cdil · Δ_max(𝕋)`, the division-free form of the blueprint's
  `Δ_max(𝕋_B) ≤ r₁^{-2} Δ_max(𝕋)` with the comparison constant `bd.Cdil` made explicit.
* (S4) reads `1 ≤ δ |𝕋|`, the division-free form of the blueprint's `|𝕋| ≥ δ^{-1}`.
* (S5) reads `δ^{2η} ∑_{T ∈ 𝕋} |T| ≤ C · Cm · m · ∑_{B ∈ 𝔅} ∑_{T_B ∈ 𝕋_B^{𝕎'}} |T_B|`, with
  `𝕋_B^{𝕎'}` the retained segments `Kakeya.VeryNotSticky.retainedSegments`, the density loss
  and the fibre count made explicit.
* (S6) reads `C · Cdil · C_{lem:ml2slabUnion}(C, C₀, exscal) · δ^{β/2} ≤ δ^{12η+12 exscal+3τ}`,
  the division-free form of the blueprint's
  `C_{lem:ml2slabUnion} ≤ δ^{-(β/2 - (12η+12 exscal+3τ))}` with the two constants of (S3) and
  (S5) adjoined, the exponent being positive by `Kakeya.VeryNotSticky.CaseParams.slab`. It is
  the only place in the slab case where a `δ`-free comparison constant is discharged, which is
  what allows the conclusion to be the constant-free currency
  `Kakeya.VeryNotSticky.goalUnion`.
* (S7) reads `Cm · m ≤ δ^{-(η+2 exscal)}`: the fibre-count scale of (C5) that (S5) puts on the
  right is within its budget `η + 2 exscal`, the difference between the exponent of (S6) and
  the honest `11η+10 exscal+3τ` of `Kakeya.VeryNotSticky.slabMassBound`, which
  `Kakeya.VeryNotSticky.slabVolumeGoal` takes with no margin (F8).

The field `deltaLtOne` is an eighth item, of the same fixed-scale kind as (S1) and (S6):
`Kakeya.VeryNotSticky` records only `δ ≤ 1`, whereas `ShadedPrism3D.multiplicity_le_rpow` and
`Kakeya.VeryNotSticky.slabEpsRange` both need the strict inequality (at `δ = 1` all the scales
collapse and the exponent `ε` is not determined). It comes from
`Kakeya.VeryNotSticky.SlabScale`, with (S1), (S6) and (S7); the blueprint records it with (S1).

The bundle depends on the thin-case exponent `τ`, through (S6) only.

The bundle is *kept* rather than dissolved into the enlarged configuration, and this is a
matter of exposition: the six lemmas below can then name (S1), (S2), (S3) individually, and the
reader is not sent to four different bundles to find out what a given step needs. Every lemma
of this subsubsection that consumes an item takes the structure as an explicit hypothesis, and
`Kakeya.goalMult_of_b_ge` applies `Kakeya.VeryNotSticky.slabInputs` once.

An earlier state of this file carried (S1)–(S6) as *accepted assumptions*, with the slab case
proved modulo them and the whole gap sitting in `Kakeya.goalMult_of_b_ge`. The two changes that
closed that gap were recording the four configuration items where they belong — (S2) on (C4),
(S3) on (C3), (S4) on (C1), (S5) on (T7) — and adding the thresholds as
`Kakeya.VeryNotSticky.SlabScale`, which is threaded into `Kakeya.goalMult_of_b_ge` at the cost
of one argument at its unique call site inside `Kakeya.goalMult_of_a_le`. -/
structure SlabInputs (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (tc : ThinConfig cfg bd)
    (τ : ℝ) : Prop where
  /-- A fixed-scale threshold, recorded with (S1): the configuration only gives `δ ≤ 1`, and
  the strict inequality is what makes the exponent `ε` of
  `Kakeya.VeryNotSticky.slabEpsRange` well defined. -/
  deltaLtOne : cfg.δ < 1
  /-- (S1) *Density threshold.* `C · C_{hyp:ml2slabinputs}(C₀) · δ^{exscal} ≤ δ^{6η}`; see
  `Kakeya.VeryNotSticky.SlabScale.density`, which discharges it, for why the exponent is `6η`. -/
  densityThreshold : (tc.C : ENNReal) * (slabInputsConstant bd.C₀ : ENNReal) *
    (cfg.δ : ENNReal) ^ cfg.exscal ≤ (cfg.δ : ENNReal) ^ (6 * cfg.η)
  /-- (S2) *Anti-clustering of the factoring bodies.*
  `C_{hyp:ml2slabinputs}(C₀) Δ_max(𝕎'_B) ≤ δ^{-exscal}` for every `B ∈ 𝔅`.

  Here `Δ_max(𝕎'_B)` is the maximal density of the *geometric* bodies `bd.Wb`, which is what
  (C4) controls; the passage from them to the enlarged carriers
  `fun j ↦ ((tc.thinBall hB).W j).toConvexSpaceBody`, which is what the enclosure is actually
  applied to, is charged inside `Kakeya.VeryNotSticky.slabInputsConstant` and not here. -/
  bodiesAntiClustering : ∀ (B : bd.bι) (hB : B ∈ bd.bs),
    (slabInputsConstant bd.C₀ : ENNReal) *
        maxDensity (tc.thinBall hB).bodies' bd.Wb ≤
      (cfg.δ : ENNReal) ^ (-cfg.exscal)
  /-- (S3) *Dilation comparison for the segment families.* `r₁² Δ_max(𝕋_B) ≤ Cdil · Δ_max(𝕋)`
  for every `B ∈ 𝔅`. -/
  segsDilation : ∀ B ∈ bd.bs,
    (cfg.r₁ : ENNReal) ^ 2 * maxDensity (bd.segs B) (fun p ↦ (bd.Y p).toConvexSpaceBody) ≤
      (bd.Cdil : ENNReal) * maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)
  /-- (S4) *Tube count.* `1 ≤ δ |𝕋|`, i.e. `|𝕋| ≥ δ^{-1}`. -/
  tubeCount : (1 : ENNReal) ≤ (cfg.δ : ENNReal) * (cfg.s.card : ENNReal)
  /-- (S5) *The segments account for the tubes*, up to the density `δ^{2η}` and the fibre
  count `C · Cm · m`. -/
  segmentMass : (cfg.δ : ENNReal) ^ (2 * cfg.η) *
      ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier ≤
    (tc.C : ENNReal) * (bd.Cm : ENNReal) * (bd.m : ENNReal) *
      ∑ B ∈ bd.bs.attach, ∑ p ∈ retainedSegments tc B.2, volume (bd.Y p).carrier
  /-- (S6) *Final fixed-scale threshold.*
  `C_fib · C · Cdil · C_{lem:ml2slabUnion}(C, C₀, exscal) δ^{β/2} ≤ δ^{12η+12 exscal+3τ}`
  (`C_fib = fibreMassConstant`). -/
  finalThreshold : (fibreMassConstant : ENNReal) * (tc.C : ENNReal) * (bd.Cdil : ENNReal) *
      (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) * (cfg.δ : ENNReal) ^ (cfg.β / 2) ≤
    (cfg.δ : ENNReal) ^ (12 * cfg.η + 12 * cfg.exscal + 3 * τ)
  /-- (S7) *Fibre-count budget.* `Cm · m ≤ C_fib · δ^{-(η+2 exscal)}`. -/
  fibreMassThreshold : (bd.Cm : ENNReal) * (bd.m : ENNReal) ≤
    (fibreMassConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal))

/-- **Anti-clustering passes to the retained subfamily.**

The first step of (S2). Since `𝕎'_B ⊆ 𝕎_B` (`Kakeya.ThinCase.ThinBall.bodies'_subset`), each
competing convex body sees a sub-sum, so `Δ_max(𝕎'_B) ≤ Δ_max(𝕎_B)` by `Kakeya.maxDensity_mono`;
now apply `Kakeya.VeryNotSticky.BallData.bodies_antiClustering` of (C4). -/
theorem slabRetainedAntiClustering (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs) :
    maxDensity (tc.thinBall hB).bodies' bd.Wb ≤
      (bd.Cbias : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) :=
  (maxDensity_mono bd.Wb (tc.thinBall hB).bodies'_subset).trans
    (bd.bodies_antiClustering B hB)

/-- **The anti-clustering threshold, cleared of the positive exponent.**

The second step of (S2): multiplying `Kakeya.VeryNotSticky.SlabScale.antiClustering` by the
positive finite real `δ^{-exscal-2ϱ}` turns
`C_{hyp:ml2slabinputs}(C₀) C_bias δ^{exscal} ≤ δ^{2ϱ}` into
`C_{hyp:ml2slabinputs}(C₀) C_bias δ^{-2ϱ} ≤ δ^{-exscal}`. -/
theorem slabAntiClusteringThreshold (cfg : VeryNotSticky.{u}) {τ : ℝ} {bd : BallData cfg}
    (tc : ThinConfig cfg bd) (ss : SlabScale cfg bd tc τ) :
    (slabInputsConstant bd.C₀ : ENNReal) * (bd.Cbias : ENNReal) *
        (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) ≤
      (cfg.δ : ENNReal) ^ (-cfg.exscal) := by
  let d : ENNReal := (cfg.δ : ENNReal)
  let C : ENNReal := (slabInputsConstant bd.C₀ : ENNReal) * (bd.Cbias : ENNReal)
  have hd0 : d ≠ 0 := by dsimp [d]; exact ENNReal.coe_ne_zero.mpr (ne_of_gt cfg.hδ)
  have hdtop : d ≠ ⊤ := by dsimp [d]; exact ENNReal.coe_ne_top
  -- `δ^exscal · δ^(-exscal - 2ϱ) = δ^(-2ϱ)`, and `δ^(2ϱ) · δ^(-exscal - 2ϱ) = δ^(-exscal)`.
  have hpair : d ^ cfg.exscal * d ^ (-cfg.exscal - 2 * cfg.ϱ) = d ^ (-(2 * cfg.ϱ)) := by
    rw [← ENNReal.rpow_add cfg.exscal (-cfg.exscal - 2 * cfg.ϱ) hd0 hdtop]
    congr 1
    ring
  have hpair2 : d ^ (2 * cfg.ϱ) * d ^ (-cfg.exscal - 2 * cfg.ϱ) = d ^ (-cfg.exscal) := by
    rw [← ENNReal.rpow_add (2 * cfg.ϱ) (-cfg.exscal - 2 * cfg.ϱ) hd0 hdtop]
    congr 1
    ring
  have hmain : C * d ^ (-(2 * cfg.ϱ)) ≤ d ^ (-cfg.exscal) := by
    calc
      C * d ^ (-(2 * cfg.ϱ)) = (C * d ^ cfg.exscal) * d ^ (-cfg.exscal - 2 * cfg.ϱ) := by
        rw [← hpair]
        ac_rfl
      _ ≤ d ^ (2 * cfg.ϱ) * d ^ (-cfg.exscal - 2 * cfg.ϱ) := by
        simpa [d, C] using
          (mul_le_mul_left ss.antiClustering (d ^ (-cfg.exscal - 2 * cfg.ϱ)))
      _ = d ^ (-cfg.exscal) := hpair2
  simpa [d, C] using hmain

/-- **(S2) of the slab inputs** (blueprint `hyp:ml2slabinputs`(S2)).

Multiply `Kakeya.VeryNotSticky.slabRetainedAntiClustering` by `C_{hyp:ml2slabinputs}(C₀)` and
chain with `Kakeya.VeryNotSticky.slabAntiClusteringThreshold`. -/
theorem slabBodiesAntiClustering (cfg : VeryNotSticky.{u}) {τ : ℝ} {bd : BallData cfg}
    (tc : ThinConfig cfg bd) (ss : SlabScale cfg bd tc τ) (B : bd.bι) (hB : B ∈ bd.bs) :
    (slabInputsConstant bd.C₀ : ENNReal) *
        maxDensity (tc.thinBall hB).bodies' bd.Wb ≤
      (cfg.δ : ENNReal) ^ (-cfg.exscal) := by
  calc
    (slabInputsConstant bd.C₀ : ENNReal) *
        maxDensity (tc.thinBall hB).bodies' bd.Wb
        ≤ (slabInputsConstant bd.C₀ : ENNReal) *
            ((bd.Cbias : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ))) :=
      mul_le_mul' le_rfl (slabRetainedAntiClustering cfg tc hB)
    _ ≤ (cfg.δ : ENNReal) ^ (-cfg.exscal) := by
      simpa [mul_assoc] using slabAntiClusteringThreshold cfg tc ss

/-- **The inputs of the slab case hold** (blueprint `lem:ml2slabinputs`).

Item by item. `deltaLtOne`, (S1), (S6) and (S7) are four of the five fields of
`Kakeya.VeryNotSticky.SlabScale` verbatim; (S3) is
`Kakeya.VeryNotSticky.BallData.segs_dilation` of (C3), (S4) is
`Kakeya.VeryNotSticky.tube_count` of (C1) and (S5) is
`Kakeya.VeryNotSticky.ThinConfig.segment_mass` of (T7), each verbatim. Only (S2) needs an
argument, and it is `Kakeya.VeryNotSticky.slabBodiesAntiClustering`.

The two case hypotheses `a ≤ δ^{1-τ}` and `b ≥ δ^{2 exscal}` are *not* needed here, although
`Kakeya.VeryNotSticky.SlabInputs` is used only under them: no item of the bundle is a statement
about which side of either dichotomy one is on. -/
theorem slabInputs (cfg : VeryNotSticky.{u}) {τ : ℝ} {bd : BallData cfg}
    (tc : ThinConfig cfg bd) (ss : SlabScale cfg bd tc τ) :
    SlabInputs cfg bd tc τ where
  deltaLtOne := ss.deltaLtOne
  densityThreshold := ss.density
  bodiesAntiClustering := slabBodiesAntiClustering cfg tc ss
  segsDilation := bd.segs_dilation
  tubeCount := cfg.tube_count
  segmentMass := tc.segment_mass
  finalThreshold := ss.final
  fibreMassThreshold := ss.fibreMass

/-! ### The prism family of the slab case

GWZ Lemma 6.9 is applied once in this file, and applying it takes four steps beyond naming the
family it is applied to — the enlarged carriers
`fun j ↦ ((tc.thinBall hB).W j).toConvexSpaceBody` of blueprint `def:ml2slabCarriers`, which is
available as a term and needs no declaration of its own. The four are: enclosing that family in
exact prisms, choosing the parameter `ε` together with the two half-width hypotheses that go
with it, and checking the density and the anti-clustering. Each is separated out below, so that
`Kakeya.VeryNotSticky.slabMultBound` is the assembly it ought to be.

The separation is forced by the enlargement sandwich `Kakeya.ThinCase.ThinBall.Wb_le_W` /
`Kakeya.ThinCase.ThinBall.W_le_cthickening`: the family GWZ Lemma 6.9 is applied to is *not* the
family (C4) controls, and keeping the passage between them inside a single proof made that proof
carry the enlargement, the enclosure, the choice of `ε` and two constant-chasing chains at
once. -/

/-- **Enclosing the shaded carriers in exact prisms** (blueprint `lem:ml2slabCarrierEnclosure`).

`Kakeya.VeryNotSticky.slabPrismEnclosure`, applied to the family of enlarged carriers
`fun j ↦ ((tc.thinBall hB).W j).toConvexSpaceBody` — which is what the shading
`(tc.thinBall hB).W` actually shades — at comparison constant `2 bd.C₀`. Its thickness
hypothesis is `Kakeya.ThinCase.ThinBall.hasThicknesses_W` applied to
`Kakeya.VeryNotSticky.BallData.bodies_thickness` of (C4), which is where the doubling of the
comparison constant comes from; its shading hypothesis holds by `rfl`, the family being the
carriers of the shaded bodies themselves; and `0 < a`, `0 < r₁` are `cfg.hdims` with `cfg.hδ`
and `r₁ = δ^{exscal} > 0`.

The half-widths are exactly `a' × b' × 1`, with `a' = a / r₁` and `b' = b / r₁`, and not `2 C₀`
times anything: `Kakeya.VeryNotSticky.slabPrismEnclosureBody` normalizes by the reciprocal of
whichever comparison constant it is handed, so the doubling cancels. This is what keeps the
window of `Kakeya.VeryNotSticky.slabEpsRange` — and with it
`Kakeya.VeryNotSticky.slabMultBoundConstant` — a function of `exscal` alone. The doubling is
charged only in the comparison constant, and is one of the two factors of
`Kakeya.VeryNotSticky.slabInputsConstant`.

The third conclusion is stated against the maximal density of the *carriers* and not of the
geometric bodies `bd.Wb`, because that is what the enclosure produces; the passage to the
geometric bodies is the second factor of `Kakeya.VeryNotSticky.slabInputsConstant` and is
carried out in `Kakeya.VeryNotSticky.slabPrismAntiClustering`, where it is composed with (S2) in
one chain. -/
theorem slabCarrierEnclosure (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs) {a' b' : NNReal}
    (ha' : a' = cfg.a / cfg.r₁) (hb' : b' = cfg.b / cfg.r₁)
    (hab' : a' ≤ b') (hb1' : b' ≤ 1) :
    ∃ P : bd.ω → ShadedPrism3D a' b' 1 hab' hb1' le_rfl,
      multiplicity (tc.thinBall hB).bodies' (fun j ↦ (P j).toShadedBody) =
          multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W ∧
      fullness (tc.thinBall hB).bodies' (tc.thinBall hB).W ≤
          slabPrismEnclosureConstant (2 * bd.C₀) *
            fullness (tc.thinBall hB).bodies' (fun j ↦ (P j).toShadedBody) ∧
      maxDensity (tc.thinBall hB).bodies' (fun j ↦ (P j).toConvexSpaceBody) ≤
          (slabPrismEnclosureConstant (2 * bd.C₀) : ENNReal) *
            maxDensity (tc.thinBall hB).bodies'
              (fun j ↦ ((tc.thinBall hB).W j).toConvexSpaceBody) := by
  let tb := tc.thinBall hB
  let t : Finset bd.ω := tb.bodies'
  let Wsh : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)) := tb.W
  let Wb' : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := fun j ↦ (Wsh j).toConvexSpaceBody
  let vt : Fin 3 → ℝ := ![ (cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ) ]
  have hC₀' : 1 ≤ 2 * bd.C₀ := by
    calc
      1 ≤ bd.C₀ := bd.hC₀
      _ ≤ 2 * bd.C₀ := by
        rw [two_mul]
        exact le_add_self
  have ha : 0 < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
  have hr₁ : 0 < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  have hnonneg : ∀ k : Fin 3, (0 : ℝ) ≤ vt k := by
    intro k
    fin_cases k <;> simp [vt, NNReal.zero_le_coe]
  have hWb : ∀ j ∈ t, HasThicknesses (bd.Wb j).carrier bd.C₀ vt := by
    intro j hj
    exact bd.bodies_thickness B hB j (tb.bodies'_subset hj)
  have hthick : ∀ j ∈ t, HasThicknesses (Wb' j).carrier (2 * bd.C₀) vt := by
    intro j hj
    exact ThinCase.ThinBall.hasThicknesses_W (C₁ := bd.C₀) (t := vt) tb hnonneg hWb j hj
  obtain ⟨P, h1, h2, h3⟩ :=
    slabPrismEnclosure (ω := bd.ω) t Wb' Wsh
      hC₀' ha hr₁ ha' hb' hab' hb1' (fun j hj => rfl) hthick
  exact ⟨P, h1, h2, h3⟩

/-- **The prism family is dense enough for GWZ Lemma 6.9** (blueprint
`lem:ml2slabPrismDensity`).

Write `C = tc.C` and chain
`C · C_{hyp:ml2slabinputs}(C₀) · δ^{exscal} ≤ δ^{6η} ≤ C · λ(𝕎'_B, Y_{𝕎'_B})
≤ C · C_{lem:ml2slabPrismEnclosure}(2 C₀) · λ(P) ≤ C · C_{hyp:ml2slabinputs}(C₀) · λ(P)`,
the first step being (S1), the second `Kakeya.ThinCase.ThinBall.fullness_bodies` of (T2), the
third the hypothesis, and the fourth
`slabPrismEnclosureConstant (2 C₀) ≤ slabInputsConstant C₀`, which holds because
`volume_comparison.C 3 = 384 ≥ 1`. Cancelling the common factor
`C · C_{hyp:ml2slabinputs}(C₀)` is legitimate in `ℝ≥0∞` because it is positive and finite, both
constants being reals at least `1`.

The lemma is stated for an arbitrary shaded family `P` carried by the index set of `𝕎'_B`,
rather than for the prism family of `Kakeya.VeryNotSticky.slabCarrierEnclosure`: nothing but the
displayed fullness comparison is used, and stating it this way keeps the dependent
`ShadedPrism3D` type out of the signature. -/
theorem slabPrismDensity (cfg : VeryNotSticky.{u}) {τ : ℝ} {bd : BallData cfg}
    (tc : ThinConfig cfg bd) (si : SlabInputs cfg bd tc τ) {B : bd.bι} (hB : B ∈ bd.bs)
    {P : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (hlam : fullness (tc.thinBall hB).bodies' (tc.thinBall hB).W ≤
      slabPrismEnclosureConstant (2 * bd.C₀) * fullness (tc.thinBall hB).bodies' P) :
    (cfg.δ : ENNReal) ^ cfg.exscal ≤ (fullness (tc.thinBall hB).bodies' P : ENNReal) := by
  let t := (tc.thinBall hB).bodies'
  let Cc : ENNReal := (slabInputsConstant bd.C₀ : ENNReal)
  -- `slabInputsConstant bd.C₀ = max 1 (slabPrismEnclosureConstant (2 * bd.C₀) ·
  -- volume_comparison.C 3)` and `volume_comparison.C 3 = 384 ≥ 1`, so
  -- `slabPrismEnclosureConstant (2 * bd.C₀) ≤ slabInputsConstant bd.C₀`, which is what
  -- enlarges the hypothesis from `C_{lem:ml2slabPrismEnclosure}(2C₀)` to the (S1) constant.
  have hC384 : (1 : NNReal) ≤ Metric.volume_comparison.C 3 := by
    dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
    norm_num
  have hleC : slabPrismEnclosureConstant (2 * bd.C₀) ≤ slabInputsConstant bd.C₀ := by
    rw [slabInputsConstant]
    calc
      slabPrismEnclosureConstant (2 * bd.C₀)
          ≤ slabPrismEnclosureConstant (2 * bd.C₀) * Metric.volume_comparison.C 3 := by
            simpa using (mul_le_mul' (le_refl _) hC384)
      _ ≤ max 1 (slabPrismEnclosureConstant (2 * bd.C₀) * Metric.volume_comparison.C 3) :=
            le_max_right _ _
  have hlamE : (fullness t ((tc.thinBall hB).W) : ENNReal) ≤
      (slabPrismEnclosureConstant (2 * bd.C₀) : ENNReal) * (fullness t P : ENNReal) := by
    simpa [ENNReal.coe_mul] using (ENNReal.coe_le_coe.mpr hlam)
  have hlam' : (fullness t ((tc.thinBall hB).W) : ENNReal) ≤
      Cc * (fullness t P : ENNReal) := by
    calc
      (fullness t ((tc.thinBall hB).W) : ENNReal)
          ≤ (slabPrismEnclosureConstant (2 * bd.C₀) : ENNReal) *
              (fullness t P : ENNReal) := hlamE
      _ ≤ Cc * (fullness t P : ENNReal) :=
            mul_le_mul' (ENNReal.coe_le_coe.mpr hleC) (le_refl _)
  have hWle : (tc.C : ENNReal) * (fullness t ((tc.thinBall hB).W) : ENNReal) ≤
      (tc.C : ENNReal) * (Cc * (fullness t P : ENNReal)) :=
    mul_le_mul' (le_refl _) hlam'
  have hchain : (tc.C : ENNReal) * Cc * (cfg.δ : ENNReal) ^ cfg.exscal ≤
      (tc.C : ENNReal) * Cc * (fullness t P : ENNReal) := by
    calc
      (tc.C : ENNReal) * Cc * (cfg.δ : ENNReal) ^ cfg.exscal
          ≤ (cfg.δ : ENNReal) ^ (6 * cfg.η) := si.densityThreshold
      _ = (cfg.δ : ENNReal) ^ (3 * (2 * cfg.η)) := by congr 1; ring
      _ ≤ (tc.C : ENNReal) * (fullness t ((tc.thinBall hB).W) : ENNReal) :=
          (tc.thinBall hB).fullness_bodies
      _ ≤ (tc.C : ENNReal) * (Cc * (fullness t P : ENNReal)) := hWle
      _ = (tc.C : ENNReal) * Cc * (fullness t P : ENNReal) := by
          rw [mul_assoc]
  have hCne : (tc.C : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1)
      (tc.thinBall hB).one_le_C))
  have hCenc_ne : Cc ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le
    (by norm_num : (0 : NNReal) < 1) (one_le_slabInputsConstant bd.C₀)))
  have hCfac_ne : (tc.C : ENNReal) * Cc ≠ 0 := mul_ne_zero hCne hCenc_ne
  have hCtop : (tc.C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCenc_top : Cc ≠ ⊤ := ENNReal.coe_ne_top
  have hCfac_top : (tc.C : ENNReal) * Cc ≠ ⊤ := ENNReal.mul_ne_top hCtop hCenc_top
  have hdelta_le : (cfg.δ : ENNReal) ^ cfg.exscal ≤ (fullness t P : ENNReal) :=
    (ENNReal.mul_le_mul_iff_left hCfac_ne hCfac_top).mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hchain)
  simpa [t] using hdelta_le

/-- **The prism family is anti-clustered enough for GWZ Lemma 6.9** (blueprint
`lem:ml2slabPrismAntiClustering`).

Chain
`Δ_max(P) ≤ C_{lem:ml2slabPrismEnclosure}(2 C₀) Δ_max(𝕎⁺_B)
≤ C_{lem:ml2slabPrismEnclosure}(2 C₀) · volume_comparison.C 3 · Δ_max(𝕎'_B)
≤ C_{hyp:ml2slabinputs}(C₀) Δ_max(𝕎'_B) ≤ δ^{-exscal}`.

The first step is the hypothesis. The second is where the two families are exchanged:
`Kakeya.ThinCase.ThinBall.isVolumeControlledEnlargement` makes the carriers a
`volume_comparison.C 3`-volume-controlled enlargement of the geometric bodies `bd.Wb`, and
`ConvexSpaceBody.IsVolumeControlledEnlargement.maxDensity_le` turns that into
`Δ_max(𝕎⁺_B) ≤ volume_comparison.C 3 · Δ_max(𝕎'_B)`. The third is
`Kakeya.VeryNotSticky.slabInputsConstant`, with equality, the truncation at `1` there being
inactive, and the fourth is (S2). No division occurs anywhere in the chain.

As in `Kakeya.VeryNotSticky.slabPrismDensity` the family is arbitrary: only the displayed
density comparison is used. -/
theorem slabPrismAntiClustering (cfg : VeryNotSticky.{u}) {τ : ℝ} {bd : BallData cfg}
    (tc : ThinConfig cfg bd) (si : SlabInputs cfg bd tc τ) {B : bd.bι} (hB : B ∈ bd.bs)
    {P : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hΔ : maxDensity (tc.thinBall hB).bodies' P ≤
      (slabPrismEnclosureConstant (2 * bd.C₀) : ENNReal) *
        maxDensity (tc.thinBall hB).bodies'
          (fun j ↦ ((tc.thinBall hB).W j).toConvexSpaceBody)) :
    maxDensity (tc.thinBall hB).bodies' P ≤ (cfg.δ : ENNReal) ^ (-cfg.exscal) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 :=
    finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)
  have hconst : (slabPrismEnclosureConstant (2 * bd.C₀) : ENNReal) *
      (volume_comparison.C 3 : ENNReal) ≤ (slabInputsConstant bd.C₀ : ENNReal) := by
    rw [← ENNReal.coe_mul]
    rw [slabInputsConstant]
    exact ENNReal.coe_le_coe.mpr
      (le_max_right 1 (slabPrismEnclosureConstant (2 * bd.C₀) * volume_comparison.C 3))
  calc
    maxDensity (tc.thinBall hB).bodies' P ≤
        (slabPrismEnclosureConstant (2 * bd.C₀) : ENNReal) *
          maxDensity (tc.thinBall hB).bodies'
            (fun j ↦ ((tc.thinBall hB).W j).toConvexSpaceBody) := hΔ
    _ ≤ (slabPrismEnclosureConstant (2 * bd.C₀) : ENNReal) *
          ((volume_comparison.C 3 : ENNReal) * maxDensity (tc.thinBall hB).bodies' bd.Wb) := by
        gcongr
        have hvc : ConvexSpaceBody.IsVolumeControlledEnlargement (tc.thinBall hB).bodies' bd.Wb
            (fun j ↦ ((tc.thinBall hB).W j).toConvexSpaceBody)
            (volume_comparison.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ENNReal) :=
          ThinCase.ThinBall.isVolumeControlledEnlargement (tc.thinBall hB)
        simpa [hdim] using ConvexSpaceBody.IsVolumeControlledEnlargement.maxDensity_le hvc
    _ ≤ (slabInputsConstant bd.C₀ : ENNReal) * maxDensity (tc.thinBall hB).bodies' bd.Wb := by
        rw [← mul_assoc]
        exact mul_le_mul' hconst le_rfl
    _ ≤ (cfg.δ : ENNReal) ^ (-cfg.exscal) := si.bodiesAntiClustering B hB

/-- **Choosing the parameter `ε` of GWZ Lemma 6.9** (blueprint `lem:ml2slabEpsChoice`).

`Kakeya.VeryNotSticky.slabScaleBounds` gives `δ^{1-exscal} ≤ a' ≤ δ^{1-τ-exscal}` and
`b' ≥ δ^{exscal}`, with `a' = a / r₁` and `b' = b / r₁`.
`Kakeya.VeryNotSticky.slabEpsRange`, applied with that window and with `0 < δ < 1`, gives
`0 < a' < 1` together with an `ε` satisfying `(a')^ε = δ^{exscal}` and
`ε ≥ exscal / (1 - exscal)`, the latter being positive since `0 < exscal < 1/2`. The two
remaining inequalities are rewritings of the defining equation: `b' ≥ δ^{exscal} = (a')^ε` is
the slab case, in the form `slabScaleBounds` just gave it, and `1 ≥ δ^{exscal} = (a')^ε` holds
because `δ ≤ 1` and `exscal > 0`.

The four conclusions about `ε` are exactly what `Kakeya.VeryNotSticky.slabMultBound` has to hand
to GWZ Lemma 6.9 about the parameter: the defining equation, which is what
`Kakeya.VeryNotSticky.slabRpowIdentity` then converts; the lower bound, which is what
`Kakeya.VeryNotSticky.slab1Constant_antitone` then consumes; and the two half-width hypotheses.
The other two hypotheses of GWZ Lemma 6.9, the density and the anti-clustering, are about the
family rather than about `ε`, which is why they are separated from this one.

`δ < 1` is passed as its own hypothesis rather than through
`Kakeya.VeryNotSticky.SlabInputs`: it is the only item of the bundle this lemma would use, and
taking it directly keeps the lemma independent of the ball and of the bundle. -/
theorem slabEpsChoice (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hδ1 : cfg.δ < 1)
    (hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    (hslab : cfg.δ ^ (2 * cfg.exscal) ≤ cfg.b) :
    0 < cfg.a / cfg.r₁ ∧ cfg.a / cfg.r₁ < 1 ∧
      ∃ ε : ℝ,
        ((cfg.a / cfg.r₁ : NNReal) : ENNReal) ^ ε = (cfg.δ : ENNReal) ^ cfg.exscal ∧
        cfg.exscal / (1 - cfg.exscal) ≤ ε ∧ 0 < ε ∧
        ((cfg.a / cfg.r₁ : NNReal) : ENNReal) ^ ε ≤ ((cfg.b / cfg.r₁ : NNReal) : ENNReal) ∧
        ((cfg.a / cfg.r₁ : NNReal) : ENNReal) ^ ε ≤ 1 := by
  let a' : NNReal := cfg.a / cfg.r₁
  let b' : NNReal := cfg.b / cfg.r₁
  have sc := slabScaleBounds cfg hthin hslab
  obtain ⟨ha'_pos, ha'_lt, ε, heps, heps_low, _⟩ :=
    slabEpsRange (hδ := cfg.hδ) (hδ1 := hδ1) (hexscal := cfg.hexscal)
      (hthinScale := params.thinScale) sc.1 sc.2.1
  have hη : 0 < ε :=
    lt_of_lt_of_le (div_pos cfg.hexscal (by linarith [params.scale])) heps_low
  have hb : ((cfg.a / cfg.r₁ : NNReal) : ENNReal) ^ ε ≤ ((cfg.b / cfg.r₁ : NNReal) : ENNReal) := by
    rw [heps]
    calc
      (cfg.δ : ENNReal) ^ cfg.exscal
          = ((cfg.δ ^ cfg.exscal : NNReal) : ENNReal) := by
              rw [ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne']
      _ ≤ ((cfg.b / cfg.r₁ : NNReal) : ENNReal) := ENNReal.coe_le_coe.2 sc.2.2
  have hc : ((cfg.a / cfg.r₁ : NNReal) : ENNReal) ^ ε ≤ 1 := by
    simpa using ENNReal.rpow_le_one (by exact_mod_cast (le_of_lt ha'_lt)) (le_of_lt hη)
  exact ⟨ha'_pos, ha'_lt, ε, heps, heps_low, hη, hb, hc⟩

/-! ### The multiplicity of the factoring bodies -/

/-- **Multiplicity of the factoring bodies in the slab case** (blueprint
`lem:ml2slabMultBound`).

Assume Configurations `hyp:ml2setup` and `hyp:ml2thinsetup`, the thin-case refinement
`a ≤ δ^{1-τ}`, the slab hypothesis `b ≥ δ^{2 exscal}` and the inputs (S1), (S2). Then
`μ(𝕎'_B, Y_{𝕎'_B}) ≤ C_{lem:ml2slabMultBound}(exscal) δ^{-8 exscal}` for every `B ∈ 𝔅`.

Put `a' = a / r₁` and `b' = b / r₁`; the order relations `a' ≤ b' ≤ 1` hold by `a ≤ b ≤ r₁` of
(C4). Let `(P, Y_P)` be the exact `a' × b' × 1` prism family supplied by
`Kakeya.VeryNotSticky.slabCarrierEnclosure`; it is non-empty by
`Kakeya.VeryNotSticky.slabBodiesNonempty`, its index set being that of `𝕎'_B`. Fix `ε` as in
`Kakeya.VeryNotSticky.slabEpsChoice`, whose hypothesis `δ < 1` is
`Kakeya.VeryNotSticky.SlabInputs.deltaLtOne`; it supplies at once `0 < a' < 1`, the defining
equation `(a')^ε = δ^{exscal}`, the bound `ε ≥ exscal/(1-exscal) > 0`, and the two half-width
hypotheses `b' ≥ (a')^ε` and `1 ≥ (a')^ε` of GWZ Lemma 6.9.

The two remaining hypotheses of GWZ Lemma 6.9 for `(P, Y_P)` with parameter `ε` are the density
`λ(P, Y_P) ≥ δ^{exscal} = (a')^ε`, which is `Kakeya.VeryNotSticky.slabPrismDensity`, and the
anti-clustering `Δ_max(P) ≤ δ^{-exscal} = (a')^{-ε}`, which is
`Kakeya.VeryNotSticky.slabPrismAntiClustering`, each applied to the comparison that
`slabCarrierEnclosure` supplies.

The conclusion of GWZ Lemma 6.9 is therefore
`μ(P, Y_P) ≤ C_{6.9}(ε) (a')^{-8ε} = C_{6.9}(ε) δ^{-8 exscal}`, which is at most
`C_{lem:ml2slabMultBound}(exscal) δ^{-8 exscal}`,
the equality being `Kakeya.VeryNotSticky.slabRpowIdentity` and the last step
`Kakeya.VeryNotSticky.slab1Constant_antitone` at `η₀ = exscal/(1-exscal)`; and
`μ(P, Y_P) = μ(𝕎'_B, Y_{𝕎'_B})` by `slabCarrierEnclosure`.

The choice `ε = η` would *not* do, because `η ≪ exscal` makes `(a')^η ≈ δ^η` larger than
`δ^{exscal}`, and the hypothesis `b' ≥ (a')^ε` then fails for bodies whose middle thickness is
as small as `b = δ^{2 exscal}`. This is why the parameter is written `ε` throughout: it is a
parameter of GWZ Lemma 6.9, at the scale of `exscal`, and not the density exponent `cfg.η`. -/
theorem slabMultBound (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    (hslab : cfg.δ ^ (2 * cfg.exscal) ≤ cfg.b)
    {bd : BallData cfg} (tc : ThinConfig cfg bd) (si : SlabInputs cfg bd tc τ)
    {B : bd.bι} (hB : B ∈ bd.bs) :
    multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W ≤
      (slabMultBoundConstant cfg.exscal : ENNReal) * (cfg.δ : ENNReal) ^ (-8 * cfg.exscal) := by
  let tb := tc.thinBall hB
  let t := tb.bodies'
  let a' : NNReal := cfg.a / cfg.r₁
  let b' : NNReal := cfg.b / cfg.r₁
  have hr₁ : 0 < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  have hbr₁ : cfg.b ≤ cfg.r₁ := by
    dsimp [r₁]
    exact cfg.hdims.2.2
  have hab' : a' ≤ b' := by
    dsimp [a', b']
    exact (div_le_div_iff_of_pos_right hr₁).mpr cfg.hdims.2.1
  have hb1' : b' ≤ 1 := by
    dsimp [b']
    exact (div_le_one hr₁).mpr hbr₁
  obtain ⟨P, hmu0, hlam0, hDel0⟩ := slabCarrierEnclosure cfg tc hB rfl rfl hab' hb1'
  have hs : t.Nonempty := slabBodiesNonempty cfg tc hB
  obtain ⟨ha'_pos, ha'_lt, epsilon, heps, heps_low, hη, hb, hc⟩ :=
    slabEpsChoice cfg params si.deltaLtOne hthin hslab
  have hlam : (a' : ENNReal) ^ epsilon ≤ (fullness t (fun j ↦ (P j).toShadedBody) : ENNReal) := by
    rw [heps]
    exact slabPrismDensity cfg tc si hB hlam0
  have hnegexp : (a' : ENNReal) ^ (-epsilon) = (cfg.δ : ENNReal) ^ (-cfg.exscal) := by
    rw [ENNReal.rpow_neg, heps, ← ENNReal.rpow_neg]
  have hDelta : maxDensity t (fun j ↦ (P j).toConvexSpaceBody) ≤ (a' : ENNReal) ^ (-epsilon) := by
    rw [hnegexp]
    exact slabPrismAntiClustering cfg tc si hB hDel0
  have hmult := ShadedPrism3D.multiplicity_le_rpow (s := t) (V := P) (η := epsilon)
    hη ha'_pos ha'_lt hs hlam hb hc hDelta
  have hC0le : ShadedPrism3D.multiplicity_le_rpow.C epsilon ≤
      ShadedPrism3D.multiplicity_le_rpow.C (cfg.exscal / (1 - cfg.exscal)) :=
    slab1Constant_antitone (div_pos cfg.hexscal (by linarith [params.scale])) heps_low
  calc
    multiplicity t tb.W = multiplicity t (fun j ↦ (P j).toShadedBody) := hmu0.symm
    _ ≤ (ShadedPrism3D.multiplicity_le_rpow.C epsilon : ENNReal) *
          (a' : ENNReal) ^ (-8 * epsilon) := hmult
    _ = (ShadedPrism3D.multiplicity_le_rpow.C epsilon : ENNReal) *
          (cfg.δ : ENNReal) ^ (-8 * cfg.exscal) := by rw [slabRpowIdentity heps]
    _ ≤ (slabMultBoundConstant cfg.exscal : ENNReal) * (cfg.δ : ENNReal) ^ (-8 * cfg.exscal) := by
      dsimp [slabMultBoundConstant]
      exact mul_le_mul' (ENNReal.coe_le_coe.2 hC0le) le_rfl

/-! ### From the multiplicity bound to the union bound -/

/-- **Mass of the factoring bodies against their shaded union** (blueprint
`lem:ml2slabBodyMassBound`).

By `ShadedBody.sum_volumeReal_shade_eq_fullness_mul` and `ShadedBody.multiplicity_mul_union`,
applied to the shaded family of `𝕎'_B` — whose carriers are, by the enlargement sandwich
`Kakeya.ThinCase.ThinBall.Wb_le_W` / `Kakeya.ThinCase.ThinBall.W_le_cthickening`, the enlarged
bodies and not the `bd.Wb j` themselves —
`λ(𝕎'_B, Y_{𝕎'_B}) ∑_j |carrier(W_j)| = ∑_j |Y_{𝕎'_B}(W_j)| =
μ(𝕎'_B, Y_{𝕎'_B}) |U(𝕎'_B, Y_{𝕎'_B})|`.
It is the sum of the *carrier* volumes that appears on the left, because the denominator of `λ`
is the total volume of the family that is being shaded. Multiplying the density bound (T2),
`δ^{6η} ≤ C λ(𝕎'_B, Y_{𝕎'_B})` (at the `tb` index `2η`), by that same sum and using
`μ(𝕎'_B, Y_{𝕎'_B}) ≤ M` gives the displayed bound for `δ^{6η} ∑_j |carrier(W_j)|`.

The geometric bodies re-enter only at the last step, through
`Kakeya.ThinCase.ThinBall.sum_volume_Wb_le`, which bounds
`∑_{W ∈ 𝕎'_B} |W| ≤ ∑_j |carrier(W_j)|` and so yields the conclusion. The comparison is used in
the only direction available, and it is the useful one, the conclusion being an *upper* bound
for `∑_{W ∈ 𝕎'_B} |W|`.

This is the only place in the slab case where the two ratios `μ` and `λ` appear cleared of their
divisions, and it carries no side condition: both `ShadedBody.multiplicity_mul_union` and
`ShadedBody.sum_volumeReal_shade_eq_fullness_mul` are division-free identities in `ℝ≥0∞`.

The statement is about `∑_{W ∈ 𝕎'_B} |W|` and not about `|𝕎'_B| |W|`: the two are comparable by
(C4), but only up to a power of `C₀`, and writing the sum avoids both that loss and the choice of
a reference body, exactly as `Kakeya.VeryNotSticky.goalUnion` writes `∑_T |T|` rather than
`|𝕋| |T|`. It is about the *geometric* bodies and not the carriers because that is the sum the
rest of the chain wants: `Kakeya.VeryNotSticky.slabSegmentSumSplit` bounds the retained segment
mass by `Δ_max(𝕋_B) ∑_{W ∈ 𝕎'_B} |W|`, and the containment of a segment in its block, which is
what that lemma rests on, is a statement about the geometric body of (C4) and not about any
enlargement of it. The comparison happens to run in the direction that makes this free.

The blueprint states this with the extra hypothesis `M ≥ 1`; it is not used, so it is
dropped. -/
theorem slabBodyMassBound (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs) {M : ENNReal}
    (hmult : multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W ≤ M) :
    (cfg.δ : ENNReal) ^ (6 * cfg.η) *
        ∑ j ∈ (tc.thinBall hB).bodies', volume (bd.Wb j).carrier ≤
      (tc.C : ENNReal) * M * volume (tc.thinBall hB).UW := by
  let tb := tc.thinBall hB
  let t := tb.bodies'
  let W := tb.W
  -- the sum over the geometric bodies `bd.Wb` is at most the sum over the enlarged carriers
  have hcarrier : ∑ j ∈ t, volume (bd.Wb j).carrier ≤
      ∑ j ∈ t, volume (W j).carrier := tb.sum_volume_Wb_le
  calc
    (cfg.δ : ENNReal) ^ (6 * cfg.η) * ∑ j ∈ t, volume (bd.Wb j).carrier
        ≤ (tc.C : ENNReal) * (fullness t W : ENNReal) *
            ∑ j ∈ t, volume (bd.Wb j).carrier := by
      gcongr
      have hfb := tb.fullness_bodies
      rwa [show (3 : ℝ) * (2 * cfg.η) = 6 * cfg.η by ring] at hfb
    _ ≤ (tc.C : ENNReal) * (fullness t W : ENNReal) *
            ∑ j ∈ t, volume (W j).carrier := mul_le_mul' le_rfl hcarrier
    _ = (tc.C : ENNReal) * (∑ j ∈ t, volume (W j).shade) := by
      rw [mul_assoc]
      rw [← ShadedBody.sum_volumeReal_shade_eq_fullness_mul t W]
    _ = (tc.C : ENNReal) * (multiplicity t W * volume (⋃ j ∈ t, (W j).shade)) := by
      rw [ShadedBody.multiplicity_mul_union t W]
    _ = (tc.C : ENNReal) * (multiplicity t W * volume tb.UW) := rfl
    _ ≤ (tc.C : ENNReal) * (M * volume tb.UW) :=
      mul_le_mul' (le_refl (tc.C : ENNReal))
        (mul_le_mul' hmult (le_refl (volume tb.UW)))
    _ = (tc.C : ENNReal) * M * volume tb.UW := by
      ring

/-- **From the multiplicity bound to the union bound** (blueprint
`lem:ml2slabUnionFromMult`).

Multiply the conclusion of `Kakeya.VeryNotSticky.slabBodyMassBound` by `δ^{3τ+2η}` and feed it
into `Kakeya.ThinCase.unionLower_thin` at the `tb` index `2η`, in the explicit form
`C_{lem:ml2thinUnionLower}(C,C₀)⁻¹ δ^{3τ+2η} |U(𝕎'_B, Y_{𝕎'_B})| ≤ |U(𝕋_B, Y'_B)|`. The density
constant of (T2) *is* the comparison constant `C` of Configuration `hyp:ml2thinsetup` — in
Lean both are the field `Kakeya.VeryNotSticky.ThinConfig.C` — so the two losses compose as
`C · C_{lem:ml2thinUnionLower}(C, C₀)`, which is
`Kakeya.VeryNotSticky.slabUnionFromMultConstant`.

`Kakeya.ThinCase.unionLower_thin` is what consumes the thin-case hypothesis `a ≤ δ^{1-τ}`,
which is why it appears among the hypotheses although nothing else in the proof uses it; it
further needs `0 < δ` and `δ ≤ a`, which are `cfg.hδ` and `cfg.hdims`, and that the ambient
dimension is three.

As in `Kakeya.VeryNotSticky.slabBodyMassBound` the blueprint's hypothesis `M ≥ 1` is not used
and is dropped. -/
theorem slabUnionFromMult (cfg : VeryNotSticky.{u}) {τ : ℝ}
    (hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs) {M : ENNReal}
    (hmult : multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W ≤ M) :
    (cfg.δ : ENNReal) ^ (3 * τ + 8 * cfg.η) *
        ∑ j ∈ (tc.thinBall hB).bodies', volume (bd.Wb j).carrier ≤
      (slabUnionFromMultConstant tc.C bd.C₀ : ENNReal) * M * volume (tc.thinBall hB).U := by
  let K : ENNReal := (ThinCase.unionLowerConstant tc.C bd.C₀ : ENNReal)
  have hd0 : (cfg.δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt cfg.hδ)
  have hdtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 :=
    finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)
  have hK1 : (1 : ENNReal) ≤ K := by
    change (1 : ENNReal) ≤ (ThinCase.unionLowerConstant tc.C bd.C₀ : ENNReal)
    exact ENNReal.coe_le_coe.mpr (ThinCase.one_le_unionLowerConstant tc.C bd.C₀)
  have hK0 : K ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) hK1)
  have hKtop : K ≠ ⊤ := by
    change (ThinCase.unionLowerConstant tc.C bd.C₀ : ENNReal) ≠ ⊤
    exact ENNReal.coe_ne_top
  have hstep :
      (cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η) * volume (tc.thinBall hB).UW ≤
        K * volume (tc.thinBall hB).U := by
    have hunion := ThinCase.unionLower_thin hdim (tc.thinBall hB) cfg.hδ cfg.hdims.1 hthin
    have hm := mul_le_mul_right hunion K
    rwa [show K * ((K⁻¹ * (cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η)) * volume (tc.thinBall hB).UW) =
        (cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η) * volume (tc.thinBall hB).UW by
          rw [← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel hK0 hKtop, one_mul]] at hm
  calc
    (cfg.δ : ENNReal) ^ (3 * τ + 8 * cfg.η) *
        ∑ j ∈ (tc.thinBall hB).bodies', volume (bd.Wb j).carrier
        = (cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η) *
            ((cfg.δ : ENNReal) ^ (6 * cfg.η) *
              ∑ j ∈ (tc.thinBall hB).bodies', volume (bd.Wb j).carrier) := by
          rw [show 3 * τ + 8 * cfg.η = (3 * τ + 2 * cfg.η) + 6 * cfg.η by ring]
          rw [ENNReal.rpow_add (3 * τ + 2 * cfg.η) (6 * cfg.η) hd0 hdtop]
          rw [← mul_assoc]
    _ ≤ (cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η) *
          ((tc.C : ENNReal) * M * volume (tc.thinBall hB).UW) :=
          mul_le_mul_right
            (slabBodyMassBound cfg tc hB hmult) ((cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η))
    _ = (tc.C : ENNReal) * M *
          ((cfg.δ : ENNReal) ^ (3 * τ + 2 * cfg.η) * volume (tc.thinBall hB).UW) := by
          ring
    _ ≤ (tc.C : ENNReal) * M * (K * volume (tc.thinBall hB).U) :=
          mul_le_mul_right hstep ((tc.C : ENNReal) * M)
    _ = (slabUnionFromMultConstant tc.C bd.C₀ : ENNReal) * M * volume (tc.thinBall hB).U := by
          rw [slabUnionFromMultConstant]
          simp only [ENNReal.coe_mul]
          ac_rfl

/-- **The shaded union is large inside one ball, slab case** (blueprint `lem:ml2slabUnion`).

`Kakeya.VeryNotSticky.slabMultBound` gives `μ(𝕎'_B, Y_{𝕎'_B}) ≤ M` with
`M = C_{lem:ml2slabMultBound}(exscal) δ^{-8 exscal}`, so
`Kakeya.VeryNotSticky.slabUnionFromMult` applies with this `M` and yields
`δ^{3τ+8η} ∑_W |W| ≤ C_{lem:ml2slabUnionFromMult}(C,C₀) C_{lem:ml2slabMultBound}(exscal)
δ^{-8 exscal} |U(𝕋_B, Y'_B)|`, which is the claim after multiplying both sides by
`δ^{8 exscal}` and reading off `Kakeya.VeryNotSticky.slabUnionConstant`.

The exponent is `8η` — the honest value produced by the two lemmas above at the `tb` index
`2η` (F8) — and not the `12η` of the budget `Kakeya.VeryNotSticky.CaseParams.slab`. The slack
is not decoration: one further power of `δ^η` is spent in `Kakeya.VeryNotSticky.slabDensity`,
where the anti-clustering bound of (C1) is only `Δ_max(𝕋) ≤ δ^{-η}` and not `Δ_max(𝕋) ≤ 1`;
`2η` is the density loss of the repaired segment-mass clause (T7),
`Kakeya.VeryNotSticky.SlabInputs.segmentMass`; and `η` (with `2 exscal`) pays for its fibre
count in `Kakeya.VeryNotSticky.SlabScale.fibreMass`. Nothing is left over: the `4η` of margin
`Kakeya.VeryNotSticky.slabVolumeGoal` had before F8 is exactly what the (C5) exponent `2η`
costs along this chain. -/
theorem slabUnion (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    (hslab : cfg.δ ^ (2 * cfg.exscal) ≤ cfg.b)
    {bd : BallData cfg} (tc : ThinConfig cfg bd) (si : SlabInputs cfg bd tc τ)
    {B : bd.bι} (hB : B ∈ bd.bs) :
    (cfg.δ : ENNReal) ^ (8 * cfg.η + 8 * cfg.exscal + 3 * τ) *
        ∑ j ∈ (tc.thinBall hB).bodies', volume (bd.Wb j).carrier ≤
      (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) * volume (tc.thinBall hB).U := by
  let d : ENNReal := (cfg.δ : ENNReal)
  let Cm : ENNReal := (slabMultBoundConstant cfg.exscal : ENNReal)
  let Cu : ENNReal := (slabUnionFromMultConstant tc.C bd.C₀ : ENNReal)
  let S : ENNReal := ∑ j ∈ (tc.thinBall hB).bodies', volume (bd.Wb j).carrier
  let U : ENNReal := volume (tc.thinBall hB).U
  let M : ENNReal := Cm * d ^ (-8 * cfg.exscal)
  have hd0 : d ≠ 0 := by
    dsimp [d]
    exact ne_of_gt (ENNReal.coe_pos.mpr cfg.hδ)
  have hdtop : d ≠ ⊤ := by
    dsimp [d]
    exact ENNReal.coe_ne_top
  have hmult : multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W ≤ M := by
    dsimp [M, Cm, d]
    exact slabMultBound cfg params hthin hslab tc si hB
  have hdvanish : d ^ (8 * cfg.exscal) * d ^ (-8 * cfg.exscal) = (1 : ENNReal) := by
    rw [← ENNReal.rpow_add (8 * cfg.exscal) (-8 * cfg.exscal) hd0 hdtop]
    rw [show 8 * cfg.exscal + (-8 * cfg.exscal) = 0 by ring]
    exact ENNReal.rpow_zero
  calc
    d ^ (8 * cfg.η + 8 * cfg.exscal + 3 * τ) * S
        = d ^ (8 * cfg.exscal) * (d ^ (3 * τ + 8 * cfg.η) * S) := by
          rw [show 8 * cfg.η + 8 * cfg.exscal + 3 * τ =
              8 * cfg.exscal + (3 * τ + 8 * cfg.η) by ring]
          rw [ENNReal.rpow_add (8 * cfg.exscal) (3 * τ + 8 * cfg.η) hd0 hdtop]
          rw [mul_assoc]
    _ ≤ d ^ (8 * cfg.exscal) * (Cu * M * U) := by
          have hle : d ^ (3 * τ + 8 * cfg.η) * S ≤ Cu * M * U := by
            simpa [S, U, d, Cu] using slabUnionFromMult cfg hthin tc hB hmult
          exact mul_le_mul' le_rfl hle
    _ = (Cu * Cm) * U := by
          dsimp [M]
          rw [show d ^ (8 * cfg.exscal) * (Cu * (Cm * d ^ (-8 * cfg.exscal)) * U) =
              (Cu * Cm) * U by
            calc
              d ^ (8 * cfg.exscal) * (Cu * (Cm * d ^ (-8 * cfg.exscal)) * U)
                  = (Cu * Cm) * (d ^ (8 * cfg.exscal) * d ^ (-8 * cfg.exscal)) * U := by ac_rfl
              _ = (Cu * Cm) * U := by
                  rw [hdvanish, mul_one]]
    _ = (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) * U := by
          rw [slabUnionConstant, ENNReal.coe_mul]

/-! ### Comparing the slab count with the tube count -/

/-- **Splitting the segment mass along the blocks** (blueprint `lem:ml2slabSegmentSumSplit`).

Split `𝕋_B^{𝕎'}` along the blocks of the factoring of (C4): the blocks are disjoint, and every
segment of `𝕋_{B,W}` is contained in `W` (the field `Kakeya.VeryNotSticky.BallData.segs_le`),
so `𝕋_{B,W} ⊆ 𝕋_B[W]` and
`∑_{T_B ∈ 𝕋_B^{𝕎'}} |T_B| = ∑_{W ∈ 𝕎'_B} ∑_{T_B ∈ 𝕋_{B,W}} |T_B| ≤ ∑_{W ∈ 𝕎'_B} Δ(𝕋_B, W) |W|
≤ Δ_max(𝕋_B) ∑_{W ∈ 𝕎'_B} |W|`. Nothing is lost in either step, and no comparison constant
appears. -/
theorem slabSegmentSumSplit (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs) :
    ∑ p ∈ retainedSegments tc hB, volume (bd.Y p).carrier ≤
      maxDensity (bd.segs B) (fun p ↦ (bd.Y p).toConvexSpaceBody) *
        ∑ j ∈ (tc.thinBall hB).bodies', volume (bd.Wb j).carrier := by
  let W : bd.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun p ↦ (bd.Y p).toConvexSpaceBody
  let s := retainedSegments tc hB
  let t := (tc.thinBall hB).bodies'
  have hmap : ∀ p ∈ s, bd.blk p ∈ t := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hinner : ∀ j ∈ t,
      ∑ p ∈ s with bd.blk p = j, volume (bd.Y p).carrier ≤
        maxDensity (bd.segs B) W * volume (bd.Wb j).carrier := by
    intro j hj
    have hsub : (s.filter fun p ↦ bd.blk p = j) ⊆
        (bd.segs B).filter (fun p ↦ W p ≤ bd.Wb j) := by
      intro p hp
      have hp' : p ∈ s ∧ bd.blk p = j := Finset.mem_filter.mp hp
      have hpS : p ∈ bd.segs B := (Finset.mem_filter.mp hp'.1).1
      exact Finset.mem_filter.mpr ⟨hpS, by
        rw [← hp'.2]
        exact bd.segs_le B hB p hpS⟩
    calc
      ∑ p ∈ s with bd.blk p = j, volume (bd.Y p).carrier
        ≤ ∑ p ∈ (bd.segs B).filter (fun p ↦ W p ≤ bd.Wb j),
              volume (bd.Y p).carrier := Finset.sum_le_sum_of_subset hsub
      _ ≤ maxDensity (bd.segs B) W * volume (bd.Wb j).carrier :=
        sum_volume_le_maxDensity_mul_volume (bd.segs B) W (bd.Wb j)
  have hfib : (∑ p ∈ s, volume (bd.Y p).carrier) =
      ∑ j ∈ t, ∑ p ∈ s with bd.blk p = j, volume (bd.Y p).carrier := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (f := fun p ↦ volume (bd.Y p).carrier) hmap
  calc
    ∑ p ∈ s, volume (bd.Y p).carrier
        = ∑ j ∈ t, ∑ p ∈ s with bd.blk p = j, volume (bd.Y p).carrier := hfib
    _ ≤ ∑ j ∈ t, maxDensity (bd.segs B) W * volume (bd.Wb j).carrier :=
      Finset.sum_le_sum hinner
    _ = maxDensity (bd.segs B) (fun p ↦ (bd.Y p).toConvexSpaceBody) *
        ∑ j ∈ (tc.thinBall hB).bodies', volume (bd.Wb j).carrier := by
      rw [Finset.mul_sum]

/-- **Comparing the slab count with the tube count** (blueprint `lem:ml2slabDensity`).

By `Kakeya.VeryNotSticky.slabSegmentSumSplit` it suffices to bound `Δ_max(𝕋_B)`, and the
dilation comparison (S3) together with `Δ_max(𝕋) ≤ δ^{-η}` of (C1) — the field
`Kakeya.VeryNotSticky.maxDensity_le` — gives `Δ_max(𝕋_B) ≤ Cdil · r₁^{-2} δ^{-η}`. This lemma
has no comparison constant of its own: the `Cdil` is the one (S3) carries, passed through.

The blueprint's `δ^η r₁² ∑_{T_B} |T_B| ≤ ∑_W |W|` is already division-free and is stated as
such, with `Cdil` on the right. -/
theorem slabDensity (cfg : VeryNotSticky.{u}) {τ : ℝ} {bd : BallData cfg}
    (tc : ThinConfig cfg bd) (si : SlabInputs cfg bd tc τ) {B : bd.bι} (hB : B ∈ bd.bs) :
    (cfg.δ : ENNReal) ^ cfg.η * (cfg.r₁ : ENNReal) ^ 2 *
        ∑ p ∈ retainedSegments tc hB, volume (bd.Y p).carrier ≤
      (bd.Cdil : ENNReal) * ∑ j ∈ (tc.thinBall hB).bodies', volume (bd.Wb j).carrier := by
  let d : ENNReal := (cfg.δ : ENNReal)
  let R : ENNReal := (cfg.r₁ : ENNReal) ^ 2
  let D : ENNReal := maxDensity (bd.segs B) (fun p ↦ (bd.Y p).toConvexSpaceBody)
  let S : ENNReal := ∑ p ∈ retainedSegments tc hB, volume (bd.Y p).carrier
  let T : ENNReal := ∑ j ∈ (tc.thinBall hB).bodies', volume (bd.Wb j).carrier
  let K : ENNReal := (bd.Cdil : ENNReal)
  have hd0 : d ≠ 0 := by
    dsimp [d]
    exact ENNReal.coe_ne_zero.mpr cfg.hδ.ne'
  have hdtop : d ≠ ⊤ := by
    dsimp [d]
    exact ENNReal.coe_ne_top
  have hRD : R * D ≤ K * d ^ (-cfg.η) := by
    calc
      R * D ≤ K * maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) := by
        dsimp [R, D, K]
        exact si.segsDilation B hB
      _ ≤ K * d ^ (-cfg.η) := by
        dsimp [d]
        exact mul_le_mul' le_rfl cfg.maxDensity_le
  have hη : d ^ cfg.η * d ^ (-cfg.η) = (1 : ENNReal) := by
    rw [← ENNReal.rpow_add cfg.η (-cfg.η) hd0 hdtop]
    rw [show cfg.η + (-cfg.η) = 0 by ring]
    exact ENNReal.rpow_zero
  calc
    (d ^ cfg.η * R) * S
        ≤ (d ^ cfg.η * R) * (D * T) :=
          mul_le_mul' le_rfl (slabSegmentSumSplit cfg tc hB)
    _ = (d ^ cfg.η * (R * D)) * T := by ac_rfl
    _ ≤ (d ^ cfg.η * (K * d ^ (-cfg.η))) * T :=
          mul_le_mul' (mul_le_mul' le_rfl hRD) le_rfl
    _ = K * ((d ^ cfg.η * d ^ (-cfg.η)) * T) := by ac_rfl
    _ = K * ((1 : ENNReal) * T) := by
          rw [hη]
    _ = K * T := by
          rw [one_mul]

/-! ### From one ball to the whole family -/

/-- **The per-ball estimate** (blueprint `lem:ml2slabPerBall`).

Multiply the conclusion of `Kakeya.VeryNotSticky.slabDensity` by `δ^{8η+8 exscal+3τ}` and
substitute it into `Kakeya.VeryNotSticky.slabUnion`. With `r₁² = δ^{2 exscal}` the left-hand
exponent is `(8η+8 exscal+3τ) + η + 2 exscal = 9η+10 exscal+3τ`. The dilation constant `Cdil`
of (S3) rides along on the right. -/
theorem slabPerBall (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    (hslab : cfg.δ ^ (2 * cfg.exscal) ≤ cfg.b)
    {bd : BallData cfg} (tc : ThinConfig cfg bd) (si : SlabInputs cfg bd tc τ)
    {B : bd.bι} (hB : B ∈ bd.bs) :
    (cfg.δ : ENNReal) ^ (9 * cfg.η + 10 * cfg.exscal + 3 * τ) *
        ∑ p ∈ retainedSegments tc hB, volume (bd.Y p).carrier ≤
      (bd.Cdil : ENNReal) * (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) *
        volume (tc.thinBall hB).U := by
  have hδE_ne0 : (cfg.δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr cfg.hδ.ne'
  have hδE_netop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- r₁² = δ^{2 exscal}, since r₁ = δ^{exscal}
  have hr1sq : (cfg.r₁ : ENNReal) ^ 2 = (cfg.δ : ENNReal) ^ (2 * cfg.exscal) := by
    rw [r₁, ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne']
    rw [pow_two, ← ENNReal.rpow_add _ _ hδE_ne0 hδE_netop]
    congr 1
    ring
  calc
    (cfg.δ : ENNReal) ^ (9 * cfg.η + 10 * cfg.exscal + 3 * τ) *
        ∑ p ∈ retainedSegments tc hB, volume (bd.Y p).carrier
        = (cfg.δ : ENNReal) ^ (8 * cfg.η + 8 * cfg.exscal + 3 * τ) *
            ((cfg.δ : ENNReal) ^ cfg.η * (cfg.δ : ENNReal) ^ (2 * cfg.exscal) *
              ∑ p ∈ retainedSegments tc hB, volume (bd.Y p).carrier) := by
      rw [show 9 * cfg.η + 10 * cfg.exscal + 3 * τ =
          (8 * cfg.η + 8 * cfg.exscal + 3 * τ) + cfg.η + 2 * cfg.exscal by ring]
      rw [ENNReal.rpow_add _ _ hδE_ne0 hδE_netop, ENNReal.rpow_add _ _ hδE_ne0 hδE_netop]
      ac_rfl
    _ ≤ (cfg.δ : ENNReal) ^ (8 * cfg.η + 8 * cfg.exscal + 3 * τ) *
        ((bd.Cdil : ENNReal) * ∑ j ∈ (tc.thinBall hB).bodies', volume (bd.Wb j).carrier) := by
      refine mul_le_mul' le_rfl ?_
      calc
        (cfg.δ : ENNReal) ^ cfg.η * (cfg.δ : ENNReal) ^ (2 * cfg.exscal) *
            ∑ p ∈ retainedSegments tc hB, volume (bd.Y p).carrier
            = (cfg.δ : ENNReal) ^ cfg.η * (cfg.r₁ : ENNReal) ^ 2 *
                ∑ p ∈ retainedSegments tc hB, volume (bd.Y p).carrier := by
          rw [← hr1sq]
        _ ≤ (bd.Cdil : ENNReal) * ∑ j ∈ (tc.thinBall hB).bodies', volume (bd.Wb j).carrier :=
          slabDensity cfg tc si hB
    _ = (bd.Cdil : ENNReal) * ((cfg.δ : ENNReal) ^ (8 * cfg.η + 8 * cfg.exscal + 3 * τ) *
        ∑ j ∈ (tc.thinBall hB).bodies', volume (bd.Wb j).carrier) := by
      ring
    _ ≤ (bd.Cdil : ENNReal) *
        ((slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) * volume (tc.thinBall hB).U) :=
      mul_le_mul' le_rfl (slabUnion cfg params hthin hslab tc si hB)
    _ = (bd.Cdil : ENNReal) * (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) *
        volume (tc.thinBall hB).U := by
      ring

/-- **The per-ball unions are pairwise disjoint** (blueprint `lem:ml2slabUnionDisjoint`).

By (C3) the shading `Y'_B` satisfies `Y'_B(T_B) ⊆ Y_B(T_B) ⊆ T_B ∩ B̂` — the fields
`Kakeya.ThinCase.ThinBall.shade_Y'_subset` and `Kakeya.VeryNotSticky.BallData.Y_piece` — so
`U(𝕋_B, Y'_B) ⊆ B̂`. The pieces `B̂`, `B ∈ 𝔅`, are pairwise disjoint by (C2)
(`Kakeya.VeryNotSticky.BallData.P_disjoint`), hence so are the sets `U(𝕋_B, Y'_B)`, and
countable additivity of Lebesgue measure on a finite disjoint family gives the displayed
equality.

The family is indexed by `bd.bs.attach` because `Kakeya.VeryNotSticky.ThinConfig.thinBall`
needs the membership proof. -/
theorem slabUnionDisjoint (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) :
    (↑bd.bs.attach : Set {x : bd.bι // x ∈ bd.bs}).PairwiseDisjoint
        (fun B ↦ (tc.thinBall B.2).U) ∧
      ∑ B ∈ bd.bs.attach, volume (tc.thinBall B.2).U =
        volume (⋃ B ∈ bd.bs.attach, (tc.thinBall B.2).U) := by
  let U_le_P : ∀ B : {x : bd.bι // x ∈ bd.bs}, (tc.thinBall B.2).U ⊆ bd.P B.1 := by
    intro B
    change (⋃ p ∈ bd.segs B.1, ((tc.thinBall B.2).Y' p).shade) ⊆ bd.P B.1
    refine Set.iUnion₂_subset (fun p hp => ?_)
    exact ((tc.thinBall B.2).shade_Y'_subset p hp).trans (bd.Y_piece B.1 B.2 p hp)
  have hdisj : (↑bd.bs.attach : Set {x : bd.bι // x ∈ bd.bs}).PairwiseDisjoint
        (fun B ↦ (tc.thinBall B.2).U) := by
    rw [Set.PairwiseDisjoint]
    intro a ha b hb hab
    have hne : a.1 ≠ b.1 := by
      intro h
      exact hab (Subtype.ext h)
    exact Disjoint.mono (U_le_P a) (U_le_P b) (bd.P_disjoint a.2 b.2 hne)
  have hmeas : ∀ B ∈ bd.bs.attach, MeasurableSet ((tc.thinBall B.2).U) := by
    intro B hB
    change MeasurableSet (⋃ p ∈ bd.segs B.1, ((tc.thinBall B.2).Y' p).shade)
    exact Finset.measurableSet_biUnion (bd.segs B.1)
      (fun p hp => ((tc.thinBall B.2).Y' p).measurableSet_shade)
  constructor
  · exact hdisj
  · exact (measure_biUnion_finset hdisj hmeas).symm

/-- **The per-ball unions sit inside `U(𝕋, Y)`** (blueprint `lem:ml2slabUnionSum`).

By the reverse compatibility of (T1) — the field
`Kakeya.VeryNotSticky.ThinConfig.compat_backward` — one has `U(𝕋_B, Y'_B) ⊆ U(𝕋, Y')` for each
`B`, and `Y' ⊆ Y_g ⊆ Y` (`Kakeya.VeryNotSticky.ThinConfig.Y'_subset`,
`Kakeya.VeryNotSticky.BallData.Yg_subset`) gives
`U(𝕋, Y') ⊆ U(𝕋, Y)`; so the union over `B ∈ 𝔅` is contained in `U(𝕋, Y)`. Now apply
`Kakeya.VeryNotSticky.slabUnionDisjoint` and monotonicity of the measure. -/
theorem slabUnionSum (cfg : VeryNotSticky.{u}) {bd : BallData cfg} (tc : ThinConfig cfg bd) :
    ∑ B ∈ bd.bs.attach, volume (tc.thinBall B.2).U ≤
      volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) := by
  have U_le : (⋃ B ∈ bd.bs.attach, (tc.thinBall B.2).U) ⊆
      ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade := by
    refine Set.iUnion₂_subset fun B hB => ?_
    change ⋃ p ∈ bd.segs B.1, ((tc.thinBall B.2).Y' p).shade ⊆
      ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade
    refine Set.iUnion₂_subset fun p hp => ?_
    intro x hx
    rw [Set.mem_iUnion₂]
    have hi : x ∈ (⋃ i ∈ bd.fam p, tc.Y' i) := tc.compat_backward B.1 B.2 p hp hx
    rw [Set.mem_iUnion₂] at hi
    rcases hi with ⟨i, hifam, hxi⟩
    refine ⟨i, ?_, ?_⟩
    · exact bd.fam_subset B.1 B.2 p hp hifam
    · exact bd.Yg_subset i (bd.fam_subset B.1 B.2 p hp hifam)
        (tc.Y'_subset i (bd.fam_subset B.1 B.2 p hp hifam) hxi)
  calc
    ∑ B ∈ bd.bs.attach, volume (tc.thinBall B.2).U =
        volume (⋃ B ∈ bd.bs.attach, (tc.thinBall B.2).U) := (slabUnionDisjoint cfg tc).2
    _ ≤ volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) := measure_mono U_le

/-- **Reaching the volume form of the goal** (blueprint `lem:ml2slabVolumeGoal`).

The hypothesis is the honest `δ^{11η+10 exscal+3τ}` of `Kakeya.VeryNotSticky.slabMassBound`
(before F8 it read `7η` and was weakened here to `11η`; the (C5) exponent `2η` in the density clause spent exactly that `4η` margin), and the two thresholds absorb the constant
`K = C · Cm · m · Cdil · C_{lem:ml2slabUnion}(C,C₀,exscal)`: (S6) gives
`C · Cdil · C_{lem:ml2slabUnion} · δ^{β/2} ≤ δ^{12η+12 exscal+3τ}` and (S7) gives
`Cm · m ≤ δ^{-(η+2 exscal)}`, so `K δ^{β/2} ≤ δ^{11η+10 exscal+3τ}` and
`K δ^{β/2} ∑_T |T| ≤ δ^{11η+10 exscal+3τ} ∑_T |T| ≤ K |U(𝕋,Y)|`; cancelling `K` gives
`δ^{β/2} ∑_T |T| ≤ |U(𝕋,Y)|`.
By (S4), `|𝕋|^β ≥ δ^{-β}`, so
`δ^{β/2} |U(𝕋,Y)| |𝕋|^β ≥ δ^{-β/2} |U(𝕋,Y)| ≥ ∑_T |T|`, which is
`Kakeya.VeryNotSticky.goalUnion` with gain `ν = β/2`. -/
theorem slabVolumeGoal (cfg : VeryNotSticky.{u}) {τ : ℝ} {bd : BallData cfg}
    (tc : ThinConfig cfg bd) (si : SlabInputs cfg bd tc τ)
    (h : (cfg.δ : ENNReal) ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) *
        ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier ≤
      (tc.C : ENNReal) * (bd.Cm : ENNReal) * (bd.m : ENNReal) * (bd.Cdil : ENNReal) *
        (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) *
        volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade)) :
    cfg.goalUnion (cfg.β / 2) := by
  let d : ENNReal := (cfg.δ : ENNReal)
  let S : ENNReal := ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier
  let V : ENNReal := volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade)
  let N : ENNReal := (cfg.s.card : ENNReal)
  -- the `δ`-free constant absorbed by (S6)
  let Cf : ENNReal := (tc.C : ENNReal) * (bd.Cdil : ENNReal) *
    (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal)
  -- the fibre-count datum absorbed by (S7)
  let Km : ENNReal := (bd.Cm : ENNReal) * (bd.m : ENNReal)
  -- the whole constant of the hypothesis
  let K : ENNReal := Km * Cf
  have hd0 : d ≠ 0 := by dsimp [d]; exact ENNReal.coe_ne_zero.mpr (ne_of_gt cfg.hδ)
  have hdtop : d ≠ ⊤ := by dsimp [d]; exact ENNReal.coe_ne_top
  have hd1 : d ≤ 1 := by dsimp [d]; exact ENNReal.coe_le_one_iff.mpr cfg.hδ1
  change S ≤ d ^ (cfg.β / 2) * V * N ^ cfg.β
  -- the hypothesis, with its constant regrouped as `K`
  have h' : d ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) * S ≤ K * V := by
    have hK : K = (tc.C : ENNReal) * (bd.Cm : ENNReal) * (bd.m : ENNReal) *
        (bd.Cdil : ENNReal) * (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) := by
      dsimp [K, Km, Cf]
      ring
    rw [hK]
    exact h
  -- (S4): `1 ≤ δ |𝕋|`, so `1 ≤ δ^β |𝕋|^β`.
  have htube : (1 : ENNReal) ≤ d * N := by simpa [d, N] using si.tubeCount
  have hstep1 : (1 : ENNReal) ≤ d ^ cfg.β * N ^ cfg.β := by
    have hprod : (d * N) ^ cfg.β = d ^ cfg.β * N ^ cfg.β :=
      ENNReal.mul_rpow_of_ne_top hdtop (by dsimp [N]; exact ENNReal.coe_ne_top) cfg.β
    rw [← hprod]
    exact ENNReal.one_le_rpow htube cfg.hβ
  -- The hypothesis is already at the honest `11η` (F8 spent the former `4η` margin), so the
  -- former weakening step `7η ≤ 11η` is now `le_refl`.
  have hleexp : 11 * cfg.η + 10 * cfg.exscal + 3 * τ ≤
      11 * cfg.η + 10 * cfg.exscal + 3 * τ := le_refl _
  have hdrop : d ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) ≤
      d ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hd1 hleexp
  have hstep : d ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) * S ≤ K * V := by
    calc
      d ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) * S
          ≤ d ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) * S := mul_le_mul_left hdrop S
      _ ≤ K * V := h'
  -- (S6) absorbs the `δ`-free constants — `fibreMassConstant` among them
  --  — and (S7) the fibre count: `K δ^{β/2} ≤ δ^{11η+…}`.
  have hft : (fibreMassConstant : ENNReal) * Cf * d ^ (cfg.β / 2) ≤
      d ^ (12 * cfg.η + 12 * cfg.exscal + 3 * τ) := by
    simpa [Cf, d, mul_assoc] using si.finalThreshold
  have hfm : Km ≤ (fibreMassConstant : ENNReal) * d ^ (-(cfg.η + 2 * cfg.exscal)) := by
    simpa [Km, d] using si.fibreMassThreshold
  have hKd : K * d ^ (cfg.β / 2) ≤ d ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) := by
    calc
      K * d ^ (cfg.β / 2) = Km * (Cf * d ^ (cfg.β / 2)) := by
        dsimp [K]
        ring
      _ ≤ ((fibreMassConstant : ENNReal) * d ^ (-(cfg.η + 2 * cfg.exscal))) *
          (Cf * d ^ (cfg.β / 2)) := mul_le_mul' hfm le_rfl
      _ = d ^ (-(cfg.η + 2 * cfg.exscal)) *
          ((fibreMassConstant : ENNReal) * Cf * d ^ (cfg.β / 2)) := by ring
      _ ≤ d ^ (-(cfg.η + 2 * cfg.exscal)) * d ^ (12 * cfg.η + 12 * cfg.exscal + 3 * τ) :=
        mul_le_mul' le_rfl hft
      _ = d ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) := by
        rw [← ENNReal.rpow_add _ _ hd0 hdtop]
        congr 1
        ring
  have hmid : K * (d ^ (cfg.β / 2) * S) ≤ K * V := by
    calc
      K * (d ^ (cfg.β / 2) * S) = (K * d ^ (cfg.β / 2)) * S := by ac_rfl
      _ ≤ d ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) * S := mul_le_mul_left hKd S
      _ ≤ K * V := hstep
  have hKtop : K ≠ ⊤ := by
    dsimp [K, Km, Cf]
    simp only [← ENNReal.coe_mul]
    exact ENNReal.coe_ne_top
  by_cases hK0 : K = 0
  · -- If `K = 0`, the hypothesis forces `S = 0` and the goal is trivial.
    have hlow : d ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) * S ≤ 0 := by
      rw [hK0, zero_mul] at h'
      exact h'
    have hdS0 : d ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) * S = 0 := by
      apply le_antisymm hlow
      simp
    have hdneb : d ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) ≠ 0 := by
      intro hz
      rcases (ENNReal.rpow_eq_zero_iff.mp hz) with ⟨hd0', _⟩ | ⟨hdt, _⟩
      · exact hd0 hd0'
      · exact hdtop hdt
    have hS0 : S = 0 := (mul_eq_zero.mp hdS0).resolve_left hdneb
    simp [hS0]
  · -- `K ≠ 0`: cancel it to get `δ^{β/2} · S ≤ V`.
    have hcancel : d ^ (cfg.β / 2) * S ≤ V := by
      have hVm : (d ^ (cfg.β / 2) * S) * K ≤ V * K := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmid
      exact (ENNReal.mul_le_mul_iff_left hK0 hKtop).mp hVm
    calc
      S = (1 : ENNReal) * S := by rw [one_mul]
      _ ≤ (d ^ cfg.β * N ^ cfg.β) * S := by
        simpa [one_mul] using mul_le_mul_left hstep1 S
      _ = (d ^ (cfg.β / 2) * N ^ cfg.β) * (d ^ (cfg.β / 2) * S) := by
        have hij : cfg.β / 2 + cfg.β / 2 = cfg.β := by ring
        have hpair : d ^ (cfg.β / 2) * d ^ (cfg.β / 2) = d ^ cfg.β := by
          simpa [hij] using (ENNReal.rpow_add (cfg.β / 2) (cfg.β / 2) hd0 hdtop).symm
        rw [← hpair]
        ac_rfl
      _ ≤ (d ^ (cfg.β / 2) * N ^ cfg.β) * V :=
        mul_le_mul_right hcancel (d ^ (cfg.β / 2) * N ^ cfg.β)
      _ = d ^ (cfg.β / 2) * V * N ^ cfg.β := by ac_rfl

/-- **Summing the per-ball estimate over the whole family** (blueprint `lem:ml2slab`, summation
step).

Sum `Kakeya.VeryNotSticky.slabPerBall` over `B ∈ 𝔅`, apply the segment-mass input (S5) of
`Kakeya.VeryNotSticky.SlabInputs` on the left and `Kakeya.VeryNotSticky.slabUnionSum` on the
right. This is the hypothesis of `Kakeya.VeryNotSticky.slabVolumeGoal`.

(S5) brings the density loss `δ^{2η}` to the left — hence `11η` and not `9η` — and the fibre
count `C · Cm · m` to the right, and (S3), through `slabPerBall`, the dilation constant `Cdil`.

No distinguished ball is taken: the argument uses *all* balls of `𝔅`, and the pairwise
disjointness of the pieces `B̂` is what makes the summation legitimate. -/
theorem slabMassBound (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    (hslab : cfg.δ ^ (2 * cfg.exscal) ≤ cfg.b)
    {bd : BallData cfg} (tc : ThinConfig cfg bd) (si : SlabInputs cfg bd tc τ) :
    (cfg.δ : ENNReal) ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) *
        ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier ≤
      (tc.C : ENNReal) * (bd.Cm : ENNReal) * (bd.m : ENNReal) * (bd.Cdil : ENNReal) *
        (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) *
        volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) := by
  have hd0 : (cfg.δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr cfg.hδ.ne'
  have hdtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- the per-ball estimates, summed over `𝔅` and bounded by `|U(𝕋, Y)|`
  have hsum : (cfg.δ : ENNReal) ^ (9 * cfg.η + 10 * cfg.exscal + 3 * τ) *
        ∑ B ∈ bd.bs.attach, ∑ p ∈ retainedSegments tc B.2, volume (bd.Y p).carrier ≤
      (bd.Cdil : ENNReal) * (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) *
        volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) := by
    calc
      (cfg.δ : ENNReal) ^ (9 * cfg.η + 10 * cfg.exscal + 3 * τ) *
          ∑ B ∈ bd.bs.attach, ∑ p ∈ retainedSegments tc B.2, volume (bd.Y p).carrier
          = ∑ B ∈ bd.bs.attach, (cfg.δ : ENNReal) ^ (9 * cfg.η + 10 * cfg.exscal + 3 * τ) *
              ∑ p ∈ retainedSegments tc B.2, volume (bd.Y p).carrier := by
            rw [Finset.mul_sum]
      _ ≤ ∑ B ∈ bd.bs.attach, (bd.Cdil : ENNReal) *
              (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) *
              volume (tc.thinBall B.2).U :=
            Finset.sum_le_sum (fun B _ => slabPerBall cfg params hthin hslab tc si B.2)
      _ = (bd.Cdil : ENNReal) * (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) *
              ∑ B ∈ bd.bs.attach, volume (tc.thinBall B.2).U := by
            rw [← Finset.mul_sum]
      _ ≤ (bd.Cdil : ENNReal) * (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) *
              volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) :=
            mul_le_mul' le_rfl (slabUnionSum cfg tc)
  calc
    (cfg.δ : ENNReal) ^ (11 * cfg.η + 10 * cfg.exscal + 3 * τ) *
        ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier
        = (cfg.δ : ENNReal) ^ (9 * cfg.η + 10 * cfg.exscal + 3 * τ) *
            ((cfg.δ : ENNReal) ^ (2 * cfg.η) *
              ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier) := by
          rw [show 11 * cfg.η + 10 * cfg.exscal + 3 * τ =
              (9 * cfg.η + 10 * cfg.exscal + 3 * τ) + 2 * cfg.η by ring]
          rw [ENNReal.rpow_add _ _ hd0 hdtop, mul_assoc]
    _ ≤ (cfg.δ : ENNReal) ^ (9 * cfg.η + 10 * cfg.exscal + 3 * τ) *
            ((tc.C : ENNReal) * (bd.Cm : ENNReal) * (bd.m : ENNReal) *
              ∑ B ∈ bd.bs.attach, ∑ p ∈ retainedSegments tc B.2, volume (bd.Y p).carrier) :=
          mul_le_mul' le_rfl si.segmentMass
    _ = (tc.C : ENNReal) * (bd.Cm : ENNReal) * (bd.m : ENNReal) *
            ((cfg.δ : ENNReal) ^ (9 * cfg.η + 10 * cfg.exscal + 3 * τ) *
              ∑ B ∈ bd.bs.attach, ∑ p ∈ retainedSegments tc B.2, volume (bd.Y p).carrier) := by
          ring
    _ ≤ (tc.C : ENNReal) * (bd.Cm : ENNReal) * (bd.m : ENNReal) *
            ((bd.Cdil : ENNReal) * (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) *
              volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade)) :=
          mul_le_mul' le_rfl hsum
    _ = (tc.C : ENNReal) * (bd.Cm : ENNReal) * (bd.m : ENNReal) * (bd.Cdil : ENNReal) *
            (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) *
            volume (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade) := by
          ring

end Kakeya.VeryNotSticky

namespace Kakeya

/-- **Main Lemma 2, slab case** (blueprint `lem:ml2slab`).

In the configuration `cfg`, together with the per-ball data `bd` of Configuration
`hyp:ml2setup` and the thin-case data `tc` of Configuration `hyp:ml2thinsetup` over it, and
with the thin-case refinement `a ≤ δ^{1-τ}`, suppose we are in the *slab case*, i.e.
`b ≥ δ^{exscal} r₁ = δ^{2·exscal}` for the convex bodies `W ∈ 𝕎_B`. Then the goal
`μ(𝕋, Y) ≤ δ^ν |𝕋|^β` holds with the explicit gain `ν = β/2`.

The gain is stated explicitly rather than existentially because it is the value
`Kakeya.VeryNotSticky.thinExponent` hard-codes for this branch. The exact inequality making
the exponent `β - 12η - 12·exscal - 3τ` — the blueprint's `β - 9η - 10·exscal - 3τ` after the
repaired (T7) and (C3) — at least `β/2` is
`Kakeya.VeryNotSticky.CaseParams.slab`.

The proof sums the per-ball estimate `Kakeya.VeryNotSticky.slabPerBall` over `B ∈ 𝔅`, applies
`Kakeya.VeryNotSticky.slabUnionSum` on the right and the segment-mass input (S5) of
`Kakeya.VeryNotSticky.SlabInputs` on the left, obtaining
`δ^{11η+10 exscal+3τ} ∑_T |T| ≤ C · Cm · m · Cdil · C_{lem:ml2slabUnion}(C,C₀,exscal) |U(𝕋,Y)|`;
`Kakeya.VeryNotSticky.slabVolumeGoal` turns this into the volume form of the goal with gain
`β/2`, and `Kakeya.VeryNotSticky.goalMult_of_goalUnion` converts it into the multiplicity
currency with no constant lost.

No distinguished ball is taken, since the argument uses *all* balls of `𝔅`;
`bd.bs_nonempty` and the pairwise disjointness of the pieces `B̂` are what make the summation
legitimate.

Beyond the two Configurations and the two case hypotheses the statement assumes only the
fixed-scale bundle `ss : Kakeya.VeryNotSticky.SlabScale cfg bd tc τ`, which is what lets it
apply `Kakeya.VeryNotSticky.slabInputs` internally and so assume nothing else. The further
facts the proof uses are the eight inputs `Kakeya.VeryNotSticky.SlabInputs`, and they are now
*produced*, not accepted: four are items of the standing configuration — (S2) on (C4), (S3) on
(C3), (S4) on (C1), (S5) on (T7) — and the remaining four, `δ < 1`, (S1), (S6) and (S7), are
the fields of `ss`. They cannot be fields of `Kakeya.VeryNotSticky.CaseScale`, since two of them
mention the thin-case constant `tc.C`, which that bundle is stated before.

The extra hypothesis costs one argument at the unique call site inside
`Kakeya.goalMult_of_a_le`, from where it is threaded up to
`Kakeya.VeryNotSticky.exists_goalMult`. -/
theorem goalMult_of_b_ge (cfg : VeryNotSticky) {τ τ' : ℝ}
    (params : VeryNotSticky.CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    (hslab : cfg.δ ^ (2 * cfg.exscal) ≤ cfg.b)
    {bd : VeryNotSticky.BallData cfg} (tc : VeryNotSticky.ThinConfig cfg bd)
    (ss : VeryNotSticky.SlabScale cfg bd tc τ) :
    cfg.goalMult (cfg.β / 2) := by
  have si : VeryNotSticky.SlabInputs cfg bd tc τ := VeryNotSticky.slabInputs cfg tc ss
  exact VeryNotSticky.goalMult_of_goalUnion cfg
    (VeryNotSticky.slabVolumeGoal cfg tc si
      (VeryNotSticky.slabMassBound cfg params hthin hslab tc si))

end Kakeya
