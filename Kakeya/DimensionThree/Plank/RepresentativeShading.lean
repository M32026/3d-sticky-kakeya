/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.LinearCover
public import Kakeya.DimensionThree.Plank.BoxMassCapture
public import Kakeya.DimensionThree.Plank.AssignedSlabFamily
public import Kakeya.DimensionThree.Plank.DenseBoxCover
public import Kakeya.DimensionThree.Plank.LocalAngleConcentration

/-!
# Item 2 on the canonical assigned representative fibre

This file runs the C-linear cover route of
`Kakeya/DimensionThree/Plank/LinearCoverRoute.lean` with the plank family taken to be the
**canonical assigned family**

`𝒜_S = Plank.assignedSlabFamily s₁ repr slabOf S`

and the representative family taken to be its own `repr`-image, which
`Plank.image_repr_assignedSlabFamily` identifies with the canonical public fibre
`R.indexSet.filter (fun Q => slabOf Q = S)`.

Nothing is selected and nothing is pruned.  The three inputs the good cover needs are produced on
that same family:

* hypothesis (5), local angular concentration, is supplied by the caller for every dense-box family
  — `Kakeya.slabwiseShading_fixedSlab` builds it on the slabwise shading;
* the captured mass by `Plank.hcap_of_fullness_assigned`, at the absolute cost `#gridShiftSet = 8`;
* the fibre-size bounds verbatim from the preassembly, by
  `Plank.filter_repr_assignedSlabFamily_eq` — a representative's fibre inside its own slab's
  assigned family is its whole fibre, so no new pigeonhole is needed.

The exponent is therefore untouched: `cLam = cGood cStb / (128 cTan)` and
`cKappa = 4 cGood cStb ρ / (cTan Cbox³)` are absolute, and the conclusion is at `c₂ · a^(4η)`
with `c₂ = cDia · cLam² · cKappa`.  Here `ρ` is the outer *ratio* parameter bounding `L / W` for the
configuration-dependent fibre window; taking `ρ = cN⁻¹ · cN⁻¹` at `L = N / cN`, `W = cN · N` gives
`ρ · W = L`, so the aggregate loses exactly `cN⁻²` and no power of `a`.  No
representative-cardinality retention factor occurs, and no Markov selection is used.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

/-! ## Half-box mass capture on the assigned slab family

`Plank.exists_dominantGoodSlabRefinement` already delivers its per-slab mass clause on the
*assigned* family `Plank.assignedSlabFamily`, so the capture step that feeds the good cover can be
run there directly: no transport from the geometric family is needed for the mass, and in
particular the set-level bridge of `Kakeya/DimensionThree/Plank/SlabSelection.lean` is not
used here.

Two small pieces are supplied.

* `Plank.mem_inSlabFamilyC_assignedSlabFamily` discharges the *geometric* hypothesis `hfam` of
  `Plank.exists_shift_halfBox_capture_of_fullness`.  That hypothesis asks only that each individual
  plank be comparable with `S`, which the preassembly guarantees for each plank's *own* slab; for a
  plank assigned to `S` that slab is `S`.  This is the one place `Plank.inSlabFamilyC` still
  appears, and it appears as an internal requirement of a low-level theorem, not as an index family
  the route carries.
* `Plank.hcap_of_fullness_assigned` packages the capture in exactly the shape of the `hcap`
  hypothesis of `Plank.exists_goodCover_saturated_aggregate`, with the saturated box families
  `T q = {i ∈ 𝒜_S : Y_i ∩ ½B_q ≠ ∅}` that the C-linear route and the angular concentration step
  both consume.

The whole cost of the conversion is the absolute `#gridShiftSet = 8`; no power of `a` is spent, and
the numeric side condition `8 c_good c_stb a^η ≤ μ` is exactly the ledger's.
-/

section AssignedHalfBoxCapture

variable {ι τ : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}

/-- **The geometric hypothesis of the capture step, on the assigned family.**  The preassembly
returns, for every plank of `s'`, membership in the geometric slab family of *its own* assigned
slab.  For a plank assigned to `S` that slab is `S`, and the two conditions defining
`Plank.inSlabFamilyC` — carrier inside the `Cset`-dilation, angle at most `Cang · θ` — do not
mention the ambient index set, so they survive restriction to the assigned family.

This is the only place the geometric family occurs on the assigned route, and it occurs as an
internal requirement of `Plank.exists_shift_halfBox_capture_of_fullness`, not as a family the route
carries. -/
theorem mem_inSlabFamilyC_assignedSlabFamily {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (Cset Cang : ℝ≥0) (s' : Finset ι) (V : ι → Plank a b hab hb1)
    (repr : ι → τ) (slabOf : τ → Slab θ hθ1) (S : Slab θ hθ1)
    (hgeo : ∀ i ∈ s', i ∈ inSlabFamilyC Cset Cang s' V (slabOf (repr i)))
    (i : ι) (hi : i ∈ assignedSlabFamily s' repr slabOf S) :
    i ∈ inSlabFamilyC Cset Cang (assignedSlabFamily s' repr slabOf S) V S := by
  obtain ⟨his, hslab⟩ := mem_assignedSlabFamily.mp hi
  have hgeo_i := hgeo i his
  rw [hslab] at hgeo_i
  rw [mem_inSlabFamilyC] at hgeo_i ⊢
  exact ⟨hi, hgeo_i.2⟩

open scoped Classical in
/-- **The `hcap` of the C-linear good cover, on the assigned family.**  The packaged middle-half
capture of `Plank.exists_shift_halfBox_capture_of_fullness`, rewritten into exactly the shape that
`Plank.exists_goodCover_saturated_aggregate` consumes, with the saturated local families

`T q = {i ∈ s : Y_i ∩ ½B_q ≠ ∅}`.

Those are the families the angular-concentration hypothesis is stated for, so the two hypotheses of
the good cover are produced against the same box families.

The arithmetic is the ledger's: the capture gives `μ · #s · 8ab ≤ 8 · (captured)`, the two `8`s
cancel, and `8 c_good c_stb a^η ≤ μ` turns the result into the required lower bound.  The only cost
is the absolute `#gridShiftSet = 8`. -/
theorem hcap_of_fullness_assigned {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (S : Slab θ hθ1) (Cset Cang μ cGood cStb : ℝ≥0) (hCset : 1 ≤ Cset)
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (η : ℝ)
    (hθ : 0 < θ) (hb : 0 < b) (hb1' : b ≤ 1)
    (hshade : ∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hfam : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V S)
    (hfull : μ ≤ ShadedBody.fullness s Y)
    (hcarvol : ∀ i ∈ s, 8 * (a : ENNReal) * (b : ENNReal) ≤ volume (Y i).carrier)
    (hμ : 8 * cGood * cStb * a ^ η ≤ μ) :
    ∃ sh ∈ gridShiftSet,
      ((8 * cGood * cStb * a ^ η * (a * b) : ℝ≥0) : ENNReal) * (s.card : ENNReal)
        ≤ ∑ q ∈ slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊,
            ∑ i ∈ s.filter (fun i => ((Y i).shade ∩ halfSlabBox S b sh q).Nonempty),
              volume ((Y i).shade ∩ halfSlabBox S b sh q) := by
  obtain ⟨sh, hsh, hcap⟩ := exists_shift_halfBox_capture_of_fullness
    S Cset Cang μ hCset s V Y hθ hb hb1' hshade hfam hfull hcarvol
  have hcup : (gridShiftSet.card : ENNReal) = 8 := by
    exact_mod_cast gridShiftSet_card
  have h80 : (8 : ENNReal) ≠ 0 := by norm_num
  have h8t : (8 : ENNReal) ≠ ⊤ := by norm_num
  refine ⟨sh, hsh, ?_⟩
  exact (ENNReal.mul_le_mul_iff_right (a := (8 : ENNReal)) h80 h8t).mp (by
    calc
      8 * (((8 * cGood * cStb * a ^ η * (a * b) : ℝ≥0) : ENNReal) * (s.card : ENNReal))
          ≤ 8 * ((μ : ENNReal) * (a : ENNReal) * (b : ENNReal) * (s.card : ENNReal)) := by
        have hm : (8 * cGood * cStb * a ^ η * (a * b) : ℝ≥0) ≤ μ * (a * b) := by
          gcongr
        have hme : ((8 * cGood * cStb * a ^ η * (a * b) : ℝ≥0) : ENNReal)
            ≤ (μ : ENNReal) * (a : ENNReal) * (b : ENNReal) := by
          calc
            ((8 * cGood * cStb * a ^ η * (a * b) : ℝ≥0) : ENNReal)
                ≤ ((μ * (a * b) : ℝ≥0) : ENNReal) := by exact_mod_cast hm
            _ = (μ : ENNReal) * (a : ENNReal) * (b : ENNReal) := by
              simp [ENNReal.coe_mul, mul_assoc]
        gcongr
      _ = (μ : ENNReal) * ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) := by
        ring
      _ ≤ 8 * ∑ q ∈ slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊,
              ∑ i ∈ s.filter (fun i => ((Y i).shade ∩ halfSlabBox S b sh q).Nonempty),
                volume ((Y i).shade ∩ halfSlabBox S b sh q) := by
        simpa [hcup] using hcap)

end AssignedHalfBoxCapture

/-! ## Item 2 on the canonical assigned representative fibre -/

variable {ι : Type*}

open scoped Classical in
/-- **The C-linear Item 2 core on the canonical assigned representative fibre.**

The cover route run on the assigned family `𝒜_S` of a fixed slab, at an arbitrary input shading
`Yd`.  The representative family is `𝒜_S.image repr`, which `Plank.image_repr_assignedSlabFamily`
identifies with the canonical public fibre `R.indexSet.filter (fun Q => slabOf Q = S)`; no subfamily
of it appears anywhere in the statement or the proof, so no representative is deleted and the common
fibre size `N` survives.

Hypothesis (5), local angular concentration, is supplied directly for every dense-box family `D`,
and `Ceta` is an outer constant: the cover route itself never needs to know which shading produced
it.  The route is C-linear — `κQ`, `Plank.sum_coverFraction_ge`,
`Plank.boxCount_of_fibreLocalScore` — and the exponent is `4 * η`.

The two constants are `cLam = cGood · cStb / (128 · cTan)` and
`cKappa = 4 · cGood · cStb · ρ / (cTan · Cbox³)`.  The fibre window `L ≤ #rep⁻¹(u) ≤ W` is
*configuration-dependent* — in the application `L = N / cN` and `W = cN · N` — so it is bound inside
the configuration quantifier and may not enter `c₂`.  Only its ratio may, and that ratio is the
outer `ρ`, constrained by `ρ · W ≤ L`; the aggregate cover-fraction bound of
`Plank.exists_goodCover_saturated_aggregate` is stated at `L / W` and is weakened to `ρ` here.  In
the application `ρ = cN⁻¹ · cN⁻¹` and `ρ · W = L` exactly, so nothing is lost. -/
theorem representativeShading_of_capture
    (cTan cGood cStb Cang Cc Ceta ρ : ℝ≥0)
    (hcTan : 1 ≤ cTan) (hcGood : 0 < cGood) (hcStb : 0 < cStb)
    (hCang : 1 ≤ Cang) (hCc : 1 ≤ Cc) (hCeta : 0 < Ceta) (hρ : 0 < ρ)
    {η : ℝ} (hη : 0 < η) :
    ∃ c2 : ℝ≥0, 0 < c2 ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθb : θ * b ≤ b} {hθ1 : θ ≤ 1}
        {ι τ : Type*}
        (s₁ : Finset ι) (V : ι → Plank a b hab hb1)
        (Yd : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (repr : ι → τ) (slabOf : τ → Slab θ hθ1) (S : Slab θ hθ1)
        (sh : Fin 3 → ℝ) (𝒦 : Finset (Fin 3 → ℤ))
        (Pr : τ → Prism3D (θ * b) b 1 hθb hb1)
        (Yθ : τ → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (T : (Fin 3 → ℤ) → Finset ι)
        (Z : (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (L W : ℝ≥0),
        0 < a → 0 < b → 0 < θ → a / b ≤ θ →
        -- the fibre-size window is configuration-dependent (`L ≍ N / cN`, `W ≍ cN · N`), so only
        -- its *ratio* may enter `c2`; that ratio is the outer `ρ`
        0 < L → 0 < W → ρ * W ≤ L →
        (assignedSlabFamily s₁ repr slabOf S).Nonempty →
        -- the saturated local families, on the assigned family
        (∀ q, T q ⊆ assignedSlabFamily s₁ repr slabOf S) →
        (∀ q, ∀ i ∈ T q, (Z q i).shade = (Yd i).shade ∩ halfSlabBox S b sh q) →
        (∀ q, ∀ i ∈ T q, (Z q i).carrier = (V i).carrier) →
        -- hypothesis (5), supplied for every dense-box family
        (∀ D : τ → Finset (Fin 3 → ℤ),
          LocalAngleConcentration V θ ((assignedSlabFamily s₁ repr slabOf S).image repr) D
            (fun _ => T) (fun _ => Z) Ceta η) →
        -- geometric data
        (∀ i ∈ assignedSlabFamily s₁ repr slabOf S,
          (Yd i).shade
            ⊆ (((Pr (repr i)).toPrismNDim.dilation Cc).carrier :
                Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ assignedSlabFamily s₁ repr slabOf S,
          (Yd i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ q, ∀ i ∈ T q, Kakeya.ComparableScalars cTan
          (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
            (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2)) →
        (∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
          Prism3D.angle (Pr u) S ≤ (Cang : ℝ) * (θ : ℝ)) →
        -- fibre-size bounds, inherited verbatim from the preassembly
        (∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
          L ≤ ((((assignedSlabFamily s₁ repr slabOf S).filter
            (fun i => repr i = u)).card : ℕ) : ℝ≥0)) →
        (∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
          ((((assignedSlabFamily s₁ repr slabOf S).filter
            (fun i => repr i = u)).card : ℕ) : ℝ≥0) ≤ W) →
        -- the captured mass, on the assigned family
        (((8 * cGood * cStb * a ^ η * (a * b) : ℝ≥0) : ENNReal) *
            (((assignedSlabFamily s₁ repr slabOf S).card : ℕ) : ENNReal)
          ≤ ∑ q ∈ 𝒦, ∑ i ∈ T q,
              volume ((Yd i).shade ∩ halfSlabBox S b sh q)) →
        -- the shading of the output family
        (∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
          ((Yθ u).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            = ((Pr u).toPrismNDim.dilation (4 * Cang + 8 + Cc)).carrier) →
        (∀ u ∈ (assignedSlabFamily s₁ repr slabOf S).image repr,
          (Yθ u).shade
            = (⋃ i ∈ assignedSlabFamily s₁ repr slabOf S, (Yd i).shade) ∩
              (((Pr u).toPrismNDim.dilation (4 * Cang + 8 + Cc)).carrier :
                Set (EuclideanSpace ℝ (Fin 3)))) →
        c2 * a ^ (4 * η)
          ≤ ShadedBody.fullness ((assignedSlabFamily s₁ repr slabOf S).image repr) Yθ := by
  have hcTan0 : (0 : ℝ≥0) < cTan := lt_of_lt_of_le zero_lt_one hcTan
  have hCboxpos : (0 : ℝ≥0) < 4 * Cang + 8 + Cc :=
    lt_of_lt_of_le Nat.ofNat_pos (le_add_self.trans le_self_add)
  have hcLam : (0 : ℝ≥0) < cGood * cStb / (128 * cTan) :=
    div_pos (mul_pos hcGood hcStb) (mul_pos Nat.ofNat_pos hcTan0)
  have hcKappa : (0 : ℝ≥0) < 4 * cGood * cStb * ρ / (cTan * (4 * Cang + 8 + Cc) ^ 3) :=
    div_pos (mul_pos (mul_pos (mul_pos Nat.ofNat_pos hcGood) hcStb) hρ)
      (mul_pos hcTan0 (pow_pos hCboxpos 3))
  obtain ⟨c2, hc2pos, hitem2⟩ := aggregateShading_of_goodCover cTan Ceta
    (cGood * cStb / (128 * cTan)) (4 * cGood * cStb * ρ / (cTan * (4 * Cang + 8 + Cc) ^ 3))
    hCeta hcLam hcKappa
  refine ⟨c2, hc2pos, ?_⟩
  intro a b θ hab hb1 hθb hθ1 ι τ s₁ V Yd repr slabOf S sh 𝒦 Pr Yθ T Z L W
    ha hb hθ habθ hL hW hρLW hne hTs hZsh hZcar hLAC hsubPr hshV htan hangPr
    hlo hup hcap hcar hshade
  obtain ⟨D, κQ, hD𝒦, hcontain, hboxfull, hcover, haggr⟩ :=
    exists_goodCover_saturated_aggregate cTan cGood cStb Cang Cc L W hcTan hcGood hcStb
      hCang hCc hL hW
      S sh 𝒦 (assignedSlabFamily s₁ repr slabOf S) V Yd T Z
      ((assignedSlabFamily s₁ repr slabOf S).image repr) Pr repr η
      ha hb hθ hne hTs (fun i hi => Finset.mem_image_of_mem repr hi) hlo hup hsubPr hshV
      hZsh hZcar htan hangPr hcap
  -- the aggregate cover-fraction constant is weakened from the configuration-dependent
  -- `L / W` to the outer ratio `ρ`; this is the only place the fibre window is used
  have hcoeff : 4 * cGood * cStb * ρ / (cTan * (4 * Cang + 8 + Cc) ^ 3)
      ≤ 4 * cGood * cStb * L / (cTan * W * (4 * Cang + 8 + Cc) ^ 3) := by
    have h : ∀ x y z : ℝ≥0, x * L / (y * W * z) = x * (L / W) / (y * z) := fun x y z => by
      rw [← mul_div_assoc, div_div, ← mul_assoc, mul_comm W y]
    rw [h]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_right ((le_div_iff₀ hW).2 hρLW) _) zero_le
  exact hitem2 (assignedSlabFamily s₁ repr slabOf S) V Yd
    S sh ((assignedSlabFamily s₁ repr slabOf S).image repr) Pr (4 * Cang + 8 + Cc) Yθ D
    (fun _ => T) (fun _ => Z) η κQ
    ha hb hθ hη hCboxpos habθ (hLAC D) (hne.image repr) hshV hcar hshade
    (fun u hu q => hTs q)
    (fun u hu q i hi => by
      rw [hZsh q i hi]
      exact Set.inter_subset_inter_right _ (halfSlabBox_subset S b sh q))
    (fun u hu q i hi => hZcar q i hi)
    (fun u hu q hq i hi => htan q i hi)
    hboxfull hcontain hcover
    (le_trans (mul_le_mul_left (mul_le_mul_left hcoeff _) _) haggr)

end Plank

/-!
## The assigned slab family sits inside the geometric one

Item 2 runs on two index families and keeps them apart:

* the **assigned** family `Plank.assignedSlabFamily s' repr slabOf S` — the exact fibre of
  `slabOf ∘ repr` — carries the mass partition and is what the public statement uses;
* the **geometric** family `Plank.inSlabFamilyC Cset Cang s' V S` — every plank comparable with the
  slab — is what the shade containment lands in.

Only one direction between them is true, and it is the one proved here: a plank assigned to `S` is
geometrically comparable with `S`.  The converse is false and is used nowhere.
-/

namespace Plank

variable {ι τ : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}

/-- **The assigned family sits inside the geometric family of its own slab.**  The generic form of
`Plank.assignedSlabFamily_subset_inSlabFamilyC`, which is stated only for
`repr : ι → Plank.EnsemblePrism`; here the representative type is arbitrary, as the typed route
needs.

Only the containment direction that is actually true is proved: a plank assigned to `S` is
geometrically comparable with `S`.  The converse is false and is never used. -/
theorem assignedSlabFamily_subset_inSlabFamilyC_of_mem {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (Cset Cang : ℝ≥0) (s' : Finset ι) (V : ι → Plank a b hab hb1)
    (repr : ι → τ) (slabOf : τ → Slab θ hθ1) (S : Slab θ hθ1)
    (hgeo : ∀ i ∈ s', i ∈ inSlabFamilyC Cset Cang s' V (slabOf (repr i))) :
    assignedSlabFamily s' repr slabOf S ⊆ inSlabFamilyC Cset Cang s' V S := fun i hi => by
  obtain ⟨his, hslab⟩ := mem_assignedSlabFamily.mp hi
  rw [← hslab]; exact hgeo i his

end Plank

/-!
## Measurability of the grid half-boxes

`Plank.halfSlabBox` is by definition the carrier of a prism, hence measurable.  This is what lets a
shading be restricted to a half-box, and it is used by the final Item 2 layer to build the
box-local families `Z`.
-/

namespace Plank

/-- The middle half of a shifted grid box is measurable: it is the carrier of a prism (extra69,
`rem:measurableSetHalfSlabBox`). -/
theorem measurableSet_halfSlabBox {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (b : ℝ≥0)
    (sh : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    MeasurableSet (halfSlabBox S b sh k) :=
  PrismNDim.measurableSet_carrier _

end Plank

end

end
