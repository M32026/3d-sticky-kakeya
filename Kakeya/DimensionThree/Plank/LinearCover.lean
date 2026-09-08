/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SaturatedGoodCover
public import Kakeya.DimensionThree.Plank.ShadingAggregation

/-!
# The C-linear cover route for Item 2

The retired good cover reached Item 2 through a Markov selection: the representative
scores were compared with a fixed threshold, a subfamily `𝒯' ⊆ 𝒯` clearing it was retained, and a
single cover fraction was asserted on `𝒯'`.  Returning to the full family then cost the cardinality
retention `f = #𝒯' / #𝒯`, and the quantitative information carried by the individual scores was
discarded.

This file replaces that step.  The observation is that the threshold was never used for anything
except to *name* a value of `κ` — `Plank.boxCount_of_goodBoxScore_saturated_var` makes that visible
by abstracting it — and the score names one by itself:

`κ_Q(u) = M(u) / (c_tan · ab · #rep⁻¹(u) · C_box³)`.

Every representative therefore keeps its own cover fraction, none is discarded, and what replaces
the uniform lower bound is a lower bound on the *average*
(`Plank.sum_coverFraction_ge`).  The aggregate is then closed linearly
(`Plank.sum_ge_of_linear_density`), so the exponent is unchanged at `η_abs + 3η + 3η'` and carries
no term for representative retention.

The geometry is untouched: Steps 1, 3 and 4 of the saturated good cover are reused verbatim, and
`Plank.perRepresentativeDensity_saturated_dilated` already takes `κ` as a parameter, so it is
instantiated per representative with no change to its proof.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

open scoped Classical in
/-- **Step 3 with the cover fraction read off the score itself.**  The instance of
`Plank.boxCount_of_goodBoxScore_saturated_var` at

`κ = M / (c_tan · ab · #F)`,

`M` the fibre-local score.  This is the *definition* of the C-linear route's cover fraction, and the
point is that at this `κ` the hypothesis `hscore` is an identity rather than an assumption: the
normalisation cancels exactly, and `(M.toNNReal : ℝ≥0∞) ≤ M` holds unconditionally.  So no
representative has to clear any threshold, and none is discarded.

A representative carrying no good-box mass gets `κ = 0` and a vacuous conclusion, which is the
degenerate behaviour one wants. -/
theorem boxCount_of_fibreLocalScore {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {hθ1 : θ ≤ 1}
    (cTan : ℝ≥0) (hcTan : 1 ≤ cTan) (S : Slab θ hθ1) (sh : Fin 3 → ℝ)
    (Dg : Finset (Fin 3 → ℤ)) (F : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Tl : (Fin 3 → ℤ) → Finset ι)
    (R : (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3)))
    (Pset : Set (EuclideanSpace ℝ (Fin 3)))
    (ha : 0 < a) (hb : 0 < b) (hFne : F.Nonempty)
    (hTl : ∀ q, Tl q ⊆ F)
    (hR : ∀ q, R q ⊆ ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hshV : ∀ i ∈ F, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (htan : ∀ q, ∀ i ∈ Tl q, Kakeya.ComparableScalars cTan
      (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2)) :
    ((((∑ q ∈ Dg, ∑ i ∈ Tl q, volume ((Y i).shade ∩ R q ∩ Pset)).toNNReal
          / (cTan * (a * b) * (F.card : ℝ≥0)) : ℝ≥0) : ENNReal)) *
        ((8 * θ * b * b : ℝ≥0) : ENNReal)
      ≤ ∑ q ∈ Dg with (((shiftedSlabBox S b sh q).carrier :
            Set (EuclideanSpace ℝ (Fin 3))) ∩ Pset).Nonempty,
          volume ((shiftedSlabBox S b sh q).carrier) := by
  have hd : cTan * (a * b) * (F.card : ℝ≥0) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (zero_lt_one.trans_le hcTan).ne' (mul_pos ha hb).ne')
      (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hFne).ne')
  refine boxCount_of_goodBoxScore_saturated_var cTan _ hcTan S sh Dg F V Y Tl R Pset
    ha hb hFne hTl hR hshV htan ?_
  rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul, mul_assoc _ cTan (a * b), mul_assoc,
    div_mul_cancel₀ _ hd]
  exact ENNReal.coe_toNNReal_le_self

open scoped Classical in
/-- **Steps 3 and 4 for a single representative, with no threshold.**  The per-representative core
of the C-linear route: the boxes of `Dg` meeting the fixed dilation `Pr^{(C_c)}` cover the larger
fixed dilation `Pr^{(C_box)}`, `C_box = 4 C_ang + 8 + C_c`, in the fraction named by the
representative's own score.

This is the `hcover` block of the retired good cover with the Markov threshold removed:
`Plank.boxCount_of_fibreLocalScore` supplies the undilated covering fraction unconditionally, and
`Plank.cover_dilatedPrism_of_boxesMeeting` transports it to the dilation at the fixed price
`C_box^(-3)`.  Nothing here selects or discards a representative, and no power of `a` is spent. -/
theorem coverFraction_dilated_of_goodBoxes {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {hθb : θ * b ≤ b} {hθ1 : θ ≤ 1}
    (cTan Cang Cc : ℝ≥0) (hcTan : 1 ≤ cTan) (hCang : 1 ≤ Cang) (hCc : 1 ≤ Cc)
    (S : Slab θ hθ1) (sh : Fin 3 → ℝ)
    (Dg : Finset (Fin 3 → ℤ)) (F : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Tl : (Fin 3 → ℤ) → Finset ι) (Pr : Prism3D (θ * b) b 1 hθb hb1)
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < θ) (hFne : F.Nonempty)
    (hTl : ∀ q, Tl q ⊆ F)
    (hshV : ∀ i ∈ F, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (htan : ∀ q, ∀ i ∈ Tl q, Kakeya.ComparableScalars cTan
      (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2))
    (hang : Prism3D.angle Pr S ≤ (Cang : ℝ) * (θ : ℝ)) :
    ((((∑ q ∈ Dg, ∑ i ∈ Tl q, volume ((Y i).shade ∩ halfSlabBox S b sh q ∩
            ((Pr.toPrismNDim.dilation Cc).carrier :
              Set (EuclideanSpace ℝ (Fin 3))))).toNNReal
          / (cTan * (a * b) * (F.card : ℝ≥0)) / (4 * Cang + 8 + Cc) ^ 3 : ℝ≥0) : ENNReal)) *
        volume ((Pr.toPrismNDim.dilation (4 * Cang + 8 + Cc)).carrier :
          Set (EuclideanSpace ℝ (Fin 3)))
      ≤ ∑ q ∈ Dg with (((shiftedSlabBox S b sh q).carrier :
            Set (EuclideanSpace ℝ (Fin 3))) ∩
          ((Pr.toPrismNDim.dilation Cc).carrier :
            Set (EuclideanSpace ℝ (Fin 3)))).Nonempty,
          volume ((shiftedSlabBox S b sh q).carrier) := by
  have hvol_eq : volume ((Pr.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      = ((8 * θ * b * b : ℝ≥0) : ENNReal) := by
    rw [Prism3D.volume_carrier Pr]
    push_cast
    ring
  refine (cover_dilatedPrism_of_boxesMeeting S sh _ Pr Cang Cc _ hCang hCc hθ hb hang
    (fun q hq => (Finset.mem_filter.mp hq).2) ?_).2
  rw [hvol_eq]
  exact boxCount_of_fibreLocalScore cTan hcTan S sh Dg F V Y Tl
    (fun q => halfSlabBox S b sh q)
    ((Pr.toPrismNDim.dilation Cc).carrier : Set (EuclideanSpace ℝ (Fin 3)))
    ha hb hFne hTl (halfSlabBox_subset S b sh) hshV htan

open scoped Classical in
/-- **The good cover for saturated local families, with no representative deleted.**  The C-linear
counterpart of the retired Markov-selection cover, and the only good-cover endpoint of the route.

The Markov version answered only for a selected `𝒯' ⊆ 𝒯`, on which a *single* cover fraction
`κ_min a^η` holds; returning to the full family then costs the cardinality retention of `𝒯'`.  Here
Step 2 is not a selection but a division: every representative keeps its own cover fraction, the
same normalisation the Markov step compares against a threshold, and what replaces the uniform
lower bound is a lower bound on the *average* (`Plank.sum_coverFraction_ge`).  Steps 1, 3 and 4 are
unchanged.

The near-constant fibre hypotheses `hlo`/`hup` are the preassembly's `N / cN ≤ #rep⁻¹(u) ≤ cN N`.
They enter for two different reasons — `W` normalises each individual cover fraction, `L` converts
`#s` into `#𝒯` — so the aggregate constant loses `L / W`, i.e. `cN^(-2)`, and **no** power of `a`.
`0 < L` also supplies the fibre nonemptiness that Step 3 needs, uniformly in `u`.

The local box fullness is left uniform: only the covering fraction becomes
representative-dependent. -/
theorem exists_goodCover_saturated_aggregate {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {hθb : θ * b ≤ b} {hθ1 : θ ≤ 1} {σ : Type*}
    (cTan cGood cStb Cang Cc L W : ℝ≥0) (hcTan : 1 ≤ cTan) (_hcGood : 0 < cGood)
    (_hcStb : 0 < cStb)
    (hCang : 1 ≤ Cang) (hCc : 1 ≤ Cc) (hL : 0 < L) (hW : 0 < W)
    (S : Slab θ hθ1) (sh : Fin 3 → ℝ)
    (𝒦 : Finset (Fin 3 → ℤ)) (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (T : (Fin 3 → ℤ) → Finset ι)
    (Z : (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (𝒯 : Finset σ) (Pr : σ → Prism3D (θ * b) b 1 hθb hb1) (rep : ι → σ) (η : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < θ) (_hs : s.Nonempty)
    (hTs : ∀ q, T q ⊆ s) (hmaps : ∀ i ∈ s, rep i ∈ 𝒯)
    (hlo : ∀ u ∈ 𝒯, L ≤ (((s.filter (fun i => rep i = u)).card : ℕ) : ℝ≥0))
    (hup : ∀ u ∈ 𝒯, (((s.filter (fun i => rep i = u)).card : ℕ) : ℝ≥0) ≤ W)
    (hsub : ∀ i ∈ s, (Y i).shade
      ⊆ (((Pr (rep i)).toPrismNDim.dilation Cc).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hshV : ∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hZsh : ∀ q, ∀ i ∈ T q, (Z q i).shade = (Y i).shade ∩ halfSlabBox S b sh q)
    (hZcar : ∀ q, ∀ i ∈ T q, (Z q i).carrier = (V i).carrier)
    (htan : ∀ q, ∀ i ∈ T q, Kakeya.ComparableScalars cTan
      (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2))
    (hangPr : ∀ u ∈ 𝒯, Prism3D.angle (Pr u) S ≤ (Cang : ℝ) * (θ : ℝ))
    (hcap : ((8 * cGood * cStb * a ^ η * (a * b) : ℝ≥0) : ENNReal) * (s.card : ENNReal)
      ≤ ∑ q ∈ 𝒦, ∑ i ∈ T q, volume ((Y i).shade ∩ halfSlabBox S b sh q)) :
    ∃ (D : σ → Finset (Fin 3 → ℤ)) (κQ : σ → ℝ≥0),
      (∀ u ∈ 𝒯, D u ⊆ 𝒦) ∧
      (∀ u ∈ 𝒯, ∀ q ∈ D u,
        ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ (((Pr u).toPrismNDim.dilation (4 * Cang + 8 + Cc)).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ u ∈ 𝒯, ∀ q ∈ D u, b * (cGood * cStb / (128 * cTan) * a ^ η)
        ≤ ShadedBody.fullness (T q) (Z q)) ∧
      (∀ u ∈ 𝒯, (κQ u : ENNReal) *
          volume (((Pr u).toPrismNDim.dilation (4 * Cang + 8 + Cc)).carrier :
            Set (EuclideanSpace ℝ (Fin 3)))
        ≤ ∑ q ∈ D u, volume ((shiftedSlabBox S b sh q).carrier)) ∧
      (4 * cGood * cStb * L / (cTan * W * (4 * Cang + 8 + Cc) ^ 3) * a ^ η) * (𝒯.card : ℝ≥0)
        ≤ ∑ u ∈ 𝒯, κQ u := by
  -- STEP 1
  obtain ⟨Dg, hDg_sub_𝒦, hfull, hhalf⟩ := goodBoxes_saturated_retainedMass cTan cGood cStb hcTan
    S sh 𝒦 s V Y T Z (fun q => halfSlabBox S b sh q) η ha hb hθ hTs hZsh hZcar htan hcap
  let Pc : σ → Set (EuclideanSpace ℝ (Fin 3)) := fun u =>
    (((Pr u).toPrismNDim.dilation Cc).carrier : Set (EuclideanSpace ℝ (Fin 3)))
  -- STEP 2a/2b: the fibre-local score, aggregated and descended to `ℝ≥0`
  let M : σ → ENNReal := fun u =>
    ∑ q ∈ Dg, ∑ i ∈ (T q).filter (fun i => rep i = u),
      volume ((Y i).shade ∩ halfSlabBox S b sh q ∩ Pc u)
  have hagg' := sum_toNNReal_ge_of_aggregate 𝒯 M _ s.card
    (fun u _ => fibreLocalScore_ne_top S sh Dg (fun q => (T q).filter (fun i => rep i = u)) Y
      (fun q => halfSlabBox S b sh q) (Pc u) (halfSlabBox_subset S b sh))
    (hhalf.trans_eq
      (sum_fibreLocalMass_eq 𝒯 Dg s T rep (fun q => halfSlabBox S b sh q) Pc Y hTs hmaps
          hsub).symm)
  -- STEP 2c: the average
  have hfrac := Plank.sum_coverFraction_ge 𝒯 s rep (fun u => (M u).toNNReal) (cTan * (a * b))
    (4 * cGood * cStb * a ^ η * (a * b)) L W
    (mul_pos (zero_lt_one.trans_le hcTan) (mul_pos ha hb)) hL hW hmaps hlo hup hagg'
  -- `D u` : the good boxes meeting the dilated representative; `κQ u` : its own cover fraction
  let D : σ → Finset (Fin 3 → ℤ) := fun u =>
    Dg.filter (fun q => (((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
      (((Pr u).toPrismNDim.dilation Cc).carrier : Set (EuclideanSpace ℝ (Fin 3)))).Nonempty)
  let κQ : σ → ℝ≥0 := fun u =>
    (M u).toNNReal / (cTan * (a * b) * (((s.filter (fun i => rep i = u)).card : ℕ) : ℝ≥0))
      / (4 * Cang + 8 + Cc) ^ 3
  refine ⟨D, κQ, fun _ _ => (Finset.filter_subset _ _).trans hDg_sub_𝒦,
    fun u hu q hq => shiftedSlabBox_subset_dilation_of_meet_dilation S sh q (Pr u) Cang Cc hCang
      hCc hθ hb (hangPr u hu) (Finset.mem_filter.mp hq).2,
    fun _ _ q hq => hfull q (Finset.filter_subset _ _ hq), fun u hu => ?_, ?_⟩
  -- STEP 3+4, one representative at a time
  · exact coverFraction_dilated_of_goodBoxes cTan Cang Cc hcTan hCang hCc S sh Dg
      (s.filter (fun i => rep i = u)) V Y (fun q => (T q).filter (fun i => rep i = u)) (Pr u)
      ha hb hθ
      (Finset.card_pos.mp (by rw [← Nat.cast_pos (α := ℝ≥0)]; exact hL.trans_le (hlo u hu)))
      (fun q => Finset.filter_subset_filter _ (hTs q))
      (fun i hi => hshV i (Finset.mem_filter.mp hi).1)
      (fun q i hi => htan q i (Finset.mem_filter.mp hi).1) (hangPr u hu)
  · refine le_trans (le_of_eq ?_) ((div_le_div_of_nonneg_right hfrac
      (show (0 : ℝ≥0) ≤ (4 * Cang + 8 + Cc) ^ 3 from zero_le)).trans_eq (Finset.sum_div _ _ _))
    rw [show 4 * cGood * cStb * a ^ η * (a * b) * L
          = 4 * cGood * cStb * L * a ^ η * (a * b) from
        (mul_right_comm _ _ _).trans (congrArg (· * (a * b)) (mul_right_comm _ _ _)),
      show cTan * (a * b) * W = cTan * W * (a * b) from mul_right_comm _ _ _,
      mul_div_mul_right _ _ (mul_ne_zero ha.ne' hb.ne'), div_mul_eq_mul_div,
      div_mul_eq_mul_div, div_mul_eq_mul_div, div_div]

/-! ## Item 2 on the full representative family -/

open scoped Classical in
/-- **Item 2 from a saturated good cover, aggregated over every representative.**  The C-linear
counterpart of the retired dilated Markov endpoint, and the only Item 2 endpoint of the route.

The Markov version asked a *uniform* `κ` with `κMin a^η ≤ κ` and reached the fullness termwise,
one representative at a time.  Here each representative supplies only the density its
own cover fraction `κQ u` buys — `Plank.perRepresentativeDensity_saturated_dilated` already takes
`κ` as a parameter, so it is instantiated per representative with **no change to its proof** — and
the fullness is reached from the *summed* mass inequality via `Plank.sum_ge_of_linear_density` and
`Plank.fullness_ge_of_aggregateMass`.

The exponent is unchanged.  The dense-box estimate contributes `a^(2η)`, the box-normalised
fullness `cLam a^η`, and the aggregate cover fraction `a^η`, so the conclusion is again at
`c₂ · a^(4η)` with `c₂ = cDia · cLam² · cKappa`.  No factor for representative retention appears,
because none is created: `𝒯` is the whole family throughout.

The local fullness `lam = cLam a^η` stays uniform; only `κ` became representative-dependent. -/
theorem aggregateShading_of_goodCover (cTan Ceta cLam cKappa : ℝ≥0)
    (hCeta : 0 < Ceta) (hcLam : 0 < cLam) (hcKappa : 0 < cKappa) :
    ∃ c2 : ℝ≥0, 0 < c2 ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθb : θ * b ≤ b} {hθ1 : θ ≤ 1}
        {ι : Type*} {σ : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (S : Slab θ hθ1) (sh : Fin 3 → ℝ)
        (𝒯 : Finset σ) (Pr : σ → Prism3D (θ * b) b 1 hθb hb1) (Cbox : ℝ≥0)
        (Yθ : σ → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (D : σ → Finset (Fin 3 → ℤ))
        (Tq : σ → (Fin 3 → ℤ) → Finset ι)
        (Z : σ → (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (η : ℝ) (κQ : σ → ℝ≥0),
        0 < a → 0 < b → 0 < θ → 0 < η → 0 < Cbox → a / b ≤ θ →
        LocalAngleConcentration V θ 𝒯 D Tq Z Ceta η →
        𝒯.Nonempty →
        (∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ u ∈ 𝒯, ((Yθ u).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = ((Pr u).toPrismNDim.dilation Cbox).carrier) →
        (∀ u ∈ 𝒯, (Yθ u).shade
          = (⋃ i ∈ s, (Y i).shade) ∩
            (((Pr u).toPrismNDim.dilation Cbox).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ u ∈ 𝒯, ∀ q, Tq u q ⊆ s) →
        (∀ u ∈ 𝒯, ∀ q, ∀ i ∈ Tq u q, (Z u q i).shade
          ⊆ (Y i).shade ∩ ((shiftedSlabBox S b sh q).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ u ∈ 𝒯, ∀ q, ∀ i ∈ Tq u q, (Z u q i).carrier = (V i).carrier) →
        (∀ u ∈ 𝒯, ∀ q ∈ D u, ∀ i ∈ Tq u q, Kakeya.ComparableScalars cTan
          (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
            (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2)) →
        (∀ u ∈ 𝒯, ∀ q ∈ D u,
          b * (cLam * a ^ η) ≤ ShadedBody.fullness (Tq u q) (Z u q)) →
        (∀ u ∈ 𝒯, ∀ q ∈ D u,
          ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ⊆ (((Pr u).toPrismNDim.dilation Cbox).carrier :
                Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ u ∈ 𝒯, (κQ u : ENNReal) *
            volume (((Pr u).toPrismNDim.dilation Cbox).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))
          ≤ ∑ q ∈ D u, volume ((shiftedSlabBox S b sh q).carrier)) →
        (cKappa * a ^ η) * (𝒯.card : ℝ≥0) ≤ ∑ u ∈ 𝒯, κQ u →
        c2 * a ^ (4 * η) ≤ ShadedBody.fullness 𝒯 Yθ := by
  obtain ⟨cDia, hcDia, hmain⟩ := perRepresentativeDensity_saturated_dilated cTan Ceta hCeta
  refine ⟨cDia * cLam ^ 2 * cKappa, mul_pos (mul_pos hcDia (pow_pos hcLam 2)) hcKappa, ?_⟩
  intro a b θ hab hb1 hθb hθ1 ι σ s V Y S sh 𝒯 Pr Cbox Yθ D Tq Z η κQ ha hb hθ hη hCbox habθ
      hLC hne
    hsh hcar hshade hTsub hZsh hZcar htan hlam hbox hcov hagg
  obtain ⟨θ0, Cstar, Mtyp, hprod, hband⟩ := hLC
  -- Every dilated representative carries the same nonzero volume
  have hvolt : ∀ u ∈ 𝒯, volume (Yθ u).carrier
      = ((8 * Cbox ^ 3 * (θ * b) * b : ℝ≥0) : ENNReal) := fun u hu => by
    rw [hcar u hu, volume_dilation (Pr u).toPrismNDim Cbox, Prism3D.volume_carrier (Pr u)]
    push_cast
    ring
  have hvne : (8 * Cbox ^ 3 * (θ * b) * b : ℝ≥0) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hCbox.ne'))
      (mul_pos hθ hb).ne') hb.ne'
  have hsum : ∑ u ∈ 𝒯, volume (Yθ u).carrier
      = (𝒯.card : ENNReal) * ((8 * Cbox ^ 3 * (θ * b) * b : ℝ≥0) : ENNReal) := by
    rw [Finset.sum_congr rfl hvolt, Finset.sum_const, nsmul_eq_mul]
  refine fullness_ge_of_aggregateMass 𝒯 Yθ _ ?_ ?_ ?_
  · rw [hsum]
    exact pos_iff_ne_zero.mpr (mul_ne_zero (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hne).ne')
      (ENNReal.coe_ne_zero.mpr hvne))
  · rw [hsum]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top
  -- Each representative supplies the density its own `κQ u` buys; the average closes the aggregate
  · have hlin := sum_ge_of_linear_density 𝒯 Yθ κQ a (cDia * cLam * cLam) cKappa (3 * η) η
      ((8 * Cbox ^ 3 * (θ * b) * b : ℝ≥0) : ENNReal) ha hvolt
      (by rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul, ← ENNReal.ofNNReal_finsetSum]
          exact ENNReal.coe_le_coe.mpr hagg)
      (fun u hu => by
        rw [hcar u hu, hshade u hu, show (cDia * cLam * cLam * a ^ (3 * η) * κQ u : ℝ≥0)
            = cDia * cLam * a ^ (2 * η) * (cLam * a ^ η) * κQ u from by
          rw [show 3 * η = 2 * η + η from by ring, NNReal.rpow_add ha.ne']; ring]
        exact hmain s V Y S sh (Pr u) Cbox (D u) (Tq u) (Z u) η (θ0 u) Mtyp Cstar cLam
          (cLam * a ^ η) (κQ u) ha hb hθ hη hcLam habθ
          (fun q hq => (hband u hu q hq).1) (fun q hq => (hband u hu q hq).2.1)
          (fun q hq => (hband u hu q hq).2.2.1)
          hprod le_rfl (hTsub u hu) hsh (hZsh u hu) (hZcar u hu) (htan u hu) (hlam u hu)
          (fun q hq => (hband u hu q hq).2.2.2) (hbox u hu) (hcov u hu))
    rwa [show 3 * η + η = 4 * η from by ring,
      show cDia * cLam * cLam * cKappa = cDia * cLam ^ 2 * cKappa from by ring] at hlin

end Plank

end

end
