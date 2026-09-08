/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.Collapse

/-!
# Main Lemma 1, Case (ii): reduction to the `b`-tubes — the fine factor over a `2`-dilate

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

section ReduceToTb

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! #### The fine factor over a dilate of a parent tube

What the plank-in-tube chain supplies is not `T i ⊆ T_b` but `T i ⊆ c · T_b`, together with a
Frostman bound taken *in* the dilate (`Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow`).  This
block restates the fine factor under that weaker containment, on top of the dilate
normalization `Kakeya.ml1Boot.exists_fineNormalization_dilate` of
`Kakeya/DimensionThree/MainLemma1/Cases.lean`.  The dilation ratio `c` is free throughout, and
is carried as an `NNReal` because it is read both as the real ratio of `Kakeya.Tube.dilate` and
inside the `NNReal`-valued constant `Kakeya.ml1Boot.fineNormalizeDilate.C`.
`Kakeya.ml1Boot.reduceToTb_fine_bound` is **not** superseded: it remains correct and the dilate
form is a separate declaration. -/

/-- **The constant `C_{lem:ml1bootReduceToTbFineBoundDilate}(c, C_F)`** (blueprint
`def:ml1bootReduceToTbFineBoundDilateConstant`), at dilation ratio `c` and Frostman budget
constant `C_F`.

Writing `C₃(c) = Kakeya.ml1Boot.fineNormalizeDilate.C c`, this is `4 C₃(c)² (2 C_F)`: the
prefactor `4 C₂² (2 C_T)` of `Kakeya.ml1Boot.reduceToTb_fine_bound` with
`C₂ = Kakeya.ml1Boot.fineFactor.C` replaced by `C₃(c)` and
`C_T = Kakeya.ml1Boot.densityTransfer.C` replaced by the parameter `C_F`.  The factor `4` is the
`Λ²` of `Kakeya.ml1Boot.fine_genKF_dilate` at `Λ = 2`, one power of `C₃(c)` comes from that
lemma's prefactor and one from the Frostman constant fed into it, and `2 C_F` is the Frostman
budget the caller's hypothesis (a) is read at.

`C_F` is a **parameter** and not `C_T`, because the Frostman bound this chain consumes is
whatever a caller can produce.  The density-transfer route
`Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow` produces it at `C_T`, i.e. at `C_F = C_T`, which
is the previous statement verbatim; the hull route
`Kakeya.ml1Boot.frostmanConstIn_fibre_convexHull_le` produces it at the larger
`Kakeya.ml1Boot.fibreMassShare.C`, which no declaration below that module can name, and the
parameter is how the wider constant is carried without an import cycle.  The constant is
**spent** here, on a conclusion side, so the widening is a loosening of this bound and is paid
in the caller's loss budget rather than in its Frostman budget.

It depends only on the ambient dimension `3`, on the ratio `c` and on `C_F`; in particular not
on `δ̃`, `ap`, `bp`, `ρ`, `γ`, `j`, or the family. -/
noncomputable abbrev reduceToTbFineBoundDilate.C (c CF : NNReal) : NNReal :=
  4 * fineNormalizeDilate.C c ^ 2 * (2 * CF)

/-- **The fine factor over the `c`-dilate of a parent tube** (blueprint
`lem:ml1bootReduceToTbFineBoundDilate`).

`Kakeya.ml1Boot.reduceToTb_fine_bound` with the containment of the fine tubes and the ambient
body of the Frostman hypothesis both moved to a named body `K ⊆ c · T_b`, and with
`Kakeya.ml1Boot.fineNormalizeDilate.C c` in place of `Kakeya.ml1Boot.fineFactor.C`.  The
conclusion is at the scale `b` and not `c b`, and only the prefactor changes, to
`Kakeya.ml1Boot.reduceToTbFineBoundDilate.C c CF`.

## The Frostman budget constant `C_F` is a parameter

Hypothesis (a) is read at `2 C_F δ̃ ^ (-2 ap')` for a caller-supplied `C_F ≥ 1`, and the same
`C_F` leaves in the conclusion's prefactor through
`Kakeya.ml1Boot.reduceToTbFineBoundDilate.C c CF`.  `C_F = C_T` is the previous statement
verbatim.  Only `1 ≤ C_F` is used, in the step `C_f ^ (1 - γ/2) ≤ C_f`, and no upper bound on
`C_F` is used anywhere: the constant occurs once on the hypothesis side, where enlarging it
weakens the assumption, and once on the conclusion side, where enlarging it weakens the
conclusion.  So the lemma is monotone in `C_F` in the caller's favour on the hypothesis and
against the caller on the conclusion, and the two motions are the same widening.

`C_F` is bound *inside* the `∀ᶠ δ̃`, beside `M`, so that one `δ̃`-threshold serves every `C_F`.
That is sound because nothing choosing the threshold sees `C_F`: `ηflat` comes from
`Kakeya.ml1Boot.fine_genKF_dilate`, which does not mention it.

## The ambient body is a parameter, and the volume ratio `M` is the price

`K` is carried straight to `Kakeya.ml1Boot.fine_genKF_dilate` and thence to the normalization
leaf; `K = c · T_b` with `M = 1` is the previous statement.  The point of naming it is that a
caller whose fine tubes sit in something smaller than the dilate — the convex hull of a plank
block, say — owes its Frostman bound only in that smaller body, which is the weaker obligation.
The conclusion still does not mention `K`: the `(δ̃ / b)` bracket is read at the *parent scale*
`b`, not at the ambient.

It does, however, mention `M`.  Naming the ambient is **not** free at the same constant, and an
earlier version of this lemma which claimed it was is refuted; the counterexample is recorded
at `Kakeya.ml1Boot.exists_fineNormalization_dilate`.  A Frostman constant divides by the volume
of its ambient body, so passing from a bound read in `K` to a conclusion read in `B₁` costs the
volume ratio `|c · T_b| / |K|`, and no order relation between `K` and the dilate bounds that
ratio: shrinking `K` towards a single fine tube sends it to infinity like `δ̃^(-2)`.  The
hypothesis `|c · T_b| ≤ M |K|` names the ratio, and the price appears as the factor `M` in the
loss prefactor of the conclusion.

Where the price lands is the whole point of putting it here rather than making the caller
bridge back to the dilate with `ConvexSpaceBody.frostmanConstIn_ambient_mono`.  Hypothesis (a)
does not see `M`: it is `2 C_F δ̃ ^ (-2 ap')` read at `K`, and the `M` shows up multiplying
`Kakeya.ml1Boot.reduceToTbFineBoundDilate.C c CF`, i.e. in the `δ̃ ^ (-3 ap')` loss budget rather
than in the Frostman budget.  The bridge would instead have charged the same ratio inside (a),
where the caller's own hull-Frostman bound has already spent the available room.

`1 ≤ M` is asked so that `Kakeya.ml1Boot.fine_genKF_dilate` may divide by `M C₃(c)`.  It costs
nothing: `K ≤ c · T_b` forces it whenever `|K|` is positive and finite.

The dilation ratio is free.  It is the ratio of the ambient body throughout and the ratio at
which the normalization loss of `Kakeya.ml1Boot.fine_genKF_dilate` is read; nothing in the
proof constrains it.  `M` is likewise free and is not tied to `c`.

The hypothesis on the parent is the *same* `T_b ⊆ B₁` as there: only the containment of the
fine tubes and the ambient body of (a) move to the dilate.  Asking `c · T_b ⊆ B₁` instead would
make the lemma vacuous for `c > 1` (blueprint `note:ml1bootDilateInBallObligation`).

This is one citation of `Kakeya.ml1Boot.fine_genKF_dilate` at `Λ = 2`, `μ₀ = λ_σ`, loss
exponent `ap'` and the `δ̃`-dependent Frostman constant `Cf = 2 C_F M C₃(c) δ̃ ^ (-2 ap')`, plus
the arithmetic step `Cf ^ (1 - γ/2) ≤ Cf`.  The `M` inside `Cf` is exactly the `M` that leaves
in the conclusion's prefactor. -/
theorem reduceToTb_fine_bound_dilate [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    (c : NNReal) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hKF : FrostmanEstimate.{u} E γ) :
    ∀ ap' > (0 : ℝ), ∃ ηflat > (0 : ℝ),
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ b : NNReal, δt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} {u : Finset ι} (Tb : Tube b E) (T : ι → ShadedTube δt E)
        (K : ConvexSpaceBody E) (M CF : NNReal)
        {lamσ : ENNReal} {R : ℝ}, 1 ≤ M → 1 ≤ CF → 0 < lamσ →
        u.Nonempty →
        Tb.carrier ⊆ Metric.closedBall 0 R →
        K ≤ Tube.dilate Tb (c : ℝ) →
        volume (Tube.dilate Tb (c : ℝ)).carrier ≤ (M : ENNReal) * volume K.carrier →
        (∀ i ∈ u, (T i).toConvexSpaceBody ≤ K) →
        (u : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (∀ i ∈ u, lamσ * volume (T i).carrier ≤ volume (T i).shade ∧
          volume (T i).shade ≤ 2 * lamσ * volume (T i).carrier) →
        -- (a)
        frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K
          ≤ 2 * (CF : ENNReal) * (δt : ENNReal) ^ (-2 * ap') →
        -- (b)
        4 * (fineNormalizeDilate.C c : ENNReal) * (δt : ENNReal) ^ ηflat
          ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal) →
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (M : ENNReal) * (reduceToTbFineBoundDilate.C c CF : ENNReal)
            * (δt : ENNReal) ^ (-3 * ap')
            * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
            * ((u.card : ENNReal) * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  intro ap' hap'
  obtain ⟨ηflat, hηflat, h_genKF⟩ := fine_genKF_dilate hdim c hγ0 hγ1 hKF ap' hap'
  refine ⟨ηflat, hηflat, ?_⟩
  let C : ENNReal := (fineNormalizeDilate.C c : ENNReal)
  have hC1 : 1 ≤ C := by
    have hCnn : 1 ≤ fineNormalizeDilate.C c := one_le_fineNormalizeDilate_C c
    change (1 : ENNReal) ≤ (fineNormalizeDilate.C c : ENNReal)
    exact_mod_cast hCnn
  have hC0 : C ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt
      (lt_of_lt_of_le zero_lt_one (one_le_fineNormalizeDilate_C c)))
  have hCtop : C ≠ ⊤ := by exact ENNReal.coe_ne_top
  filter_upwards [h_genKF 2 (by norm_num : (1 : NNReal) ≤ 2), self_mem_nhdsWithin] with δt
    hδt_aux hδt_pos
  intro b hδtb hb1 ι u Tb T K M CF lamσ R hM hCF hlamσ hu hTb hKle hKfat hsubK hED hdens hFa hFull
  have hCF1 : 1 ≤ (CF : ENNReal) := by exact_mod_cast hCF
  have hCFtop : (CF : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδt0 : 0 < δt := hδt_pos
  have hδt1 : δt ≤ 1 := le_trans hδtb hb1
  have hδtle : (δt : ENNReal) ≤ 1 := by exact_mod_cast hδt1
  have hδtpos : 0 < (δt : ENNReal) := ENNReal.coe_pos.mpr hδt0
  have hδtne : (δt : ENNReal) ≠ 0 := ne_of_gt hδtpos
  have hδttop : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hME : (1 : ENNReal) ≤ (M : ENNReal) := by exact_mod_cast hM
  have hM0 : (M : ENNReal) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hME)
  have hMtop : (M : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hMC1 : (1 : ENNReal) ≤ (M : ENNReal) * C := one_le_mul hME hC1
  have hMC0 : (M : ENNReal) * C ≠ 0 := mul_ne_zero hM0 hC0
  have hMCtop : (M : ENNReal) * C ≠ ⊤ := ENNReal.mul_ne_top hMtop hCtop
  let Cf : ENNReal :=
    2 * (CF : ENNReal) * (δt : ENNReal) ^ (-2 * ap') * ((M : ENNReal) * C)
  have hpow1 : (1 : ENNReal) ≤ (δt : ENNReal) ^ (-2 * ap') := by
    have hneg : -2 * ap' < 0 := by nlinarith [hap']
    exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg hδtpos hδtle hneg
  have hCf1 : 1 ≤ Cf := by
    dsimp [Cf]
    exact one_le_mul (one_le_mul (one_le_mul (by norm_num : (1 : ENNReal) ≤ 2) hCF1) hpow1) hMC1
  have hCftop : Cf ≠ ⊤ := by
    dsimp [Cf]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hCFtop)
        (ENNReal.rpow_ne_top_of_ne_zero hδtne hδttop)) hMCtop
  have hCf_div : Cf / ((M : ENNReal) * C)
      = 2 * (CF : ENNReal) * (δt : ENNReal) ^ (-2 * ap') := by
    dsimp [Cf]
    rw [ENNReal.mul_div_cancel_right hMC0 hMCtop]
  have hdens' : ∀ i ∈ u,
      (2 : ENNReal)⁻¹ * lamσ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ (2 : ENNReal) * lamσ * volume (T i).carrier := by
    intro i hi
    have hdens_i := hdens i hi
    have hinv : (2 : ENNReal)⁻¹ * lamσ ≤ lamσ := by
      calc
        (2 : ENNReal)⁻¹ * lamσ ≤ 1 * lamσ := by
          exact mul_le_mul_of_nonneg_right
            (by norm_num : (2 : ENNReal)⁻¹ ≤ (1 : ENNReal)) (by positivity)
        _ = lamσ := by simp
    constructor
    · calc
        (2 : ENNReal)⁻¹ * lamσ * volume (T i).carrier
            ≤ lamσ * volume (T i).carrier := by
              exact mul_le_mul_of_nonneg_right hinv (by positivity)
        _ ≤ volume (T i).shade := hdens_i.1
    · exact hdens_i.2
  have hFa' : frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K
      ≤ Cf / ((M : ENNReal) * C) := by
    rw [hCf_div]
    exact hFa
  have hFull' : C * (2 : ENNReal) ^ 2 * (δt : ENNReal) ^ ηflat
      ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal) := by
    calc
      C * (2 : ENNReal) ^ 2 * (δt : ENNReal) ^ ηflat = 4 * C * (δt : ENNReal) ^ ηflat := by
        ring
      _ ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal) := hFull
  have hmult : ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
      ≤ C * (2 : ENNReal) ^ 2 * (δt : ENNReal) ^ (-ap')
        * Cf ^ (1 - γ / 2)
        * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
        * ((u.card : ENNReal) * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    exact hδt_aux Cf hCf1 hCftop b hδtb hb1 (ι := ι) (u := u) Tb T K M (μ₀ := lamσ) hM
      ⟨hlamσ, hu, hTb, hKle, hKfat, hsubK, hED, hdens', hFull'⟩ hFa'
  have hpos : 0 ≤ (1 - γ / 2 : ℝ) := by nlinarith [hγ1]
  have hCfmono : Cf ^ (1 - γ / 2) ≤ Cf := by
    calc
      Cf ^ (1 - γ / 2) ≤ Cf ^ (1 : ℝ) := by
        exact ENNReal.rpow_le_rpow_of_exponent_le hCf1 (by nlinarith [hγ0])
      _ = Cf := by rw [ENNReal.rpow_one]
  have hrpow_add : (δt : ENNReal) ^ (-3 * ap')
      = (δt : ENNReal) ^ (-ap') * (δt : ENNReal) ^ (-2 * ap') := by
    calc
      (δt : ENNReal) ^ (-3 * ap') = (δt : ENNReal) ^ (-ap' + -2 * ap') := by
        congr 1
        ring
      _ = (δt : ENNReal) ^ (-ap') * (δt : ENNReal) ^ (-2 * ap') :=
            (ENNReal.rpow_add (x := (δt : ENNReal)) (-ap') (-2 * ap') hδtne hδttop)
  have hreduce : (reduceToTbFineBoundDilate.C c CF : ENNReal)
      = 4 * C ^ 2 * (2 * (CF : ENNReal)) := by
    change (4 * fineNormalizeDilate.C c ^ 2 * (2 * CF) : ENNReal)
        = 4 * C ^ 2 * (2 * (CF : ENNReal))
    dsimp [C]
  have hpref_equal : C * (2 : ENNReal) ^ 2 * (δt : ENNReal) ^ (-ap')
      * (2 * (CF : ENNReal) * (δt : ENNReal) ^ (-2 * ap') * ((M : ENNReal) * C))
      = (M : ENNReal) * (reduceToTbFineBoundDilate.C c CF : ENNReal)
        * (δt : ENNReal) ^ (-3 * ap') := by
    rw [hrpow_add]
    rw [hreduce]
    ring
  calc
    ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
        ≤ C * (2 : ENNReal) ^ 2 * (δt : ENNReal) ^ (-ap') * Cf ^ (1 - γ / 2)
          * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := hmult
    _ ≤ C * (2 : ENNReal) ^ 2 * (δt : ENNReal) ^ (-ap') * Cf
          * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          gcongr
    _ = (M : ENNReal) * (reduceToTbFineBoundDilate.C c CF : ENNReal)
          * (δt : ENNReal) ^ (-3 * ap')
          * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          dsimp only [Cf]
          rw [hpref_equal]

/-- **The fine-factor input package over a dilate** (blueprint
`lem:ml1bootReduceToTbFineInput`, hypotheses (i)–(iii)).

`(𝕋̃|_{u'}, Ỹ')` is the refined fine family and `l₀` a parent index; the fields are items (a),
(c) and (d) of `Kakeya.ml1Boot.IsFactorOneScaleDilate` read at that single index, which is
exactly what `Kakeya.ml1Boot.exists_factorOneScaleUniform_dilate` returns.

Throughout, `𝕋̃[T̃_{b,l₀}]` means the **parent-map** fibre `Kakeya.ml1Boot.fibre _ p_b l₀`, and
never the containment fibre `𝕋̃[K] = (T̃ i)_{T̃ i ⊆ K}` that the density-transfer chain of
`Kakeya.ml1Boot.maxDensity_fibre_le_density_dilate` writes with the same bracket.  One reading
is fixed here and used in every field.

Neither the parent family nor the scale `b` occurs: the package is pure bookkeeping about the
fibre, which is why the parent tube is not a parameter. -/
structure IsFineInputDilate {ι κ : Type*} [DecidableEq κ] {δt : NNReal} (ap' : ℝ)
    (u : Finset ι) (T : ι → ShadedTube δt E) (p : ι → κ)
    (u' : Finset ι) (T' : ι → ShadedTube δt E) (lamσ : ENNReal) (l₀ : κ) : Prop where
  /-- The refined index set is a subset of the given one. -/
  subset : u' ⊆ u
  /-- `Ỹ'` shades the same tubes as `𝕋̃`. -/
  tube_eq : ∀ i ∈ u', (T' i).toTube = (T i).toTube
  /-- (i) The fibre over `l₀` survives the refinement. -/
  fibre_nonempty : (fibre u' p l₀).Nonempty
  /-- (i) Its tubes are pairwise essentially distinct. -/
  fibre_essDistinct : ((fibre u' p l₀ : Finset ι) : Set ι).Pairwise
    (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
  /-- (ii) The refined shading densities are two-sidedly comparable to `λ_σ`. -/
  dens : ∀ i ∈ u', lamσ * volume (T i).carrier ≤ volume (T' i).shade ∧
    volume (T' i).shade ≤ 2 * lamσ * volume (T i).carrier
  /-- (ii) `λ_σ ≥ δ̃ ^ ap' λ(𝕋̃, Ỹ)`. -/
  lamσ_ge : (δt : ENNReal) ^ ap'
      * (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal) ≤ lamσ
  /-- (iii) The fibre Frostman constant grows by at most `δ̃ ^ (-ap')` under the refinement,
  in *every* convex body containing the whole fibre. -/
  frostman_refine : ∀ K : ConvexSpaceBody E,
    (∀ i ∈ u, p i = l₀ → (T i).toConvexSpaceBody ≤ K) →
    frostmanConstIn (fibre u' p l₀) (fun i => (T i).toConvexSpaceBody) K
      ≤ (δt : ENNReal) ^ (-ap')
        * frostmanConstIn (fibre u p l₀) (fun i => (T i).toConvexSpaceBody) K

/-- **The fine-factor input package discharges the hypotheses of
`Kakeya.ml1Boot.reduceToTb_fine_bound_dilate`** (blueprint `lem:ml1bootReduceToTbFineInput`).

Two citations.  The Frostman half applies `Kakeya.ml1Boot.IsFineInputDilate.frostman_refine` at
the ambient body `K`, which the hypothesis `hKfib` asks to contain the whole fibre.
The fullness half applies `Kakeya.ml1Boot.fine_fullness_threshold` at the constant
`Kakeya.ml1Boot.fineNormalizeDilate.C c`, and is where `a + 2 ap' ≤ ηflat` is spent.

## The ambient body is a parameter, and no parent family is needed

The body in which the Frostman constant is read is a bound variable `K`, not the literal
`Kakeya.Tube.dilate (Tb l₀) c`, and the only thing asked of it is that it contain the fibre.
That containment used to be *derived*, from `Kakeya.ml1Boot.IsParentFamilyDilate.le_parent_dilate`
at the dilate; it was the only use of the parent family here, so with the body named the parent
hypothesis, the parent tubes and the parent index set have all left the statement.  Reading the
seam at a smaller body — the convex hull of a plank block rather than a `b`-tube — is therefore
free on this lemma, which is the point: by
`Kakeya.ml1Boot.frostmanConstIn_le_of_le_ambient` the bound at the smaller body is the weaker
hypothesis and cannot be recovered from the bound at the dilate after the fact.

## The dilation ratio is free

Nothing here is special to `c = 2`, and with the body named, the ratio has no geometry left to
enter: the lemma reads the Frostman hypothesis and returns the Frostman conclusion in the
*same* body `K`, and no volume comparison and no covering count of this lemma sees `c` at all.
The constant does: `Kakeya.ml1Boot.fineNormalizeDilate.C c` occurs in `habsorb` and in the
fullness conclusion, but only as an opaque `C ≥ 1` handed to
`Kakeya.ml1Boot.fine_fullness_threshold`, so the ratio is still unconstrained.

The ratio is an `NNReal` rather than a bare real, and elsewhere on the chain the geometry is
read at its coercion `(c : ℝ)`.  That is forced by the constant, whose radius argument is an
`NNReal`; it costs nothing here, since the only caller,
`Kakeya.ml1Boot.reduceToTb_fine_factor_dilate`, is itself `NNReal`-parametrized, and it buys
`1 ≤ 1 + 2 c` for free, so `Kakeya.ml1Boot.one_le_fineNormalizeDilate_C` needs no side
hypothesis.  The fine *bound* over a dilate,
`Kakeya.ml1Boot.reduceToTb_fine_bound_dilate`, is now free in the same ratio: the seam at
`Kakeya.ml1Boot.fine_genKF_dilate` and `Kakeya.ml1Boot.exists_fineNormalization_dilate`, which
used to pin it at `2`, no longer does.  The ratio is pinned first at
`Kakeya.ml1Boot.normalized_le_of_coarse_dilate`, and there because of the *coarse* seam
`Kakeya.ml1Boot.exists_factorOneScaleUniform_dilate`, not this one.

The displayed Frostman assumption is of the shape
`Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow` supplies, but that bounds the Frostman constant
of the *containment* fibre, of which the parent-map fibre is only a subfamily; the passage costs
an index-set factor and is the caller's obligation, not this lemma's.

## The Frostman budget constant is a parameter

The constant the two Frostman bounds are read at is a parameter `CF`, appearing on the
hypothesis side at `2 CF δ̃ ^ (-ap')` and on the conclusion side at `2 CF δ̃ ^ (-2 ap')`.  Only
one power of `δ̃` is bought here, by
`Kakeya.ml1Boot.IsFineInputDilate.frostman_refine`, and the constant is carried through
untouched, which is why no hypothesis on `CF` is needed at all — not even `1 ≤ CF`.  `CF = C_T`
is the previous statement verbatim; the point of the parameter is that a caller whose producer
is the hull route `Kakeya.ml1Boot.frostmanConstIn_fibre_convexHull_le` holds its bound at
`Kakeya.ml1Boot.fibreMassShare.C`, which is above this module in the import order and cannot be
named here. -/
theorem reduceToTb_fine_input [Nontrivial E]
    {δt : NNReal} (hδt0 : 0 < δt) (hδt1 : δt ≤ 1)
    {a ap' ηflat : ℝ} (ha : 0 ≤ a) (hap' : 0 < ap') (hηflat : a + 2 * ap' ≤ ηflat)
    (c CF : NNReal)
    (habsorb : 4 * (fineNormalizeDilate.C c : ENNReal) * (δt : ENNReal) ^ ap' ≤ 1)
    {ι κ : Type*} [DecidableEq κ] {u u' : Finset ι}
    {T T' : ι → ShadedTube δt E} {pb : ι → κ}
    {lamσ : ENNReal} {l₀ : κ} (K : ConvexSpaceBody E)
    (hfull : (δt : ENNReal) ^ a
      ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal))
    (hKfib : ∀ i ∈ u, pb i = l₀ → (T i).toConvexSpaceBody ≤ K)
    (hFrostman : frostmanConstIn (fibre u pb l₀) (fun i => (T i).toConvexSpaceBody) K
      ≤ 2 * (CF : ENNReal) * (δt : ENNReal) ^ (-ap'))
    (hinput : IsFineInputDilate ap' u T pb u' T' lamσ l₀) :
    frostmanConstIn (fibre u' pb l₀) (fun i => (T i).toConvexSpaceBody) K
      ≤ 2 * (CF : ENNReal) * (δt : ENNReal) ^ (-2 * ap') ∧
    4 * (fineNormalizeDilate.C c : ENNReal) * (δt : ENNReal) ^ ηflat
      ≤ (ShadedBody.fullness (fibre u' pb l₀) (fun i => (T' i).toShadedBody) : ENNReal) := by
  have hFrostman' :
      frostmanConstIn (fibre u' pb l₀) (fun i => (T i).toConvexSpaceBody) K
        ≤ 2 * (CF : ENNReal) * (δt : ENNReal) ^ (-2 * ap') := by
    have hδne : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδt0)
    have hδtop : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hpow : (δt : ENNReal) ^ (-ap') * (δt : ENNReal) ^ (-ap')
        = (δt : ENNReal) ^ (-2 * ap') := by
      rw [← ENNReal.rpow_add (-ap') (-ap') hδne hδtop]
      congr 1
      ring
    calc
      frostmanConstIn (fibre u' pb l₀) (fun i => (T i).toConvexSpaceBody) K
          ≤ (δt : ENNReal) ^ (-ap') *
              frostmanConstIn (fibre u pb l₀) (fun i => (T i).toConvexSpaceBody) K := by
            exact hinput.frostman_refine K hKfib
      _ ≤ (δt : ENNReal) ^ (-ap') * (2 * (CF : ENNReal)
            * (δt : ENNReal) ^ (-ap')) := by
            exact mul_le_mul_right hFrostman ((δt : ENNReal) ^ (-ap'))
      _ = 2 * (CF : ENNReal) * ((δt : ENNReal) ^ (-ap')
            * (δt : ENNReal) ^ (-ap')) := by
            ring
      _ = 2 * (CF : ENNReal) * (δt : ENNReal) ^ (-2 * ap') := by
            rw [hpow]
  have hC3 : (1 : NNReal) ≤ fineNormalizeDilate.C c := by
    exact one_le_fineNormalizeDilate_C c
  have hpos' : ∀ i ∈ u', 0 < volume ((T' i).toShadedBody).carrier := by
    intro i hi'
    simpa using (Tube.volume_pos_and_lt_top (σ := δt) hδt0 hδt1 ((T' i).toTube)).1
  have hfin' : ∀ i ∈ u', volume ((T' i).toShadedBody).carrier ≠ ⊤ := by
    intro i hi'
    exact (Tube.volume_pos_and_lt_top (σ := δt) hδt0 hδt1 ((T' i).toTube)).2.ne
  have hterm' : ∀ i ∈ u',
      lamσ * volume ((T' i).toShadedBody).carrier
        ≤ volume ((T' i).toShadedBody).shade := by
    intro i hi'
    have ht : (T' i).toTube = (T i).toTube := hinput.tube_eq i hi'
    have hcar : volume ((T' i).toShadedBody).carrier = volume (T i).carrier := by
      simpa using congrArg (fun T : Tube δt E => volume T.carrier) ht
    simpa [hcar] using (hinput.dens i hi').1
  have hfull' :
      4 * (fineNormalizeDilate.C c : ENNReal) * (δt : ENNReal) ^ ηflat
        ≤ (ShadedBody.fullness (fibre u' pb l₀) (fun i => (T' i).toShadedBody) : ENNReal) := by
    exact fine_fullness_threshold (δt := δt) hδt0 hδt1
      (C := fineNormalizeDilate.C c) (_hC := hC3)
      (a := a) (ap' := ap') (ηf := ηflat) ha hap' hηflat
      (habsorb := habsorb)
      (lam := (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal))
      (lamσ := lamσ) hfull hinput.lamσ_ge
      (s' := u') (Z := fun i => (T' i).toShadedBody) hpos' hfin' hterm'
      (S := fibre u' pb l₀) (by intro i hi; exact (Finset.mem_filter.mp hi).1)
      hinput.fibre_nonempty
  exact ⟨hFrostman', hfull'⟩

/-- **The fine factor over a dilate, packaged for the assembly** (blueprint
`lem:ml1bootReduceToTbFineFactorDilate`).

The composite of `Kakeya.ml1Boot.reduceToTb_fine_input` and
`Kakeya.ml1Boot.reduceToTb_fine_bound_dilate`.  It exists so that
`Kakeya.ml1Boot.normalized_le_of_coarse` spends one citation on the fine factor rather than
two, with one smallness threshold rather than two: the condition `4 C₃(c) δ̃ ^ ap' ≤ 1` of the
first is absorbed into the `∀ᶠ δ̃`.

The dilation ratio `c` is free, both halves being free in it.  Enlarging `c` enlarges
`Kakeya.ml1Boot.fineNormalizeDilate.C c` and hence tightens that smallness condition, but the
condition is discharged eventually in `δ̃` for every fixed `c`, so nothing is owed to a caller
on its account.

## The ambient body is a parameter, and `M` is what naming it costs

The Frostman hypothesis and the containment of the fibre are read at a named body `K`, of
which two things are asked: `K ≤ c · T̃_{b,l₀}` and the volume comparison
`|c · T̃_{b,l₀}| ≤ M |K|`.  `K = c · T̃_{b,l₀}` with `M = 1` is the previous statement.  The
body is threaded unchanged through both halves — `Kakeya.ml1Boot.reduceToTb_fine_input` does
not see the parent at all any more, and `Kakeya.ml1Boot.reduceToTb_fine_bound_dilate` carries
`K` and `M` down to the normalization leaf — so a caller may name a plank block's convex hull
here and owe its Frostman bound only in that hull, paying the hull's volume deficit `M` in the
loss prefactor instead.  The parent tube itself is still needed, for `T̃_{b,l₀} ⊆ B₁` and for
the `(δ̃ / b)` bracket of the conclusion; the parent *family* is not, and has left the
statement.

The volume clause is not decoration.  Without it the underlying normalization leaf is false —
see the counterexample recorded at `Kakeya.ml1Boot.exists_fineNormalization_dilate` — because a
Frostman constant divides by its ambient's volume and an order bound on `K` says nothing about
that volume.  `M` therefore appears in the conclusion, multiplying
`Kakeya.ml1Boot.reduceToTbFineBoundDilate.C c CF`.  `Kakeya.ml1Boot.reduceToTb_fine_input` is
untouched by the volume clause: it neither reads nor returns a volume, and its `habsorb`
threshold is still at the `M`-free `Kakeya.ml1Boot.fineNormalizeDilate.C c`.

## The Frostman budget constant `C_F` is a parameter

The Frostman hypothesis is read at `2 C_F δ̃ ^ (-ap')` for a caller-supplied `C_F ≥ 1`, and the
same `C_F` leaves in the conclusion's prefactor through
`Kakeya.ml1Boot.reduceToTbFineBoundDilate.C c CF`; both halves are free in it.  `C_F = C_T` is
the previous statement verbatim.  Only `1 ≤ C_F` is used and only inside
`Kakeya.ml1Boot.reduceToTb_fine_bound_dilate`; no upper bound on `C_F` is used anywhere on the
chain.  Like `M`, `C_F` is bound *inside* the `∀ᶠ δ̃`, so a caller that holds it only inside its
own `∀ᶠ` — which is where the hull producer's constant becomes available — can still supply it.
Nothing that fixes the threshold or `ηflat` sees `C_F`, so the uniformity is free.

Its remaining hypotheses are exactly what `Kakeya.ml1Boot.exists_factorOneScaleUniform_dilate`
returns, in items (a), (c) and (d), bundled as `Kakeya.ml1Boot.IsFineInputDilate`.  As there,
the bracket `𝕋̃[T̃_{b,l₀}]` is the **parent-map** fibre throughout. -/
theorem reduceToTb_fine_factor_dilate [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    (c : NNReal) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hKF : FrostmanEstimate.{u} E γ) :
    ∀ ap' > (0 : ℝ), ∃ ηflat > (0 : ℝ),
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ b : NNReal, δt ≤ b → b ≤ 1 →
      ∀ {a : ℝ}, 0 ≤ a → a + 2 * ap' ≤ ηflat →
      ∀ {ι : Type u} {κ : Type*} [DecidableEq κ] {u u' : Finset ι}
        (T T' : ι → ShadedTube δt E) (Tbl : Tube b E) (pb : ι → κ)
        (K : ConvexSpaceBody E) (M CF : NNReal)
        {lamσ : ENNReal} {l₀ : κ} {R : ℝ},
        1 ≤ M →
        1 ≤ CF →
        0 < lamσ →
        (δt : ENNReal) ^ a
          ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal) →
        Tbl.carrier ⊆ Metric.closedBall 0 R →
        K ≤ Tube.dilate Tbl (c : ℝ) →
        volume (Tube.dilate Tbl (c : ℝ)).carrier ≤ (M : ENNReal) * volume K.carrier →
        (∀ i ∈ u, pb i = l₀ → (T i).toConvexSpaceBody ≤ K) →
        frostmanConstIn (fibre u pb l₀) (fun i => (T i).toConvexSpaceBody) K
          ≤ 2 * (CF : ENNReal) * (δt : ENNReal) ^ (-ap') →
        IsFineInputDilate ap' u T pb u' T' lamσ l₀ →
        ShadedBody.multiplicity (fibre u' pb l₀) (fun i => (T' i).toShadedBody)
          ≤ (M : ENNReal) * (reduceToTbFineBoundDilate.C c CF : ENNReal)
            * (δt : ENNReal) ^ (-3 * ap')
            * ((δt / b : NNReal) : ENNReal) ^ (-2 * γ)
            * (((fibre u' pb l₀).card : ENNReal)
              * ((δt / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  intro ap' hap'
  obtain ⟨ηflat, hηflat, hfineBound⟩ :=
    reduceToTb_fine_bound_dilate hdim c hγ0 hγ1 hKF ap' hap'
  -- the smallness condition of `reduceToTb_fine_input` holds for all small `δt`
  have habsorbev : ∀ᶠ (δt : NNReal) in 𝓝[>] (0 : NNReal),
      4 * (fineNormalizeDilate.C c : ENNReal) * (δt : ENNReal) ^ ap' ≤ 1 := by
    have hC_pos : 0 < fineNormalizeDilate.C c := by
      exact lt_of_lt_of_le zero_lt_one (one_le_fineNormalizeDilate_C c)
    have hf0 : (fineNormalizeDilate.C c : ENNReal) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr (ne_of_gt hC_pos)
    let C2 : ENNReal := 4 * (fineNormalizeDilate.C c : ENNReal)
    have hC2_0 : C2 ≠ 0 := by
      dsimp [C2]
      exact mul_ne_zero (by norm_num : (4 : ENNReal) ≠ 0) hf0
    have hC2_top : C2 ≠ ⊤ := by
      dsimp [C2]
      exact ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
    have hinv : 0 < C2⁻¹ := by
      rw [ENNReal.inv_pos]
      exact hC2_top
    filter_upwards [ENNReal.eventually_coe_rpow_le_of_pos (ρ := ap') hap' hinv] with δt hδ
    calc
      C2 * (δt : ENNReal) ^ ap' ≤ C2 * C2⁻¹ := by
        exact mul_le_mul_of_nonneg_left hδ (by positivity)
      _ = 1 := ENNReal.mul_inv_cancel hC2_0 hC2_top
  refine ⟨ηflat, hηflat, ?_⟩
  filter_upwards [hfineBound, habsorbev, self_mem_nhdsWithin] with δt hfine habsorb hδt0
  intro b hδtb hb1
  have hδt1 : δt ≤ 1 := le_trans hδtb hb1
  intro a ha hηflat_le ι κ _ u u' T T' Tbl pb K M CF lamσ l₀ R
    hM hCF hlamσ hfull hball hKle hKfat hKfib hFrostman hinput
  -- `reduceToTb_fine_input` discharges the two hypotheses of the bound lemma
  obtain ⟨hFr, hFull⟩ :=
    reduceToTb_fine_input (δt := δt) hδt0 hδt1 (a := a) (ap' := ap')
      (ηflat := ηflat) ha hap' hηflat_le c CF habsorb K hfull hKfib hFrostman hinput
  -- convert the Frostman bound from `T` to `T'`, which shade the same tubes (`tube_eq`)
  have hconv : ∀ i ∈ fibre u' pb l₀, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody := by
    intro i hi
    have hi' : i ∈ u' := (Finset.mem_filter.mp hi).1
    have htube := hinput.tube_eq i hi'
    simpa using congrArg (fun Td : Tube δt E => Td.toConvexSpaceBody) htube
  have hdens_congr : ∀ B : ConvexSpaceBody E,
      densityIn (fibre u' pb l₀) (fun i => (T' i).toConvexSpaceBody) B
        = densityIn (fibre u' pb l₀) (fun i => (T i).toConvexSpaceBody) B := by
    intro B
    simp only [densityIn]
    have hfilter : (fibre u' pb l₀).filter (fun i => (T' i).toConvexSpaceBody ≤ B) =
        (fibre u' pb l₀).filter (fun i => (T i).toConvexSpaceBody ≤ B) := by
      exact Finset.filter_congr (fun i hi => by rw [hconv i hi])
    rw [hfilter]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun B' : ConvexSpaceBody E => volume B'.carrier)
      (hconv i (Finset.mem_filter.mp hi).1)
  have hFrostEq : frostmanConstIn (fibre u' pb l₀) (fun i => (T' i).toConvexSpaceBody) K
      = frostmanConstIn (fibre u' pb l₀) (fun i => (T i).toConvexSpaceBody) K := by
    refine congrArg sInf (Set.ext fun C => ?_)
    constructor <;> intro h K' hK' <;>
      simpa [hdens_congr K', hdens_congr K] using h K' hK'
  have hFr' : frostmanConstIn (fibre u' pb l₀) (fun i => (T' i).toConvexSpaceBody) K
      ≤ 2 * (CF : ENNReal) * (δt : ENNReal) ^ (-2 * ap') := by
    rw [hFrostEq]
    exact hFr
  -- the remaining hypotheses of the bound lemma, for the fibre and the tubes `T'`
  have hne : (fibre u' pb l₀).Nonempty := hinput.fibre_nonempty
  have hcontainT : ∀ i ∈ fibre u' pb l₀, (T' i).toConvexSpaceBody ≤ K := by
    intro i hi
    have hi' : i ∈ u' := (Finset.mem_filter.mp hi).1
    have hpb : pb i = l₀ := (Finset.mem_filter.mp hi).2
    rw [hconv i hi]
    exact hKfib i (hinput.subset hi') hpb
  have hpairT : ((fibre u' pb l₀ : Finset ι) : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T' i).carrier (T' j).carrier) := by
    intro i hi j hj hij
    have hT := hinput.fibre_essDistinct hi hj hij
    have hi' : i ∈ u' := (Finset.mem_filter.mp hi).1
    have hj' : j ∈ u' := (Finset.mem_filter.mp hj).1
    have hTi : (T' i).carrier = (T i).carrier := by
      have htube := hinput.tube_eq i hi'
      simpa using congrArg (fun Td : Tube δt E => Td.carrier) htube
    have hTj : (T' j).carrier = (T j).carrier := by
      have htube := hinput.tube_eq j hj'
      simpa using congrArg (fun Td : Tube δt E => Td.carrier) htube
    simpa [hTi, hTj] using hT
  have hdensT : ∀ i ∈ fibre u' pb l₀,
      lamσ * volume (T' i).carrier ≤ volume (T' i).shade ∧
        volume (T' i).shade ≤ 2 * lamσ * volume (T' i).carrier := by
    intro i hi
    have hi' : i ∈ u' := (Finset.mem_filter.mp hi).1
    have hdens := hinput.dens i hi'
    have hcar : volume (T' i).carrier = volume (T i).carrier := by
      have htube := hinput.tube_eq i hi'
      simpa using congrArg (fun Td : Tube δt E => volume Td.carrier) htube
    rw [hcar]
    exact hdens
  exact hfine b hδtb hb1 (ι := ι) (u := fibre u' pb l₀) (Tb := Tbl) (T := T') (K := K) (M := M)
    (CF := CF) (lamσ := lamσ) hM hCF hlamσ hne hball hKle hKfat hcontainT hpairT hdensT hFr'
    hFull

/-- **Discharging the dilate fullness hypothesis** (blueprint
`lem:ml1bootReduceToTbDilateFullness`).

With `γ ap' = 10 a / ε`, `0 < γ ≤ 1` and `0 < ε ≤ 1` one has `ap' ≥ 10 a`, hence
`a ≤ ap' / 2`, and therefore every `lam ≥ δ̃ ^ a` also satisfies `lam ≥ δ̃ ^ (ap' / 2)`, which is
the fullness hypothesis of `Kakeya.ml1Boot.exists_factorOneScaleUniform_dilate` at
`ε' = ap' / 2`.

Both `γ ≤ 1` and `ε ≤ 1` are needed and are the only facts about `γ` and `ε` used.  The lemma
is stated separately so that the one place `Kakeya.ml1Boot.normalized_le_of_coarse` needs
`ε ≤ 1` is visible rather than buried in an already long assembly proof. -/
theorem reduceToTb_dilate_fullness {δt : NNReal} (hδt0 : 0 < δt) (hδt1 : δt ≤ 1)
    {γ ε a ap' : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ha : 0 ≤ a)
    (hlink : γ * ap' = 10 * a / ε) :
    a ≤ ap' / 2 ∧
      ∀ lam : ENNReal, (δt : ENNReal) ^ a ≤ lam → (δt : ENNReal) ^ (ap' / 2) ≤ lam := by
  have hδt1E : (δt : ENNReal) ≤ 1 := by exact_mod_cast hδt1
  have hεγ_le_1 : ε * γ ≤ 1 := by
    nlinarith [mul_le_mul hγ1 hε1 hε0.le (by norm_num : (0 : ℝ) ≤ 1)]
  have hεγ_mul_ap' : (ε * γ) * ap' = 10 * a := by
    calc
      (ε * γ) * ap' = ε * (γ * ap') := by ring
      _ = ε * (10 * a / ε) := by rw [hlink]
      _ = 10 * a := by field_simp [hε0.ne']
  have hεγ_pos : 0 < ε * γ := mul_pos hε0 hγ0
  have hap0 : 0 ≤ ap' := by
    exact (mul_nonneg_iff_of_pos_left hεγ_pos).mp (by rw [hεγ_mul_ap']; positivity)
  have h10a_le_ap' : 10 * a ≤ ap' := by
    calc
      10 * a = (ε * γ) * ap' := by rw [hεγ_mul_ap']
      _ ≤ 1 * ap' := mul_le_mul_of_nonneg_right hεγ_le_1 hap0
      _ = ap' := by simp
  have ha_le_ap' : a ≤ ap' / 2 := by
    nlinarith [h10a_le_ap', ha]
  constructor
  · exact ha_le_ap'
  · intro lam hfull
    calc
      (δt : ENNReal) ^ (ap' / 2) ≤ (δt : ENNReal) ^ a := by
        exact ENNReal.rpow_le_rpow_of_exponent_ge hδt1E ha_le_ap'
      _ ≤ lam := hfull

/-- **Selecting a surviving parent index** (blueprint `lem:ml1bootReduceToTbIndexSelect`).

If the retained fine index set `s'` is nonempty and every retained member has its parent in
`t''`, then `t''` is nonempty and some `l₀ ∈ t''` has a nonempty fibre in `s'`; the three
cardinality bounds follow.

Only the index data `(s, t, p)` is used, so the statement holds verbatim for an ordinary
parent family (`Kakeya.ml1Boot.IsParentFamily`, the case `c = 1`); the dilate hypothesis is
carried because that is the form the assembly has in hand. -/
theorem exists_surviving_parent_index [Nontrivial E] {c : ℝ} {σ ρ : NNReal}
    {ι κ : Type*} [DecidableEq κ] {s s' : Finset ι} {t t'' : Finset κ}
    {V : ι → Tube σ E} {Vρ : κ → Tube ρ E} {p : ι → κ}
    (_hparent : IsParentFamilyDilate c s V t Vρ p)
    (hs' : s' ⊆ s) (hs'ne : s'.Nonempty) (hmapsTo : ∀ i ∈ s', p i ∈ t'') :
    t''.Nonempty ∧ ∃ l₀ ∈ t'', (fibre s' p l₀).Nonempty ∧
      1 ≤ (fibre s' p l₀).card ∧ 1 ≤ t''.card ∧ 1 ≤ s.card := by
  rcases hs'ne with ⟨i₀, hi₀⟩
  refine ⟨⟨p i₀, hmapsTo i₀ hi₀⟩, p i₀, hmapsTo i₀ hi₀, ?_, ?_, ?_, ?_⟩
  · exact ⟨i₀, by simp [fibre, hi₀]⟩
  · exact Finset.card_pos.mpr ⟨i₀, by simp [fibre, hi₀]⟩
  · exact Finset.card_pos.mpr ⟨p i₀, hmapsTo i₀ hi₀⟩
  · exact Finset.card_pos.mpr ⟨i₀, hs' hi₀⟩

end ReduceToTb

end ml1Boot

end Kakeya
