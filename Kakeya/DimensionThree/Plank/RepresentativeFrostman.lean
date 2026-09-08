/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.RepresentativeDensity
public import Kakeya.FrostmanConstant

/-!
# The two Frostman-specific inputs of GWZ Lemma 6.4

GWZ Lemma 6.4 feeds the output of Lemma 6.13 into the generalized Frostman tube estimate. Two
geometric inputs are needed before that assembly can start, and this file supplies both.

## Input 1: the fibre bound `N ≲ M θ`

`Plank.ThickenedRepr.fibreScale_le_of_nonconcentration`. The representative fibre
`repr⁻¹(Q) ∩ s` is contained in a *fixed dilation* of the standard `θ`-thickening of any one of its
own members (`Plank.ThickenedRepr.fibre_subset_dilated_thickening`), so a non-concentration
hypothesis for those dilated thickenings bounds the fibre by `M θ` and hence `N ≤ cN · M · θ`.

The dilation is unavoidable, and it is why the hypothesis is `Plank.IsThickeningNonconcentrated`
rather than the aligned-prism count `|{j ∈ s : P_j ⊆ (P_i)_θ}| ≤ M θ`: the representative geometry
of `Plank.ThickenedRepr` controls a plank only through `subset_repr` and `repr_subset_thickened`,
both of which are fixed-dilation statements, and dilating an aligned `θb × b × 1` thickening also
widens its `b`- and `1`-axes, which no aligned thickening at any scale `φ ≤ 1` recovers.

Concretely, the aligned form is *not* sufficient: take `a = b`, `θ = 1`, `Q` the common
representative of `K` planks obtained from one plank by translating along its long axis by distinct
amounts `δ ∈ (0,1)`. All `K` planks are non-essentially-distinct from `Q` and lie in
`Q.dilation 2`, so they form one fibre of a legitimate `ThickenedRepr`; but
`(V i).thickened 1 = V i` here, so `{j ∈ s : V j ⊆ (V i).thickened 1} = {i}` and the aligned count
is `1 ≤ M · θ` with `M = 1`, while the fibre has `K` members. The dilated hypothesis rules this out
because all `K` planks *do* lie in the dilated thickening of each other.

`Plank.IsThickeningNonconcentrated.mono` records that the hypothesis gets stronger as the dilation
factor grows, so the value used here is a genuine strengthening of the aligned form at `C = 1`.

## Input 2: the Frostman transfer to one slab fibre

`Plank.ThickenedRepr.frostmanConstant_slabFibre_le`. With `Kakeya.frostmanConstant W K` normalised
as `Δ_max(𝕎) · |K| / ∑_{i} |W i|`, the transfer is an exact computation on top of the maximal-density
transfer `Plank.ThickenedRepr.mul_maxDensity_repr_le` of `RepresentativeDensity.lean`:

* the maximal density of the representatives obeys `a N Δ_max(𝒯_S) ≲ θ b Δ_max(𝒫)`;
* `Δ_max(𝒫) · |B| ≤ C_F · |s| · 8ab` is the Frostman hypothesis in division-free form;
* every plank has volume `8ab` and every representative has volume `8θb²`, so the scale factors
  cancel *exactly*: `(θ b) · (a b) = a · (θ b²)`;
* the `1/N` created by the fibre transfer is cancelled by `|s| ≤ cN · N · |𝒯|`
  (`Plank.ThickenedRepr.card_fibreFamily_eq_sum_fibre`), which is the only place a cardinality
  ratio is introduced.

What is left is the honest slab factor `|𝒯| / |𝒯_S|` of the paper's `C_F(𝒫'_{θ,S}, S) ≲ C |𝒮| |S|`.
It is *not* absorbed into a constant: the invalid simplification `C_F(𝒫, B_1) ≤ C ⟹
C_F(𝒫_{θ,S}, S) ≤ C` is exactly what that ratio prevents. The `|S|` on the right-hand side is
definitional (it is the `|K|` of `Kakeya.frostmanConstant`), so no slab-versus-ball volume
comparison is needed anywhere.

The global upward-inheritance statement `C_F(𝒯, B) ≲ C_F(𝒫, B)` is
`Plank.ThickenedRepr.frostmanConstant_repr_le`, the same computation at `T = 𝒯` and `K = B`.
-/

@[expose] public section

open MeasureTheory Metric Kakeya
open scoped NNReal Classical

noncomputable section

namespace Kakeya

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **Division-free form of a Frostman hypothesis.** If the family is `CF`-Frostman in `K` and all
of its bodies lie in `K`, then `Δ_max(𝕎) · |K| ≤ CF · ∑_i |W i|`. This is
`Kakeya.frostmanConstant s W K ≤ CF` with the division cleared, and it is the form the transfer
below consumes. -/
theorem maxDensity_mul_volume_le_of_isFrostmanIn {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {CF : ENNReal}
    (hFr : ConvexSpaceBody.IsFrostmanIn s W K CF) (hWK : ∀ i ∈ s, W i ≤ K)
    (hK0 : volume K.carrier ≠ 0) :
    maxDensity s W * volume K.carrier ≤ CF * ∑ i ∈ s, volume (W i).carrier := by
  calc
    maxDensity s W * volume K.carrier ≤ CF * densityIn s W K * volume K.carrier := by
      gcongr
      exact hFr.maxDensity_le_of_carrier_subset hWK
    _ = CF * ∑ i ∈ s, volume (W i).carrier := by
      rw [mul_assoc, densityIn_of_all_le hWK,
        ENNReal.div_mul_cancel hK0 K.isCompact.measure_ne_top]

/-- The scalar Frostman constant is bounded by any admissible Frostman constant, provided the
family lies in the reference body and carries positive mass. -/
theorem frostmanConstant_le_of_isFrostmanIn {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {CF : ENNReal}
    (hFr : ConvexSpaceBody.IsFrostmanIn s W K CF) (hWK : ∀ i ∈ s, W i ≤ K)
    (hK0 : volume K.carrier ≠ 0) (hmass : ∑ i ∈ s, volume (W i).carrier ≠ 0) :
    frostmanConstant s W K ≤ CF := by
  have hsum_top : (∑ i ∈ s, volume (W i).carrier) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => (W i).isCompact.measure_ne_top
  unfold frostmanConstant
  rw [ENNReal.div_le_iff hmass hsum_top]
  exact maxDensity_mul_volume_le_of_isFrostmanIn hFr hWK hK0

/-- The plank window has volume at least `1`: it contains the unit cube, of volume `8`. -/
theorem one_le_volume_plankWindow : 1 ≤ volume plankWindow.carrier := by
  let P : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
    PrismNDim.mk' 0 (EuclideanSpace.basisFun (Fin 3) ℝ) (fun _ : Fin 3 => 1)
  have hvolP : volume P.carrier = (8 : ENNReal) := by
    rw [PrismNDim.volume_carrier]
    simp [P, PrismNDim.thicknesses_mk']
    norm_num
  have hsub3 : (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 : ℝ) := by
    calc
      (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
          Metric.closedBall P.center (∑ i, (P.thicknesses i : ℝ)) := P.carrier_subset_closedBall
      _ = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 : ℝ) := by
        simp [P, PrismNDim.center_mk', PrismNDim.thicknesses_mk']
  have hsub4 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 : ℝ) ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (4 : ℝ) := by
    exact Metric.closedBall_subset_closedBall (by norm_num : (3 : ℝ) ≤ 4)
  calc
    1 ≤ volume P.carrier := by
      rw [hvolP]
      norm_num
    _ ≤ volume plankWindow.carrier := by
      rw [plankWindow_carrier]
      exact measure_mono (hsub3.trans hsub4)

end Kakeya

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk : ℝ≥0}
  {ι : Type*} {s : Finset ι} {V : ι → Plank a b hab hb1}

/-! ### Input 1: the fibre bound `N ≲ M θ` -/

/-- **Non-concentration of a plank family in dilated thickenings.** For every scale
`φ ∈ [a/b, 1]` and every member `P_i`, at most `M · φ` of the planks lie in the `C`-dilation of the
standard `φ`-thickening `(P_i)_φ`.

At `C = 1` this is the aligned-prism hypothesis of `Kakeya.FrostmanEstimate.plankEstimate`; the
predicate is monotone in `C` (`Plank.IsThickeningNonconcentrated.mono`), so larger `C` is a
strictly stronger hypothesis. The representative geometry forces `C > 1`; see the module
docstring for why the aligned form cannot bound a representative fibre. -/
def IsThickeningNonconcentrated (s : Finset ι) (V : ι → Plank a b hab hb1) (C M : ℝ≥0) : Prop :=
  ∀ i ∈ s, ∀ (φ : ℝ≥0) (hφ1 : φ ≤ 1), a / b ≤ φ →
    ((s.filter fun j => ((V j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        (((V i).thickened φ hφ1).toPrismNDim.dilation C).carrier).card : ℝ≥0) ≤ M * φ

/-- Non-concentration in dilated thickenings is monotone in the dilation factor: the hypothesis at
the larger factor is the stronger one. -/
theorem IsThickeningNonconcentrated.mono {C C' M : ℝ≥0} (hCC' : C ≤ C')
    (h : IsThickeningNonconcentrated s V C' M) : IsThickeningNonconcentrated s V C M := by
  intro i hi φ hφ1 hφa
  refine (Nat.cast_le.mpr ?_).trans (h i hi φ hφ1 hφa)
  exact Finset.card_le_card
    (Finset.monotone_filter_right s fun j _ hj =>
      hj.trans (PrismNDim.dilation_carrier_mono ((V i).thickened φ hφ1).toPrismNDim hCC'))

namespace ThickenedRepr

/-- The absolute dilation factor at which a representative fibre is seen from one of its own
members: dilating a plank into its representative costs `cThk`, dilating the representative into
the thickening of the anchor costs `cThk` again, and re-centring the first dilation on the anchor's
thickening costs the `1 + 2 · cThk` of `PrismNDim.dilation_carrier_subset_dilation_of_subset`. -/
def fibreDilation (cThk : ℝ≥0) : ℝ≥0 := (1 + 2 * cThk) * cThk

theorem one_le_fibreDilation {cThk : ℝ≥0} (hcThk : 1 ≤ cThk) : 1 ≤ fibreDilation cThk := by
  rw [fibreDilation]
  exact one_le_mul (le_add_of_nonneg_right (by positivity)) hcThk

/-- **The fibre is seen from any of its members.** Every plank of the fibre `repr⁻¹(Q)` lies in the
`fibreDilation cThk`-dilation of the standard `θ`-thickening of any fixed member `i₀` of that
fibre. This is the only geometric input of the fibre bound, and it is unconditional: no essential
distinctness, no smallness of `a`, `b` or `θ`, and no non-concentration. -/
theorem fibre_subset_dilated_thickening (R : ThickenedRepr s V θ hθ1 cThk)
    {Q : ThickenedPlank θ b hθ1 hb1} {i₀ : ι} (hi₀ : i₀ ∈ s) (hQ : R.repr i₀ = Q)
    {j : ι} (hj : j ∈ s) (hj' : R.repr j = Q) :
    ((V j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (((V i₀).thickened θ hθ1).toPrismNDim.dilation (fibreDilation cThk)).carrier := by
  -- Step 1: `V j` lies in the `cThk`-dilation of its representative `Q`.
  have h1 : ((V j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      ((Q.toPrismNDim.dilation cThk).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    simpa [hj'] using R.subset_repr j hj
  -- Step 2: `Q` lies in the `cThk`-dilated `θ`-thickening of the anchor `V i₀`.
  let K : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
    ((V i₀).thickened θ hθ1).toPrismNDim.dilation cThk
  have h2 : (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ K.carrier := by
    simpa [K, hQ] using R.repr_subset_thickened i₀ hi₀
  -- Step 3: dilating the containment at factor `cThk` carries the `cThk`-dilation of `Q`.
  have h3 : ((Q.toPrismNDim.dilation cThk).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (K.dilation (1 + 2 * cThk)).carrier := by
    exact PrismNDim.dilation_carrier_subset_dilation_of_subset (by simpa using h2) cThk
  -- Chain, collapsing the double dilation to the single factor `fibreDilation cThk`.
  exact h1.trans (by
    simpa [K, fibreDilation, PrismNDim.dilation_dilation] using h3)

/-- **The fibre bound.** Under non-concentration in `fibreDilation cThk`-dilated thickenings, every
active representative fibre has at most `M · θ` members. -/
theorem card_fibre_le_of_nonconcentration (R : ThickenedRepr s V θ hθ1 cThk) {M : ℝ≥0}
    (hM : IsThickeningNonconcentrated s V (fibreDilation cThk) M) (hθa : a / b ≤ θ)
    {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ R.indexSet) :
    ((s.filter fun i => R.repr i = Q).card : ℝ≥0) ≤ M * θ := by
  classical
  rcases Finset.mem_image.mp hQ with ⟨i₀, hi₀, hQeq⟩
  have hsub : s.filter (fun i => R.repr i = Q) ⊆
      s.filter (fun j => ((V j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        (((V i₀).thickened θ hθ1).toPrismNDim.dilation (fibreDilation cThk)).carrier) := by
    intro j hj
    have hjmem : j ∈ s ∧ R.repr j = Q := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr
      ⟨hjmem.1, fibre_subset_dilated_thickening R hi₀ hQeq hjmem.1 hjmem.2⟩
  calc
    ((s.filter fun i => R.repr i = Q).card : ℝ≥0) ≤
        ((s.filter fun j => ((V j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
            (((V i₀).thickened θ hθ1).toPrismNDim.dilation (fibreDilation cThk)).carrier).card :
          ℝ≥0) := by
          exact_mod_cast Finset.card_le_card hsub
    _ ≤ M * θ := hM i₀ hi₀ θ hθ1 hθa

/-- **`N ≲ M θ`.** The uniform fibre scale `N` produced by GWZ Lemma 6.13 obeys
`N ≤ cN · M · θ`. The loss is exactly the pigeonhole constant `cN` of the fibre-size comparison;
no power of `b / a` appears, and no large-`θ` branch is needed, because the dilation sits inside the
hypothesis rather than in its scale. -/
theorem fibreScale_le_of_nonconcentration (R : ThickenedRepr s V θ hθ1 cThk) {M : ℝ≥0}
    (hM : IsThickeningNonconcentrated s V (fibreDilation cThk) M) (hθa : a / b ≤ θ)
    {N : ℕ} {cN : ℝ≥0} (hcN : 0 < cN) (hne : R.indexSet.Nonempty)
    (hfib : ∀ Q ∈ R.indexSet, (N : ℝ) / (cN : ℝ) ≤ ((s.filter fun i => R.repr i = Q).card : ℝ)) :
    (N : ℝ≥0) ≤ cN * M * θ := by
  rcases hne with ⟨Q, hQ⟩
  have hcard_le : ((s.filter fun i => R.repr i = Q).card : ℝ≥0) ≤ M * θ :=
    card_fibre_le_of_nonconcentration R hM hθa hQ
  have hcard_le_real : ((s.filter fun i => R.repr i = Q).card : ℝ) ≤ (M * θ : ℝ) := by
    exact_mod_cast hcard_le
  have hN_le_Mθ : (N : ℝ) / (cN : ℝ) ≤ (M * θ : ℝ) := le_trans (hfib Q hQ) hcard_le_real
  have hcN_real : 0 < (cN : ℝ) := by exact_mod_cast hcN
  have hN_le : (N : ℝ) ≤ (M * θ : ℝ) * (cN : ℝ) := (div_le_iff₀ hcN_real).mp hN_le_Mθ
  have hN_le' : (N : ℝ) ≤ ((cN * M * θ : ℝ≥0) : ℝ) := by
    calc
      (N : ℝ) ≤ (M * θ : ℝ) * (cN : ℝ) := hN_le
      _ = ((cN * M * θ : ℝ≥0) : ℝ) := by
        norm_cast
        ring
  exact_mod_cast hN_le'

/-! ### Input 2: the Frostman transfer -/

/-- Every thickened representative has the volume `8 θ b²` of a `θb × b × 1` prism. -/
theorem volume_thickenedPlank (Q : ThickenedPlank θ b hθ1 hb1) :
    volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = 8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal) := by
  rw [Prism3D.volume_carrier Q]
  push_cast
  ring

/-- The total mass of a finite family of thickened representatives. -/
theorem sum_volume_thickenedPlank (T : Finset (ThickenedPlank θ b hθ1 hb1)) :
    ∑ Q ∈ T, volume ((fun Q : ThickenedPlank θ b hθ1 hb1 => Q.toConvexSpaceBody) Q).carrier
      = (T.card : ENNReal) * (8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) := by
  calc
    ∑ Q ∈ T, volume ((fun Q : ThickenedPlank θ b hθ1 hb1 => Q.toConvexSpaceBody) Q).carrier
        = ∑ _Q ∈ T, (8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) := by
          refine Finset.sum_congr rfl ?_
          intro Q hQ
          simpa using volume_thickenedPlank Q
    _ = (T.card : ENNReal) * (8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- The total mass of the original plank family. -/
theorem sum_volume_plank (s : Finset ι) (V : ι → Plank a b hab hb1) :
    ∑ i ∈ s, volume ((fun i => (V i).toConvexSpaceBody) i).carrier
      = (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
  calc
    ∑ i ∈ s, volume ((fun i => (V i).toConvexSpaceBody) i).carrier
        = ∑ _i ∈ s, (8 * (a : ENNReal) * (b : ENNReal)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using Prism3D.volume_carrier (V i)
    _ = (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- **The core of the Frostman transfer**, in the division-free form that both consumers use:
the maximal density of any set `T` of representatives, weighted by the window volume, is bounded by
the Frostman constant of the original family times the representative mass `|𝒯| · 8θb²`.

The `1/N` of the density transfer is cancelled here, against `|s| ≤ cN · N · |𝒯|`; the two scale
factors cancel exactly, since `(θ b) · (a b) = a · (θ b²)`. -/
theorem mul_volume_plankWindow_maxDensity_repr_le (R : ThickenedRepr s V θ hθ1 cThk)
    {T : Finset (ThickenedPlank θ b hθ1 hb1)} (hT : T ⊆ R.indexSet)
    {N : ℕ} {cN : ℝ≥0} (hN : 1 ≤ N) (hcN : 1 ≤ cN) (ha : 0 < a)
    (hlo : ∀ Q ∈ R.indexSet, (N : ℝ) / (cN : ℝ) ≤ ((s.filter fun i => R.repr i = Q).card : ℝ))
    (hhi : ∀ Q ∈ R.indexSet, ((s.filter fun i => R.repr i = Q).card : ℝ) ≤ (cN : ℝ) * (N : ℝ))
    {CF : ENNReal} (hVwin : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ plankWindow)
    (hFrost : ConvexSpaceBody.IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow CF) :
    maxDensity T (fun Q => Q.toConvexSpaceBody) * volume plankWindow.carrier ≤
      ((enlargementConst cThk * cN ^ 2 : ℝ≥0) : ENNReal) * CF *
        (R.indexSet.card : ENNReal) * (8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) := by
  classical
  let aN : ENNReal := (a : ENNReal) * (N : ENNReal)
  let ΔT : ENNReal := maxDensity T (fun Q => Q.toConvexSpaceBody)
  let volB : ENNReal := volume plankWindow.carrier
  let ΔP : ENNReal := maxDensity s (fun i => (V i).toConvexSpaceBody)
  let C : ENNReal := (enlargementConst cThk : ENNReal)
  let cN' : ENNReal := (cN : ENNReal)
  let rhs : ENNReal := ((enlargementConst cThk * cN ^ 2 : ℝ≥0) : ENNReal) * CF *
    (R.indexSet.card : ENNReal) * (8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal))
  -- Fibre bounds for `T` from the full index set.
  have hcN0 : 0 < cN := lt_of_lt_of_le zero_lt_one hcN
  have hfib_T : ∀ Q ∈ T, (N : ℝ) / (cN : ℝ) ≤ ((s.filter fun i => R.repr i = Q).card : ℝ) :=
    fun Q hQ => hlo Q (hT hQ)
  -- Step 1: the density transfer.
  have hdens : aN * ΔT ≤ C * cN' * ((θ : ENNReal) * (b : ENNReal)) * ΔP := by
    simpa [aN, ΔT, C, cN'] using
      (Plank.ThickenedRepr.mul_maxDensity_repr_le R hT hcN0 hfib_T)
  -- Step 2: the Frostman hypothesis in division-free form.
  have hvolB0 : volume plankWindow.carrier ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (Kakeya.one_le_volume_plankWindow))
  have hFrost_le : ΔP * volB ≤
      CF * ∑ i ∈ s, volume ((fun i => (V i).toConvexSpaceBody) i).carrier := by
    simpa [ΔP, volB] using
      (Kakeya.maxDensity_mul_volume_le_of_isFrostmanIn (s := s)
        (W := fun i => (V i).toConvexSpaceBody) (K := plankWindow) (CF := CF) hFrost hVwin hvolB0)
  -- Step 3: the total mass of the original planks.
  have hsum : ∑ i ∈ s, volume ((fun i => (V i).toConvexSpaceBody) i).carrier
      = (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
    exact Plank.ThickenedRepr.sum_volume_plank s V
  -- Step 4: the cardinality bound, transported to ENNReal.
  have hcard_enn : (s.card : ENNReal) ≤
      (cN : ENNReal) * (N : ENNReal) * (R.indexSet.card : ENNReal) := by
    have hnn : (s.card : ℝ≥0) ≤ cN * (N : ℝ≥0) * (R.indexSet.card : ℝ≥0) := by
      exact_mod_cast (Plank.ThickenedRepr.card_fibreFamily_eq_sum_fibre R N cN hlo hhi).2
    simpa using (ENNReal.coe_le_coe.mpr hnn)
  -- Main chain.
  have hmain : aN * (ΔT * volB) ≤ aN * rhs := by
    calc
      aN * (ΔT * volB) = aN * ΔT * volB := by ring
      _ ≤ C * cN' * ((θ : ENNReal) * (b : ENNReal)) * ΔP * volB := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using (mul_le_mul_right hdens volB)
      _ = C * cN' * ((θ : ENNReal) * (b : ENNReal)) * (ΔP * volB) := by ring
      _ ≤ C * cN' * ((θ : ENNReal) * (b : ENNReal)) *
          (CF * ∑ i ∈ s, volume ((fun i => (V i).toConvexSpaceBody) i).carrier) := by
        gcongr
      _ = C * cN' * ((θ : ENNReal) * (b : ENNReal)) * CF *
          ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) := by
        rw [hsum]
        ring
      _ ≤ C * cN' * ((θ : ENNReal) * (b : ENNReal)) * CF *
          (((cN : ENNReal) * (N : ENNReal) * (R.indexSet.card : ENNReal)) *
            (8 * (a : ENNReal) * (b : ENNReal))) := by
        gcongr
      _ = aN * rhs := by
        simp [aN, rhs, C, cN', ENNReal.coe_mul, ENNReal.coe_pow]
        ring
  -- Cancel `aN`.
  have hN_pos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have haN0 : aN ≠ 0 := by
    dsimp [aN]
    exact mul_ne_zero (ENNReal.coe_ne_zero.mpr (ne_of_gt ha))
      (by
        rw [← ENNReal.coe_natCast]
        exact ENNReal.coe_ne_zero.mpr (by exact_mod_cast (ne_of_gt hN_pos)))
  have haNtop : aN ≠ ⊤ := by
    dsimp [aN]
    exact WithTop.mul_ne_top ENNReal.coe_ne_top (ENNReal.natCast_ne_top N)
  have hcanc : (ΔT * volB) * aN ≤ rhs * aN := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmain
  exact (ENNReal.mul_le_mul_iff_left haN0 haNtop).1 hcanc

/-- **Global upward inheritance** (the paper's `C_F(𝒫'_θ) ≲ C_F(𝒫)`): the full family of selected
thickened representatives is Frostman in the plank window, with the fixed loss
`enlargementConst cThk * cN ^ 2`. -/
theorem frostmanConstant_repr_le (R : ThickenedRepr s V θ hθ1 cThk)
    {N : ℕ} {cN : ℝ≥0} (hN : 1 ≤ N) (hcN : 1 ≤ cN) (ha : 0 < a) (hb : 0 < b) (hθ0 : 0 < θ)
    (hne : R.indexSet.Nonempty)
    (hlo : ∀ Q ∈ R.indexSet, (N : ℝ) / (cN : ℝ) ≤ ((s.filter fun i => R.repr i = Q).card : ℝ))
    (hhi : ∀ Q ∈ R.indexSet, ((s.filter fun i => R.repr i = Q).card : ℝ) ≤ (cN : ℝ) * (N : ℝ))
    {CF : ENNReal} (hVwin : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ plankWindow)
    (hFrost : ConvexSpaceBody.IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow CF) :
    frostmanConstant R.indexSet (fun Q => Q.toConvexSpaceBody) plankWindow ≤
      ((enlargementConst cThk * cN ^ 2 : ℝ≥0) : ENNReal) * CF := by
  unfold frostmanConstant
  rw [sum_volume_thickenedPlank R.indexSet]
  have hcard_ne : (R.indexSet.card : ENNReal) ≠ 0 := by
    rw [← ENNReal.coe_natCast]
    exact ENNReal.coe_ne_zero.mpr (by exact_mod_cast (ne_of_gt (Finset.card_pos.mpr hne)))
  have hθ_ne : (θ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hθ0)
  have hb_ne : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hb)
  have hmass_ne : (8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hθ_ne) hb_ne) hb_ne
  have hden_ne : (R.indexSet.card : ENNReal) *
      (8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) ≠ 0 :=
    mul_ne_zero hcard_ne hmass_ne
  have hmass_ne_top : (8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top 8) ENNReal.coe_ne_top)
      ENNReal.coe_ne_top) ENNReal.coe_ne_top
  have hden_ne_top : (R.indexSet.card : ENNReal) *
      (8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top R.indexSet.card) hmass_ne_top
  rw [ENNReal.div_le_iff hden_ne hden_ne_top]
  simpa [mul_assoc] using
    mul_volume_plankWindow_maxDensity_repr_le R (T := R.indexSet) Finset.Subset.rfl hN hcN ha
      hlo hhi hVwin hFrost

/-- **The Frostman transfer to one slab fibre** (the `C_F(𝒫'_{θ,S}, S) ≲ C |𝒮| |S|` of GWZ Lemma
6.4). For any set `T` of representatives — in the application, those assigned to a single slab `S`
— the scalar Frostman constant of `T` inside `S` is bounded by the Frostman constant of the
original plank family times the *retained* fibre ratio `|𝒯| / |T|` and the slab volume.

No containment of `T` in (a dilation of) `S` is needed: the `|S|` is the `|K|` of
`Kakeya.frostmanConstant`, and the estimate holds for every reference body. The ratio
`|𝒯| / |T|` is the factor that makes the naive `C_F(𝒫, B_1) ≤ C ⟹ C_F(T, S) ≤ C` false, and it is
exposed rather than hidden in the constant. -/
theorem frostmanConstant_slabFibre_le (R : ThickenedRepr s V θ hθ1 cThk)
    {T : Finset (ThickenedPlank θ b hθ1 hb1)} (hT : T ⊆ R.indexSet) (hTne : T.Nonempty)
    {N : ℕ} {cN : ℝ≥0} (hN : 1 ≤ N) (hcN : 1 ≤ cN) (ha : 0 < a) (hb : 0 < b) (hθ0 : 0 < θ)
    (hlo : ∀ Q ∈ R.indexSet, (N : ℝ) / (cN : ℝ) ≤ ((s.filter fun i => R.repr i = Q).card : ℝ))
    (hhi : ∀ Q ∈ R.indexSet, ((s.filter fun i => R.repr i = Q).card : ℝ) ≤ (cN : ℝ) * (N : ℝ))
    {CF : ENNReal} (hVwin : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ plankWindow)
    (hFrost : ConvexSpaceBody.IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow CF)
    (S : Slab θ hθ1) :
    frostmanConstant T (fun Q => Q.toConvexSpaceBody) S.toConvexSpaceBody ≤
      ((enlargementConst cThk * cN ^ 2 : ℝ≥0) : ENNReal) * CF *
        ((R.indexSet.card : ENNReal) / (T.card : ENNReal)) * volume S.carrier := by
  classical
  -- Step 1: the `|B|`-free bound on the maximal density of `T`, from the density transfer and
  -- `1 ≤ volume plankWindow.carrier`.
  have hBig : maxDensity T (fun Q => Q.toConvexSpaceBody) ≤
      ((enlargementConst cThk * cN ^ 2 : ℝ≥0) : ENNReal) * CF *
        (R.indexSet.card : ENNReal) * (8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) := by
    exact (le_mul_of_one_le_right zero_le one_le_volume_plankWindow).trans
      (mul_volume_plankWindow_maxDensity_repr_le R hT hN hcN ha hlo hhi hVwin hFrost)
  -- Step 2: the total-mass denominator `|T| · 8θb²` is nonzero and finite.
  have hTcard0 : (T.card : ENNReal) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hTne)
  have hTcard_top : (T.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmass_ne0 : (8 : ENNReal) * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal) ≠ 0 := by
    positivity
  have hmass_top : (8 : ENNReal) * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.coe_ne_top)) (ENNReal.coe_ne_top)) (ENNReal.coe_ne_top)
  have hden0 : (T.card : ENNReal) *
      (8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) ≠ 0 := by
    exact mul_ne_zero hTcard0 hmass_ne0
  have hden_top : (T.card : ENNReal) *
      (8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top hTcard_top hmass_top
  -- Step 3: unfold the scalar constant, rewrite the total mass of `T`, and clear the denominator.
  unfold frostmanConstant
  rw [sum_volume_thickenedPlank]
  rw [ENNReal.div_le_iff hden0 hden_top]
  calc
    maxDensity T (fun Q => Q.toConvexSpaceBody) * volume S.carrier
        ≤ (((enlargementConst cThk * cN ^ 2 : ℝ≥0) : ENNReal) * CF *
            (R.indexSet.card : ENNReal) * (8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal))) *
            volume S.carrier := by
          gcongr
    _ = (((enlargementConst cThk * cN ^ 2 : ℝ≥0) : ENNReal) * CF *
            ((R.indexSet.card : ENNReal) / (T.card : ENNReal)) * volume S.carrier) *
            ((T.card : ENNReal) * (8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal))) := by
          have hdiv : (R.indexSet.card : ENNReal) / (T.card : ENNReal) * (T.card : ENNReal) =
              (R.indexSet.card : ENNReal) :=
            ENNReal.div_mul_cancel hTcard0 hTcard_top
          conv_lhs => rw [← hdiv]
          ring

end ThickenedRepr

end Plank

end

end
