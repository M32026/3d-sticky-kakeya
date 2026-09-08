module

public import Kakeya.DimensionThree.MainLemma1.Cases

/-!
Exact fixed-source port of the card-retaining fine-normalization construction used by the WZ
middle route.  It is isolated in a internal namespace because the current public projection in
`Cases.lean` omits the card-retention conclusion even though the underlying selection supplies it.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya
namespace ml1Boot
namespace W44NormalizationPort

noncomputable section

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma fineNormalize_C_dominates {c₁ : NNReal}
    (hc₁ : c₁ = _root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * ((2 : ℝ) + 2) * ((_root_.Tube.normalization.C 3 : NNReal) : ℝ)
        * Kakeya.Tube.tubeOverlapCoreClose.C 3)) :
    c₁ ≤ fineNormalize.C (_root_.Tube.normalization.C 3) ∧
      ((4 * _root_.Tube.normalization.C 3) ^ 6 : NNReal) * c₁
        ≤ fineNormalize.C (_root_.Tube.normalization.C 3) ∧
      ((4 * _root_.Tube.normalization.C 3) ^ 12 : NNReal) * c₁
        ≤ fineNormalize.C (_root_.Tube.normalization.C 3) := by
  let CN : NNReal := _root_.Tube.normalization.C 3
  let ratio : ℝ := 4 * ((2 : ℝ) + 2) * (CN : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3
  let D : NNReal := (Kakeya.Tube.tubeOverlapCoreClose.C 3).toNNReal
  let u : NNReal := (16 : NNReal) * CN * D
  have hCN1 : (1 : NNReal) ≤ CN := _root_.Tube.normalization.one_le_C 3
  have hD0 : (0 : ℝ) ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 :=
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < (1 : ℝ))
      (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3))
  have hD1 : (1 : NNReal) ≤ D := by
    dsimp [D]; rw [← NNReal.coe_le_coe, Real.toNNReal_of_nonneg hD0]
    exact le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3)
  have hratio0 : (0 : ℝ) ≤ ratio := by
    dsimp [ratio]
    positivity
  have hu_re : ratio = (u : ℝ) := by
    dsimp [u, ratio, D]
    norm_num
    exact hD0
  have hu : ratio.toNNReal = u := by
    apply NNReal.coe_injective
    rw [Real.toNNReal_of_nonneg hratio0]
    exact hu_re
  have hu1 : (1 : NNReal) ≤ u :=
    one_le_mul (one_le_mul (by norm_num : (1 : NNReal) ≤ 16) hCN1) hD1
  have hu6 : u ^ 6 ≤ u ^ 12 := pow_le_pow_right₀ hu1 (by norm_num)
  have hbase : (1 : NNReal) ≤ 4 * CN := one_le_mul (by norm_num : (1 : NNReal) ≤ 4) hCN1
  have hpw6 : (4 * CN) ^ 6 ≤ (4 * CN) ^ 12 := pow_le_pow_right₀ hbase (by norm_num)
  have h16le : (16 : NNReal) ^ 12 ≤ (4 : NNReal) ^ 36 := by
    calc
      (16 : NNReal) ^ 12 = (4 : NNReal) ^ 24 := by norm_num
      _ ≤ (4 : NNReal) ^ 36 := pow_le_pow_right₀ (by norm_num : (1 : NNReal) ≤ 4) (by norm_num)
  have hu12 : u ^ 12 ≤ ((4 * CN) ^ 6) ^ 6 * D ^ 12 := by
    calc
      u ^ 12 = (16 : NNReal) ^ 12 * CN ^ 12 * D ^ 12 := by dsimp [u]; rw [mul_pow, mul_pow]
      _ ≤ (4 : NNReal) ^ 36 * CN ^ 36 * D ^ 12 := by
            exact mul_le_mul
              (mul_le_mul h16le (pow_le_pow_right₀ hCN1 (by norm_num))
                (by positivity) (by positivity))
              le_rfl (by positivity) (by positivity)
      _ = ((4 * CN) ^ 6) ^ 6 * D ^ 12 := by rw [← mul_pow, ← pow_mul]
  have hkey : c₁ ≤ _root_.Tube.comparableReplacement.C 3 ((4 * CN) ^ 6) := by
    rw [hc₁]
    unfold _root_.Tube.essDistinctTubesInSelfDilate.C
      _root_.Tube.essDistinctTubesInSelfDilate.thinC
      _root_.Tube.essDistinctTubesInSelfDilate.fatC
      _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
    set A : NNReal :=
      24 * (2 ^ (3 - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C (3 - 1)) ^ 2
        * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * 3 - 1))⁻¹
        * (32 * (3 : NNReal)) ^ (2 * 3 - 1) with hA
    set B : NNReal := 6 ^ (2 * 3) * (Tube.card_le_of_EssDistinct.C 3).toNNReal with hB
    calc
      A * ratio.toNNReal ^ (2 * 3) + B * ratio.toNNReal ^ (4 * 3)
          = A * u ^ 6 + B * u ^ 12 := by rw [hu]
      _ ≤ A * u ^ 12 + B * u ^ 12 := by
            exact add_le_add (mul_le_mul le_rfl hu6 (by positivity) (by positivity)) le_rfl
      _ = (A + B) * u ^ 12 := by ring
      _ ≤ (A + B) * (((4 * CN) ^ 6) ^ 6 * D ^ 12) := by
            exact mul_le_mul le_rfl hu12 (by positivity) (by positivity)
      _ ≤ 1 + (A + B) * (((4 * CN) ^ 6) ^ 6 * D ^ 12) := le_add_self
      _ = _root_.Tube.comparableReplacement.C 3 ((4 * CN) ^ 6) := by
            rw [hA, hB]
            unfold _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
            norm_num
            ring
  constructor
  · unfold fineNormalize.C
    rw [hc₁]
    exact le_add_self
  constructor
  · unfold fineNormalize.C
    exact le_trans
      (le_trans (mul_le_mul hpw6 le_rfl (by positivity) (by positivity))
        (mul_le_mul le_rfl hkey (by positivity) (by positivity)))
      le_self_add
  · unfold fineNormalize.C
    exact le_trans (mul_le_mul le_rfl hkey (by positivity) (by positivity)) le_self_add

/-- **Reading off the four conclusions from `Tube.IsComparableReplacementFree`.**

The package hands back the retained index set `u'`, and its four fields plus two generic
transport lemmas give the three quantitative clauses at the constants recorded here:
multiplicity is exact and pays only the selection constant `C₁`
(`ShadedBody.multiplicity_le_of_isCRefinement` against the refinement clause), fullness pays the
comparability constant `Cv` on top of it (`ShadedBody.IsCRefinement.coe_mul_fullness_le`), and
the Frostman constant pays `C₁` for the passage to the subfamily
(`ConvexSpaceBody.frostmanConstIn_subfamily_le`, applicable because all members of `𝕍` are
`σ`-tubes and hence of equal volume) and `Cv` for the comparability.  The factor `Λ ^ 2` is the
density spread, and enters through the refinement constant `(C₁ Λ ^ 2)⁻¹`. -/
lemma of_comparableReplacementFree {ι : Type*} {u : Finset ι} {σ : NNReal}
    {𝕎 : ι → ShadedBody E} {𝕍 : ι → ShadedTube σ E} {K : ConvexSpaceBody E}
    {Cv Λ C₁ : NNReal} (hΛ : 1 ≤ Λ) (hCv : 1 ≤ Cv) (hC₁ : 1 ≤ C₁)
    (hVK : ∀ i ∈ u, (𝕍 i).toConvexSpaceBody ≤ K)
    (h : _root_.Tube.IsComparableReplacementFree u 𝕎 𝕍 K Cv Λ C₁) :
    ∃ u' ⊆ u, u'.Nonempty ∧
      (u' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (𝕍 i).carrier (𝕍 j).carrier) ∧
        (u.card : ENNReal) ≤ (C₁ : ENNReal) * (u'.card : ENNReal) ∧
        ShadedBody.multiplicity u 𝕎
          ≤ (C₁ : ENNReal) * (Λ : ENNReal) ^ 2
            * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) ∧
        (ShadedBody.fullness u 𝕎 : ENNReal)
          ≤ ((Cv : ENNReal) * (C₁ : ENNReal)) * (Λ : ENNReal) ^ 2
            * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal) ∧
        frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody) K
          ≤ (C₁ : ENNReal) * (Cv : ENNReal)
            * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K := by
  rcases h.select with ⟨u', hu'sub, hu'ne, hpair, hu'card, hcref⟩
  let ce : ENNReal := ((C₁ * Λ ^ 2)⁻¹ : NNReal)
  have hL0 : Λ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hΛ)
  have hC₁0 : C₁ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC₁)
  have hC₁Λ : (C₁ * Λ ^ 2 : NNReal) ≠ 0 := mul_ne_zero hC₁0 (pow_ne_zero 2 hL0)
  have hC₁ΛE0 : ((C₁ * Λ ^ 2 : NNReal) : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hC₁Λ
  have hce0 : ce ≠ 0 := by
    dsimp [ce]
    rw [ENNReal.coe_inv hC₁Λ]
    intro hz
    have hcan := ENNReal.inv_mul_cancel hC₁ΛE0
      (ENNReal.coe_ne_top : ((C₁ * Λ ^ 2 : NNReal) : ENNReal) ≠ ⊤)
    rw [hz, zero_mul] at hcan
    exact zero_ne_one hcan
  have hce_top : ce ≠ ⊤ := by
    dsimp [ce]
    exact ENNReal.coe_ne_top
  have cRef_ne0 : (C₁ * Λ ^ 2 : NNReal)⁻¹ ≠ 0 :=
    ENNReal.coe_ne_zero.mp (by simpa [ce] using hce0)
  have hcoef : ce⁻¹ = (C₁ : ENNReal) * (Λ : ENNReal) ^ 2 := by
    change (((C₁ * Λ ^ 2)⁻¹ : NNReal) : ENNReal)⁻¹ = (C₁ : ENNReal) * (Λ : ENNReal) ^ 2
    rw [ENNReal.coe_inv hC₁Λ]
    rw [InvolutiveInv.inv_inv]
    rw [ENNReal.coe_mul, ENNReal.coe_pow]
  refine ⟨u', hu'sub, hu'ne, hpair, hu'card, ?_, ?_, ?_⟩
  · rw [← h.multiplicity]
    calc
      ShadedBody.multiplicity u (fun i => (𝕍 i).toShadedBody)
          ≤ ce⁻¹ * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := by
            exact ShadedBody.multiplicity_le_of_isCRefinement (s := u)
              (V := fun i => (𝕍 i).toShadedBody) (s' := u')
              (V' := fun i => (𝕍 i).toShadedBody) (c := (C₁ * Λ ^ 2)⁻¹) cRef_ne0 hcref
      _ = (C₁ : ENNReal) * (Λ : ENNReal) ^ 2
              * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := by
            rw [hcoef]
  · have hfullNN : ShadedBody.fullness u 𝕎
        ≤ (Cv : NNReal) * ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) := by
      have hCv0 : Cv ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCv)
      calc
        ShadedBody.fullness u 𝕎
            = (Cv : NNReal) * ((Cv : NNReal)⁻¹ * ShadedBody.fullness u 𝕎) := by
              rw [← mul_assoc, mul_inv_cancel₀ hCv0, one_mul]
        _ ≤ (Cv : NNReal) * ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) := by
              exact mul_le_mul_right h.fullness (Cv : NNReal)
    have hfull1 : (ShadedBody.fullness u 𝕎 : ENNReal)
        ≤ (Cv : ENNReal) * (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ENNReal) := by
      exact_mod_cast hfullNN
    have hcfull : ce * (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ENNReal)
        ≤ (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal) := by
      simpa [ce] using (IsCRefinement.coe_mul_fullness_le hcref)
    have hfull2 : (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ENNReal)
        ≤ (C₁ : ENNReal) * (Λ : ENNReal) ^ 2
            * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal) := by
      have hmm := mul_le_mul_right hcfull ce⁻¹
      rwa [← mul_assoc, ENNReal.inv_mul_cancel hce0 hce_top, one_mul, hcoef] at hmm
    calc
      (ShadedBody.fullness u 𝕎 : ENNReal)
          ≤ (Cv : ENNReal) * (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ENNReal) :=
            hfull1
      _ ≤ (Cv : ENNReal)
            * ((C₁ : ENNReal) * (Λ : ENNReal) ^ 2
                * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal)) := by
            gcongr
      _ = ((Cv : ENNReal) * (C₁ : ENNReal)) * (Λ : ENNReal) ^ 2
            * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal) := by ring
  · rcases hu'ne with ⟨i₀, hi₀⟩
    have hu'ne_nonempty : u.Nonempty := ⟨i₀, hu'sub hi₀⟩
    let v : ENNReal := volume ((𝕍 i₀).toConvexSpaceBody).carrier
    have hvol : ∀ i ∈ u, volume ((𝕍 i).toConvexSpaceBody).carrier = v := by
      intro i hi
      dsimp [v]
      simpa using _root_.Tube.volume_carrier_eq_volume_carrier
        (by simpa using (𝕍 i).toTube) (by simpa using (𝕍 i₀).toTube)
    have hC₁E0 : (C₁ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hC₁0
    have hC₁Etop : (C₁ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hcardκ : (C₁ : ENNReal)⁻¹ * (u.card : ENNReal) ≤ (u'.card : ENNReal) := by
      calc
        (C₁ : ENNReal)⁻¹ * (u.card : ENNReal)
            ≤ (C₁ : ENNReal)⁻¹ * ((C₁ : ENNReal) * (u'.card : ENNReal)) := by
              exact mul_le_mul_right hu'card _
        _ = (u'.card : ENNReal) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hC₁E0 hC₁Etop, one_mul]
    have hκ0 : (C₁ : ENNReal)⁻¹ ≠ 0 := by
      intro hz
      have hcan := ENNReal.inv_mul_cancel hC₁E0 hC₁Etop
      rw [hz, zero_mul] at hcan
      exact zero_ne_one hcan
    have hsubF := ConvexSpaceBody.frostmanConstIn_subfamily_le (s := u)
      (W := fun i => (𝕍 i).toConvexSpaceBody) (K := K)
      (v := v) (κ := (C₁ : ENNReal)⁻¹)
      hu'ne_nonempty hvol hVK hu'sub hκ0 hcardκ
    have hF1 : frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody) K
        ≤ (C₁ : ENNReal) * frostmanConstIn u (fun i => (𝕍 i).toConvexSpaceBody) K := by
      simpa [InvolutiveInv.inv_inv] using hsubF
    calc
      frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody) K
          ≤ (C₁ : ENNReal) * frostmanConstIn u (fun i => (𝕍 i).toConvexSpaceBody) K := hF1
      _ ≤ (C₁ : ENNReal)
            * ((Cv : ENNReal) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K) := by
            exact mul_le_mul_right h.frostmanConstIn (C₁ : ENNReal)
      _ = (C₁ : ENNReal) * (Cv : ENNReal)
            * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K := by ring

/-- **The ambient enlargement to `B₁`**, in the form the fine normalization uses it: reading a
Frostman constant at the unit ball rather than at a smaller body `K'` containing every member
costs exactly the volume ratio `|B₁| / |K'|`
(`ConvexSpaceBody.frostmanConstIn_ambient_mono`), and `hratio` bounds that ratio by `Cv`. -/
lemma frostmanConstIn_closedUnitBall_le_of_ambient
    {ι : Type*} {u : Finset ι} {𝕎 : ι → ShadedBody E} {K' : ConvexSpaceBody E} {Cv : NNReal}
    (hK' : K' ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
    (hK'vol : volume K'.carrier ≠ 0)
    (hWK' : ∀ i ∈ u, (𝕎 i).toConvexSpaceBody ≤ K')
    (hratio : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      ≤ (Cv : ENNReal) * volume K'.carrier) :
    frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
      ≤ (Cv : ENNReal) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' := by
  have hmono := frostmanConstIn_ambient_mono hK' hK'vol hWK'
  have hK'voltop : volume K'.carrier ≠ ⊤ := K'.isCompact'.measure_ne_top
  have hdiv : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      / volume K'.carrier ≤ (Cv : ENNReal) := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl hK'vol) (Or.inl hK'voltop)]
    exact hratio
  calc
    frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
        ≤ volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
          / volume K'.carrier
          * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' := hmono
    _ ≤ (Cv : ENNReal) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' := by
          gcongr

-- All `δ`-tubes are isometric, so their affine images under one map have a common volume: this
-- is the hypothesis `hcommon` of `Tube.exists_comparableReplacement_affine`.
lemma volume_affineImage_carrier_eq {δ : NNReal} (S S' : ShadedTube δ E)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) (hemb : MeasurableEmbedding L) :
    volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
      = volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier := by
  change volume (L.toAffineMap '' S.carrier) = volume (L.toAffineMap '' S'.carrier)
  rw [Kakeya.volume_affineImage L S.carrier, Kakeya.volume_affineImage L S'.carrier]
  rw [_root_.Tube.volume_carrier_eq_volume_carrier S.toTube S'.toTube]

-- An affine equivalence multiplies carrier and shade by the same Jacobian, so a two-sided
-- density bracket is carried over verbatim: the hypothesis `hZ` of
-- `Tube.exists_comparableReplacement_affine`, read at the common volume of the images.
lemma affineImage_shade_bounds {δ : NNReal} (S S' : ShadedTube δ E)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) (hemb : MeasurableEmbedding L)
    {Λ : NNReal} {μ₀ : ENNReal}
    (h₁ : (Λ : ENNReal)⁻¹ * μ₀ * volume S.carrier ≤ volume S.shade)
    (h₂ : volume S.shade ≤ (Λ : ENNReal) * μ₀ * volume S.carrier) :
    (Λ : ENNReal)⁻¹ * μ₀
          * volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
        ≤ volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).shade ∧
      volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).shade
        ≤ (Λ : ENNReal) * μ₀
          * volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier := by
  -- An affine equivalence multiplies every volume by the same Jacobian `J`, so the two-sided
  -- density bracket carried over from `h₁` and `h₂` is unchanged.
  let J : ENNReal := ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)|
  have hprimed : volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
      = volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier :=
    (volume_affineImage_carrier_eq S S' L hcont hemb).symm
  have hcarrier : volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
      = J * volume S.carrier := by
    dsimp [J]
    change volume (L.toAffineMap '' S.carrier) = J * volume S.carrier
    exact Kakeya.volume_affineImage L S.carrier
  have hshade : volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).shade
      = J * volume S.shade := by
    dsimp [J]
    change volume (L.toAffineMap '' S.shade) = J * volume S.shade
    exact Kakeya.volume_affineImage L S.shade
  constructor
  · rw [hprimed, hcarrier, hshade]
    calc
      (Λ : ENNReal)⁻¹ * μ₀ * (J * volume S.carrier)
          = J * ((Λ : ENNReal)⁻¹ * μ₀ * volume S.carrier) := by ring
      _ ≤ J * volume S.shade := by
            exact mul_le_mul (le_rfl : J ≤ J) h₁ (by positivity) (by positivity)
  · rw [hshade, hprimed, hcarrier]
    calc
      J * volume S.shade ≤ J * ((Λ : ENNReal) * μ₀ * volume S.carrier) := by
            exact mul_le_mul (le_rfl : J ≤ J) h₂ (by positivity) (by positivity)
      _ = (Λ : ENNReal) * μ₀ * (J * volume S.carrier) := by ring

-- A `δ`-tube of positive scale has positive volume (`Tube.le_volume`), and an affine
-- equivalence has nonzero Jacobian: the hypothesis `hW` of
-- `Tube.exists_comparableReplacement_affine`.
lemma volume_affineImage_carrier_pos [Nontrivial E] {δ : NNReal} (hδ : 0 < δ)
    (S : ShadedTube δ E) (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L)
    (hemb : MeasurableEmbedding L) :
    0 < volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier := by
  have hδpos : 0 < (δ : ENNReal) := ENNReal.coe_pos.mpr hδ
  have hpow : 0 < (δ : ENNReal) ^ (Module.finrank ℝ E - 1) := by positivity
  have hc : (0 : ENNReal) < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) :=
    ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
  have hSpos : 0 < volume (S.toShadedBody).carrier := by
    calc
      0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * (δ : ENNReal) ^
          (Module.finrank ℝ E - 1) := by positivity
      _ ≤ volume (S.toShadedBody).carrier := by simpa using (_root_.Tube.le_volume S.toTube)
  have hdet : LinearMap.det (L.linear : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' L.linear).ne_zero
  have hJ : 0 < ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| := by
    rw [ENNReal.ofReal_pos]
    exact abs_pos.mpr hdet
  change 0 < volume (L.toAffineMap '' (S.toShadedBody).carrier)
  rw [Kakeya.volume_affineImage]
  positivity

/-- **`Tube.rescale_outer_tube` with the image-core length freed to the radius `R`.**

`Tube.rescale_outer_tube` consumes its packaged `Tube.IsNormalizationDistortion` at exactly two
fields: `image_subset_cthickening`, which is proved unconditionally by
`Tube.normalization_image_subset_cthickening` (no containment hypothesis at all), and
`dist_le_C`, which it uses only to run the chain
`dist (Ψ x) (Ψ y) = dist (Φ x) (Φ y) / (4 R) ≤ C_N / (4 R) ≤ R / (4 R) = 1/4 ≤ 1`.

So the packaged structure is stronger than the route needs: what the route needs is
`dist (Φ x) (Φ y) ≤ R`, and the packaged field supplies that only via `C_N ≤ R`.  The
distinction is invisible at `R = C_N` but decisive over a dilate: for `T ⊆ c · T₀` the image
core has length at most `√(1 + 4 c²)`, which exceeds the hardwired `C_N = 64` once
`c > 31.99…`, while the dilated instance runs at `R = (1 + 2 c) C_N` and so satisfies the
relaxed hypothesis for *every* `c`.  Freeing the field here is therefore what makes
`Kakeya.ml1Boot.exists_fineNormalization_dilate` provable at an unbounded dilation ratio.

`Kakeya/Tube/Rescale.lean` is not ours to extend, so this is the local restatement; the proof is
that of `Tube.rescale_outer_tube` with the two `hdist` projections replaced by `hcth` and
`hlen`. -/
private lemma rescale_outer_tube_of_dist_le [Nontrivial E] {θ ρ σ : NNReal} {R : ℝ}
    (hsit : _root_.Tube.IsRescalingSituation θ ρ σ R 3) (hn : Module.finrank ℝ E = 3)
    (hR : 0 < R) (hρσ : (ρ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (T₀ : Tube θ E) (T : Tube ρ E)
    (hcth : T₀.normalization '' T.carrier ⊆
      Metric.cthickening
        ((_root_.Tube.normalization.C (Module.finrank ℝ E) : ℝ) * ((ρ : ℝ) / (θ : ℝ)))
        (segment ℝ (T₀.normalization T.x) (T₀.normalization T.y)))
    (hlen : dist (T₀.normalization T.x) (T₀.normalization T.y) ≤ R)
    (hball : T₀.normalization '' T.carrier ⊆ Metric.closedBall T₀.x R)
    (hxy : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y) :
    T₀.rescaleMap R '' T.carrier ⊆ (_root_.Tube.centredExtension σ hxy).carrier ∧
      (_root_.Tube.centredExtension σ hxy).carrier ⊆ Metric.closedBall (0 : E) 1 ∧
      volume (_root_.Tube.centredExtension σ hxy).carrier
        ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (T₀.rescaleMap R '' T.carrier) := by
  let τ : ℝ := (ρ : ℝ) / (θ : ℝ)
  let C0 : ℝ := (_root_.Tube.normalization.C (Module.finrank ℝ E) : ℝ)
  have hθpos : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hsit.pos_ambient
  have hρ_nonneg : 0 ≤ τ := by
    dsimp [τ]
    exact div_nonneg (by positivity) (le_of_lt hθpos)
  have h4Rpos : (0 : ℝ) < 4 * R := by positivity
  have h4R0 : (4 : ℝ) * R ≠ 0 := ne_of_gt h4Rpos
  have hC0_nonneg : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hC0_le_R : C0 ≤ R := by
    dsimp [C0]
    simpa [hn] using hsit.normalizationConst_le_radius
  have hRdiv : R / (4 * R) = (1 : ℝ) / 4 := by
    field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
  -- (1) Thickness: `Ψ(T) ⊆ V`.
  have hth0 : T₀.rescaleMap R '' T.carrier ⊆
      Metric.cthickening (C0 * τ / (4 * R))
        (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)) := by
    exact _root_.Tube.rescaleMap_image_subset_cthickening T₀ hR (r := C0 * τ)
      (A := T.carrier) (p := T.x) (q := T.y)
      (mul_nonneg hC0_nonneg hρ_nonneg) hcth
  have hrad : C0 * τ / (4 * R) ≤ (σ : ℝ) := by
    have h1 : C0 * τ ≤ R * τ := mul_le_mul_of_nonneg_right hC0_le_R hρ_nonneg
    have h2 : C0 * τ / (4 * R) ≤ (R * τ) / (4 * R) := by
      exact div_le_div_of_nonneg_right h1 (le_of_lt h4Rpos)
    have h3 : (R * τ) / (4 * R) = τ / 4 := by
      field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
    have h4 : τ / 4 ≤ (σ : ℝ) := by
      have : τ ≤ 4 * (σ : ℝ) := by simpa [τ] using hρσ
      linarith
    calc
      C0 * τ / (4 * R) ≤ (R * τ) / (4 * R) := h2
      _ = τ / 4 := h3
      _ ≤ (σ : ℝ) := h4
  have hth1 : T₀.rescaleMap R '' T.carrier ⊆
      Metric.cthickening (σ : ℝ) (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)) := by
    exact hth0.trans (Metric.cthickening_mono hrad
      (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)))
  have hlen1 : dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y) ≤ 1 := by
    calc
      dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)
          = dist (T₀.normalization T.x) (T₀.normalization T.y) / (4 * R) := by
            simpa [τ, C0] using _root_.Tube.dist_rescaleMap T₀ hR T.x T.y
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hlen (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
      _ ≤ 1 := by norm_num
  have hth2 : T₀.rescaleMap R '' T.carrier ⊆ (_root_.Tube.centredExtension σ hxy).carrier := by
    exact hth1.trans (_root_.Tube.cthickening_subset_centredExtension hxy hlen1)
  -- (2) Position: `V ⊆ B̄(0,1)`.
  have hpx : dist (T₀.normalization T.x) T₀.x ≤ R := by
    have hmem : T₀.normalization T.x ∈ T₀.normalization '' T.carrier :=
      ⟨T.x, _root_.Tube.x_mem_carrier T, rfl⟩
    exact Metric.mem_closedBall.mp (hball hmem)
  have hpy : dist (T₀.normalization T.y) T₀.x ≤ R := by
    have hmem : T₀.normalization T.y ∈ T₀.normalization '' T.carrier :=
      ⟨T.y, _root_.Tube.y_mem_carrier T, rfl⟩
    exact Metric.mem_closedBall.mp (hball hmem)
  have hpx0 : dist (T₀.rescaleMap R T.x) (0 : E) ≤ 1 / 4 := by
    calc
      dist (T₀.rescaleMap R T.x) (0 : E)
          = dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T₀.x) := by
            rw [← _root_.Tube.rescaleMap_apply_x]
      _ = dist (T₀.normalization T.x) (T₀.normalization T₀.x) / (4 * R) :=
            _root_.Tube.dist_rescaleMap T₀ hR T.x T₀.x
      _ = dist (T₀.normalization T.x) T₀.x / (4 * R) := by rw [_root_.Tube.normalization_apply_x]
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hpx (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
  have hpy0 : dist (T₀.rescaleMap R T.y) (0 : E) ≤ 1 / 4 := by
    calc
      dist (T₀.rescaleMap R T.y) (0 : E)
          = dist (T₀.rescaleMap R T.y) (T₀.rescaleMap R T₀.x) := by
            rw [← _root_.Tube.rescaleMap_apply_x]
      _ = dist (T₀.normalization T.y) (T₀.normalization T₀.x) / (4 * R) :=
            _root_.Tube.dist_rescaleMap T₀ hR T.y T₀.x
      _ = dist (T₀.normalization T.y) T₀.x / (4 * R) := by rw [_root_.Tube.normalization_apply_x]
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hpy (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
  have hpos : (_root_.Tube.centredExtension σ hxy).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    exact _root_.Tube.centredExtension_subset_closedBall hxy hpx0 hpy0 hsit.out_le_quarter
  -- (3) Volume: `|V| ≤ (4R)^6 |W|`.
  have hvol0 : volume (_root_.Tube.centredExtension σ hxy).carrier
      ≤ ENNReal.ofReal
            ((_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3)
          * volume (T₀.rescaleMap R '' T.carrier) := by
    simpa [hn] using _root_.Tube.volume_centredExtension_le_mul_volume_rescale_image
      (n := 3) hsit hR T₀ T hxy
  have hC64R : (64 : ℝ) ≤ R := by
    have hC : (64 : ℝ) ≤ (_root_.Tube.normalization.C 3 : ℝ) := by
      norm_num [_root_.Tube.normalization.C]
    exact le_trans hC hsit.normalizationConst_le_radius
  have hbig : (256 : ℝ) ≤ 4 * R := by linarith
  have hpow256 : (256 : ℝ) ^ 3 ≤ (4 * R) ^ 3 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 256) hbig 3
  have h12 : (12 : ℝ) ≤ (4 * R) ^ 3 := by nlinarith
  have hcoef : (_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3
      ≤ (4 * R) ^ 6 := by
    have hvp12 : (_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) ≤ 12 :=
      _root_.Tube.volume_ratio_three_le_twelve
    calc
      (_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3
          ≤ 12 * (4 * R) ^ 3 := by gcongr
      _ ≤ (4 * R) ^ 3 * (4 * R) ^ 3 := by gcongr
      _ = (4 * R) ^ 6 := by ring
  have hvol : volume (_root_.Tube.centredExtension σ hxy).carrier
      ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (T₀.rescaleMap R '' T.carrier) := by
    exact hvol0.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl)
  exact ⟨hth2, hpos, hvol⟩

/-- **The selection constant of the downstairs route is dominated by the normalization loss, at a
free normalized radius `R` and a free tilt `κ`.**

`Kakeya.ml1Boot.fineNormalize_C_dominates` is the same statement hardwired to the undilated
instance `(R, κ) = (C_N, 2)`, and the dilated half of the normalization runs at
`(R, κ) = ((1 + 2 c) C_N, max 2 (2 c))`, so it needs the parametric form.  The coupling
hypothesis `κ + 2 ≤ R` holds at both instances — `4 ≤ 64` and `2 c + 4 ≤ 64 + 128 c` — and is
what keeps the selection ratio `4 (κ + 2) R C_n` below `4 R² C_n`.

The third clause carries a factor `125` that the undilated form does not.  It is the price of
descending the ambient volume comparison from `c · T_τ` to the sub-body `K`: the `c`-dilate has
volume `c³ |T_τ|`, and `c ≥ 1/5` — forced, not assumed, since a `δ`-tube fits inside `c · T_τ`
only if `1 ≤ c + 4 c τ` (`Kakeya.ml1Boot.volume_ambient_le_mul_volume_dilate`) — bounds `c⁻³` by
`125`.  There is room for it: the comparison reduces to `125 ≤ 4 ^ 24 R ^ 12`. -/
private lemma fineNormalize_C_dominates_gen {R κ c₁ : NNReal}
    (hCR : _root_.Tube.normalization.C 3 ≤ R) (hκR : κ + 2 ≤ R)
    (hc₁ : c₁ = _root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3)) :
    c₁ ≤ fineNormalize.C R κ ∧
      ((4 * R) ^ 6 : NNReal) * c₁ ≤ fineNormalize.C R κ ∧
      (125 : NNReal) * ((4 * R) ^ 12 : NNReal) * c₁ ≤ fineNormalize.C R κ := by
  let ratio : ℝ := 4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3
  let D : NNReal := (Kakeya.Tube.tubeOverlapCoreClose.C 3).toNNReal
  let u : NNReal := 4 * (κ + 2) * R * D
  have hR1 : (1 : NNReal) ≤ R := le_trans (_root_.Tube.normalization.one_le_C 3) hCR
  have hκ1 : (1 : NNReal) ≤ κ + 2 := by
    exact le_trans (by norm_num : (1 : NNReal) ≤ 2)
      (le_add_of_nonneg_left (by positivity : (0 : NNReal) ≤ κ))
  have hD0 : (0 : ℝ) ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 :=
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < (1 : ℝ))
      (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3))
  have hD1 : (1 : NNReal) ≤ D := by
    dsimp [D]; rw [← NNReal.coe_le_coe, Real.toNNReal_of_nonneg hD0]
    exact le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3)
  have hratio0 : (0 : ℝ) ≤ ratio := by
    dsimp [ratio]
    positivity
  have hu_re : ratio = (u : ℝ) := by
    dsimp [u, ratio, D]
    norm_num
    exact Or.inl hD0
  have hu : ratio.toNNReal = u := by
    apply NNReal.coe_injective
    rw [Real.toNNReal_of_nonneg hratio0]
    exact hu_re
  have hu1 : (1 : NNReal) ≤ u :=
    one_le_mul (one_le_mul (one_le_mul (by norm_num : (1 : NNReal) ≤ 4) hκ1) hR1) hD1
  have hu6 : u ^ 6 ≤ u ^ 12 := pow_le_pow_right₀ hu1 (by norm_num)
  have hule : u ≤ 4 * R ^ 2 * D := by
    dsimp [u]
    calc
      4 * (κ + 2) * R * D
          ≤ 4 * R * R * D := by
            exact mul_le_mul
              (mul_le_mul (mul_le_mul le_rfl hκR (by positivity) (by positivity))
                le_rfl (by positivity) (by positivity))
              le_rfl (by positivity) (by positivity)
      _ = 4 * R ^ 2 * D := by ring
  have hu12' : 125 * u ^ 12 ≤ ((4 * R) ^ 6) ^ 6 * D ^ 12 := by
    calc
      125 * u ^ 12 ≤ 125 * (4 * R ^ 2 * D) ^ 12 := by
            exact mul_le_mul le_rfl (pow_le_pow_left₀ (by positivity : (0 : NNReal) ≤ u) hule 12)
              (by positivity) (by positivity)
      _ = 125 * 4 ^ 12 * R ^ 24 * D ^ 12 := by
            ring_nf
      _ ≤ (4 : NNReal) ^ 36 * R ^ 36 * D ^ 12 := by
            exact mul_le_mul
              (mul_le_mul (by norm_num : (125 * 4 ^ 12 : NNReal) ≤ 4 ^ 36)
                (pow_le_pow_right₀ hR1 (by norm_num)) (by positivity) (by positivity))
              le_rfl (by positivity) (by positivity)
      _ = ((4 * R) ^ 6) ^ 6 * D ^ 12 := by
            ring_nf
  have hu12 : u ^ 12 ≤ ((4 * R) ^ 6) ^ 6 * D ^ 12 := by
    exact le_trans
      (le_mul_of_one_le_left (by positivity) (by norm_num : (1 : NNReal) ≤ 125))
      hu12'
  have hbase : (1 : NNReal) ≤ 4 * R := one_le_mul (by norm_num : (1 : NNReal) ≤ 4) hR1
  have hpw6 : (4 * R) ^ 6 ≤ (4 * R) ^ 12 := pow_le_pow_right₀ hbase (by norm_num)
  have hkey : c₁ ≤ _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
    rw [hc₁]
    unfold _root_.Tube.essDistinctTubesInSelfDilate.C
      _root_.Tube.essDistinctTubesInSelfDilate.thinC
      _root_.Tube.essDistinctTubesInSelfDilate.fatC
      _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
    set A : NNReal :=
      24 * (2 ^ (3 - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C (3 - 1)) ^ 2
        * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * 3 - 1))⁻¹
        * (32 * (3 : NNReal)) ^ (2 * 3 - 1) with hA
    set B : NNReal := 6 ^ (2 * 3) * (Tube.card_le_of_EssDistinct.C 3).toNNReal with hB
    calc
      A * ratio.toNNReal ^ (2 * 3) + B * ratio.toNNReal ^ (4 * 3)
          = A * u ^ 6 + B * u ^ 12 := by rw [hu]
      _ ≤ A * u ^ 12 + B * u ^ 12 := by
            exact add_le_add (mul_le_mul le_rfl hu6 (by positivity) (by positivity)) le_rfl
      _ = (A + B) * u ^ 12 := by ring
      _ ≤ (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := by
            exact mul_le_mul le_rfl hu12 (by positivity) (by positivity)
      _ ≤ 1 + (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := le_add_self
      _ = _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
            rw [hA, hB]
            unfold _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
            norm_num
            ring
  have hkey125 : 125 * c₁ ≤ _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
    rw [hc₁]
    unfold _root_.Tube.essDistinctTubesInSelfDilate.C
      _root_.Tube.essDistinctTubesInSelfDilate.thinC
      _root_.Tube.essDistinctTubesInSelfDilate.fatC
      _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
    set A : NNReal :=
      24 * (2 ^ (3 - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C (3 - 1)) ^ 2
        * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * 3 - 1))⁻¹
        * (32 * (3 : NNReal)) ^ (2 * 3 - 1) with hA
    set B : NNReal := 6 ^ (2 * 3) * (Tube.card_le_of_EssDistinct.C 3).toNNReal with hB
    calc
      125 * (A * ratio.toNNReal ^ (2 * 3) + B * ratio.toNNReal ^ (4 * 3))
          = 125 * (A * u ^ 6 + B * u ^ 12) := by rw [hu]
      _ = 125 * (A * u ^ 6) + 125 * (B * u ^ 12) := by ring
      _ ≤ 125 * (A * u ^ 12) + 125 * (B * u ^ 12) := by
            exact add_le_add
              (mul_le_mul le_rfl (mul_le_mul le_rfl hu6 (by positivity) (by positivity))
                (by positivity) (by positivity))
              le_rfl
      _ = 125 * (A + B) * u ^ 12 := by ring
      _ = (A + B) * (125 * u ^ 12) := by ring
      _ ≤ (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := by
            exact mul_le_mul le_rfl hu12' (by positivity) (by positivity)
      _ ≤ 1 + (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := le_add_self
      _ = _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
            rw [hA, hB]
            unfold _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
            norm_num
            ring
  constructor
  · unfold fineNormalize.C
    rw [hc₁]
    exact le_add_self
  constructor
  · unfold fineNormalize.C
    exact le_trans
      (le_trans (mul_le_mul hpw6 le_rfl (by positivity) (by positivity))
        (mul_le_mul le_rfl hkey (by positivity) (by positivity)))
      le_self_add
  · unfold fineNormalize.C
    calc
      (125 : NNReal) * ((4 * R) ^ 12 : NNReal) * c₁
          = (4 * R) ^ 12 * (125 * c₁) := by ring
      _ ≤ (4 * R) ^ 12 * _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
            exact mul_le_mul le_rfl hkey125 (by positivity) (by positivity)
      _ ≤ (4 * R) ^ 12 * _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6)
            + _root_.Tube.essDistinctTubesInSelfDilate.C 3
                (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3) :=
            le_self_add

/-- **Normalizing a fine fibre to the unit ball, over an arbitrary ambient body** (blueprint
`lem:ml1bootFineNormalizeCore`).

This is the route shared by the two halves of the fine normalization, with the ambient body `P`
and the normalized ambient radius `R` left free.  Both halves are this lemma instantiated:
`Kakeya.ml1Boot.exists_fineNormalization` at `(P, R, κ) = (T_τ, C_N, 2)`, and
`Kakeya.ml1Boot.exists_fineNormalization_dilate` at
`(P, R, κ) = (K, (1 + 2 c) C_N, max 2 (2 c))` — see the "Not a corollary of the undilated half"
note at the latter for why neither is derivable from the other.

Everything the route needs from the ambient body is isolated into four hypotheses, and nothing
else here mentions `P`:

* `hsub`, the members sit in `P`;
* `hball`, the normalization `Φ_{T_τ}` carries `P` into `B̄(T_τ.x, R)` — this is what fixes `R`,
  and it is the *only* place the shape of `P` enters the geometry;
* `hlen`, each image core has length at most `R` — the relaxed form of
  `Tube.IsNormalizationDistortion.dist_le_C` discussed at
  `Kakeya.ml1Boot.rescale_outer_tube_of_dist_le`;
* `hperp`, each member is tilted against the axis of `T_τ` by at most `κ τ`.

The remaining two, `hPvol` and `hratio`, are the ambient enlargement to `B₁`: `Cw` is the loss
of replacing the ambient body by the unit ball, and it is the *only* route by which a
volume-ratio parameter such as the `M` of the dilated half can reach the Frostman clause.  The
constants are returned raw — the selection constant `C₁`, the comparability constant `(4 R) ^ 6`
and `Cw`, in the combinations the four clauses actually pay — so that each instance does its own
domination against `Kakeya.ml1Boot.fineNormalize.C R κ`.

The output scale is `Kakeya.ml1Boot.fineScale δ τ` and not the bare ratio `δ / τ`; with `δ / τ`
this statement is false at both instances, refuted by
`Kakeya.ml1Boot.not_exists_fineNormalization` and
`Kakeya.ml1Boot.not_exists_fineNormalization_dilate`.

## The construction-visibility clauses

The last four clauses of the conclusion are not part of the blueprint lemma.  They expose the
data the route already builds, so that a consumer can see *which* family `V` is rather than only
that one exists.  Writing `Ψ = Tube.rescaleMap T_τ R` for the normalization-and-homothety of the
proof, they say that the intermediate family — the `Ψ`-image of the input — sits inside the
output with the same shade and comparable volume, and that `Ψ` carries the ambient body into
`B(0, 1/4)`:

* `Ψ(T i) ⊆ V i` for every `i ∈ u`;
* `(V i).shade = Ψ((T i).shade)` for every `i ∈ u`;
* `|V i| ≤ (4 R) ^ 6 |Ψ(T i)|` for every `i ∈ u`;
* `Ψ(P) ⊆ B(0, 1/4)`.

They cost nothing: they are the local hypotheses `hsub'`, `hshade`, `hvol` and `hK'c` that the
selection package `Tube.exists_comparableReplacement_affine` is fed with anyway, restated
through `hWcarrier` in terms of `Ψ` rather than of the local abbreviation `𝕎`.

What the proof does **not** have, and so what is deliberately absent here, is the `hdilate`
clause of `ConvexSpaceBody.frostmanConstIn_ge_of_comparable` — for every `K' ≤ K` a `L ≤ K`
with `K' ≤ L`, `|L| ≤ C |K'|` and `V i ≤ L` whenever `Ψ(T i) ≤ K'`.  `Tube.exists_comparableReplacement_affine`
never forms such an `L`; its Frostman item is the one-sided
`Tube.comparableTransport_oneSided`, which needs only `Ψ(T i) ⊆ V i ⊆ K` and the volume
bracket.  Also absent is any clause about indices outside `u`: `hsub`, `hlen` and `hperp` are
hypothesised on `u` alone, so nothing at all is known about `V i` for `i ∉ u`, even though `V`
is a total function. -/
theorem exists_fineNormalization_core [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δ τ : NNReal} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτ1 : τ ≤ 1)
    {Λ : NNReal} (hΛ : 1 ≤ Λ) {μ₀ : ENNReal} (hμ₀ : 0 < μ₀)
    {ι : Type*} {u : Finset ι} (Tτ : Tube τ E) (T : ι → ShadedTube δ E)
    (P : ConvexSpaceBody E) {R κ Cw : NNReal}
    (hR : _root_.Tube.normalization.C 3 ≤ R)
    (hu : u.Nonempty)
    (hsub : ∀ i ∈ u, (T i).carrier ⊆ P.carrier)
    (hball : Tτ.normalization '' P.carrier ⊆ Metric.closedBall Tτ.x (R : ℝ))
    (hlen : ∀ i ∈ u,
      dist (Tτ.normalization (T i).x) (Tτ.normalization (T i).y) ≤ (R : ℝ))
    (hperp : ∀ i ∈ u, ‖(T i).toTube.direction
        - (inner ℝ Tτ.direction (T i).toTube.direction : ℝ) • Tτ.direction‖
      ≤ (κ : ℝ) * (τ : ℝ))
    (hPvol : volume P.carrier ≠ 0)
    (hratio : volume (Metric.closedBall (0 : E) 1)
      ≤ (Cw : ENNReal) * volume (Tτ.rescaleMap (R : ℝ) '' P.carrier))
    (hED : (u : Set ι).Pairwise fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
    (hdens : ∀ i ∈ u, (Λ : ENNReal)⁻¹ * μ₀ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ (Λ : ENNReal) * μ₀ * volume (T i).carrier) :
    ∃ u' ⊆ u, u'.Nonempty ∧ ∃ V : ι → ShadedTube (fineScale δ τ) E,
      (u' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
        (∀ i ∈ u', (V i).carrier ⊆ Metric.closedBall 0 1) ∧
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * ((κ : ℝ) + 2) * (R : ℝ)
                * Kakeya.Tube.tubeOverlapCoreClose.C 3) : ENNReal)
            * (Λ : ENNReal) ^ 2
            * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) ∧
        (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal)
          ≤ (((4 * R) ^ 6 : NNReal) : ENNReal)
            * (_root_.Tube.essDistinctTubesInSelfDilate.C 3
                (4 * ((κ : ℝ) + 2) * (R : ℝ)
                  * Kakeya.Tube.tubeOverlapCoreClose.C 3) : ENNReal)
            * (Λ : ENNReal) ^ 2
            * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ENNReal) ∧
        frostmanConstIn u' (fun i => (V i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall
          ≤ (_root_.Tube.essDistinctTubesInSelfDilate.C 3
                (4 * ((κ : ℝ) + 2) * (R : ℝ)
                  * Kakeya.Tube.tubeOverlapCoreClose.C 3) : ENNReal)
            * (((4 * R) ^ 6 : NNReal) : ENNReal) * (Cw : ENNReal)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P ∧
        -- the construction-visibility clauses: `V` is comparable to the image of `T` under the
        -- explicit rescaling map `Ψ = Tube.rescaleMap Tτ R`
        (∀ i ∈ u, Tτ.rescaleMap (R : ℝ) '' (T i).carrier ⊆ (V i).carrier) ∧
        (∀ i ∈ u, (V i).shade = Tτ.rescaleMap (R : ℝ) '' (T i).shade) ∧
        (∀ i ∈ u, volume (V i).carrier
          ≤ (((4 * R) ^ 6 : NNReal) : ENNReal)
            * volume (Tτ.rescaleMap (R : ℝ) '' (T i).carrier)) ∧
        Tτ.rescaleMap (R : ℝ) '' P.carrier ⊆ Metric.closedBall (0 : E) (1 / 4) := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  have hτ0 : 0 < τ := lt_of_lt_of_le hδ hδτ
  let i₀ : ι := Classical.choose hu
  have hi₀ : i₀ ∈ u := Classical.choose_spec hu
  have hδτ0 : 0 < (δ / τ : NNReal) := by
    rw [← NNReal.coe_lt_coe]
    rw [NNReal.coe_div]
    exact div_pos (by exact_mod_cast hδ) (by exact_mod_cast hτ0)
  have hpos : 0 < fineScale δ τ := by
    dsimp [fineScale]
    exact lt_min hδτ0 (by norm_num)
  have hquarter : (fineScale δ τ : ℝ) ≤ 1 / 4 := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).2.1
  have hratioσ : (fineScale δ τ : ℝ) ≤ (δ : ℝ) / (τ : ℝ) := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).1
  have hρσ : (δ : ℝ) / (τ : ℝ) ≤ 4 * (fineScale δ τ : ℝ) := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).2.2
  have hR1n : (1 : NNReal) ≤ R := le_trans (_root_.Tube.normalization.one_le_C 3) hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1n
  have hR0 : 0 < (R : ℝ) := lt_of_lt_of_le zero_lt_one hR1
  have hsit : _root_.Tube.IsRescalingSituation τ δ (fineScale δ τ) (R : ℝ) 3 :=
    ⟨hτ0, hδτ, hτ1, hpos, hquarter, hratioσ, by exact_mod_cast hR⟩
  obtain ⟨L, hL⟩ := _root_.Tube.exists_rescaleEquiv hτ0 hR0 Tτ
  have hcont : Continuous L := AffineEquiv.continuous_of_finiteDimensional L
  have hemb : MeasurableEmbedding L :=
    (AffineEquiv.toContinuousAffineEquiv L).toHomeomorph.measurableEmbedding
  have hxy : ∀ i : ι, Tτ.rescaleMap (R : ℝ) (T i).x ≠ Tτ.rescaleMap (R : ℝ) (T i).y := by
    intro i h
    rw [← hL] at h
    exact (fun hne => hne (L.injective h)) (fun hxy => by
      have := (T i).toTube.dist_eq_one
      rw [hxy] at this
      simp at this)
  set 𝕎 : ι → ShadedBody E := fun i => ((T i).toShadedBody).affineImage L.toAffineMap hcont hemb
  set 𝕍 : ι → ShadedTube (fineScale δ τ) E := fun i =>
    { toTube := _root_.Tube.centredExtension (fineScale δ τ) (hxy i)
      shade := (𝕎 i).shade ∩ (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).carrier
      measurableSet_shade :=
        (𝕎 i).measurableSet_shade.inter
          (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).isCompact.measurableSet
      shade_subset := Set.inter_subset_right }
  have hballi : ∀ i ∈ u, Tτ.normalization '' (T i).carrier ⊆ Metric.closedBall Tτ.x (R : ℝ) := by
    intro i hi
    exact (Set.image_mono (hsub i hi)).trans hball
  have houter := fun i hi => rescale_outer_tube_of_dist_le
    (hsit := hsit) (hn := hdim) (hR := hR0) (hρσ := hρσ) (T₀ := Tτ)
    (T := (T i).toTube)
    (hcth := _root_.Tube.normalization_image_subset_cthickening hτ0 hτ1 Tτ (T i).toTube)
    (hlen := hlen i hi) (hball := hballi i hi) (hxy := hxy i)
  have hofR : ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) = (((4 * R) ^ 6 : NNReal) : ENNReal) := by
    have h4R : ENNReal.ofReal (4 * (R : ℝ)) = ((4 * R : NNReal) : ENNReal) := by
      rw [show (4 : ℝ) * (R : ℝ) = ((4 * R : NNReal) : ℝ) by
        rw [NNReal.coe_mul]
        norm_num]
      rw [ENNReal.ofReal_coe_nnreal]
    have hRnonneg : (0 : ℝ) ≤ 4 * (R : ℝ) := by positivity
    calc
      ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) = (ENNReal.ofReal (4 * (R : ℝ))) ^ 6 := by
            rw [ENNReal.ofReal_pow hRnonneg]
      _ = ((4 * R : NNReal) : ENNReal) ^ 6 := by rw [h4R]
      _ = (((4 * R) ^ 6 : NNReal) : ENNReal) := by
            rw [ENNReal.coe_pow]
  have hWcarrier : ∀ i ∈ u, (𝕎 i).carrier = Tτ.rescaleMap (R : ℝ) '' (T i).carrier := by
    intro i hi
    dsimp [𝕎]
    change L.toAffineMap '' (T i).carrier = Tτ.rescaleMap (R : ℝ) '' (T i).carrier
    rw [← hL]
  have hsub' : ∀ i ∈ u, (𝕎 i).carrier ⊆ (𝕍 i).carrier := by
    intro i hi
    rw [hWcarrier i hi]
    simpa [𝕍] using (houter i hi).1
  have h𝕍ball : ∀ i ∈ u, (𝕍 i).toTube.carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    simpa [𝕍] using (houter i hi).2.1
  have hshade : ∀ i ∈ u, (𝕍 i).shade = (𝕎 i).shade := by
    intro i hi
    dsimp [𝕍]
    exact (Set.inter_eq_left).mpr ((𝕎 i).shade_subset.trans (hsub' i hi))
  have hCv : 1 ≤ (4 * R) ^ 6 := by
    exact one_le_pow₀ (one_le_mul (by norm_num) hR1n)
  have hVK : ∀ i ∈ u,
      (𝕍 i).toConvexSpaceBody ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    intro i hi
    change (𝕍 i).carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    simpa [𝕍] using h𝕍ball i hi
  let c' : ℝ := 4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3
  have hc'1 : (1 : ℝ) ≤ c' := by
    dsimp [c']
    have hκ0 : (0 : ℝ) ≤ (κ : ℝ) := NNReal.coe_nonneg κ
    have hRgr : (1 : ℝ) ≤ (R : ℝ) := hR1
    have hCnR : (1 : ℝ) ≤ (Kakeya.Tube.tubeOverlapCoreClose.C 3 : ℝ) := by
      exact_mod_cast (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3))
    have hk : (1 : ℝ) ≤ 4 * ((κ : ℝ) + 2) := by
      nlinarith
    have hk0 : (0 : ℝ) ≤ 4 * ((κ : ℝ) + 2) := le_trans zero_le_one hk
    have hb1 : (1 : ℝ) ≤ (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := by
              exact mul_le_mul hRgr hCnR (by norm_num) (by positivity)
    have hb10 : (0 : ℝ) ≤ (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := le_trans zero_le_one hb1
    calc
      1 ≤ 1 * 1 := by norm_num
      _ ≤ (4 * ((κ : ℝ) + 2)) * ((R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3) := by
            exact mul_le_mul hk hb1 (by positivity) hk0
      _ = 4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := by ring
  let c₁ : NNReal := _root_.Tube.essDistinctTubesInSelfDilate.C 3
    (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3)
  have hc₁ : c₁ = _root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3) := by
    rfl
  have hC₁ : (1 : NNReal) ≤ c₁ := by
    let 𝕋 : ι → Tube δ E := fun i => (T i).toTube
    have hpw₀ : (({i₀} : Finset ι) : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (𝕋 i).carrier (𝕋 j).carrier) := by
      simp
    have hsub₀ : ∀ j ∈ ({i₀} : Finset ι), (𝕋 j).carrier
        ⊆ (Kakeya.Tube.dilate (𝕋 i₀) c').carrier := by
      intro j hj
      have hji : j = i₀ := by simpa using hj
      subst j
      exact _root_.Tube.subset_dilate (𝕋 i₀) hc'1
    have hcount : (({i₀} : Finset ι).card : ENNReal)
        ≤ (_root_.Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) c' : ENNReal) :=
      _root_.Tube.essDistinctTubesInSelfDilate hc'1 hδ (le_trans hδτ hτ1 : δ ≤ 1) (𝕋 i₀)
        ({i₀} : Finset ι) 𝕋 hpw₀ hsub₀
    exact ENNReal.coe_le_coe.mp (by simpa [c₁, c', hdim] using hcount)
  have hVtube : ∀ i ∈ u, (𝕍 i).toTube = _root_.Tube.centredExtension (fineScale δ τ) (hxy i) := by
    intro i hi
    rfl
  have hvol : ∀ i ∈ u, volume (𝕍 i).carrier
      ≤ (((4 * R) ^ 6 : NNReal) : ENNReal) * volume (𝕎 i).carrier := by
    intro i hi
    calc
      volume (𝕍 i).carrier
          = volume (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).carrier := by
            simp [𝕍]
      _ ≤ ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) * volume (Tτ.rescaleMap (R : ℝ) '' (T i).carrier) :=
            (houter i hi).2.2
      _ = (((4 * R) ^ 6 : NNReal) : ENNReal) * volume (Tτ.rescaleMap (R : ℝ) '' (T i).carrier) := by
            rw [hofR]
      _ = (((4 * R) ^ 6 : NNReal) : ENNReal) * volume (𝕎 i).carrier := by
            rw [hWcarrier i hi]
  let W : ENNReal := volume (𝕎 i₀).carrier
  have hW : 0 < W := by
    dsimp [W]
    simpa [𝕎] using volume_affineImage_carrier_pos hδ (T i₀) L hcont hemb
  have hcommon : ∀ i ∈ u, volume (𝕎 i).carrier = W := by
    intro i hi
    dsimp [W]
    simpa [𝕎] using volume_affineImage_carrier_eq (T i) (T i₀) L hcont hemb
  have hZ : ∀ i ∈ u, (Λ : ENNReal)⁻¹ * μ₀ * W ≤ volume (𝕎 i).shade ∧
      volume (𝕎 i).shade ≤ (Λ : ENNReal) * μ₀ * W := by
    intro i hi
    have hz := affineImage_shade_bounds (S := T i) (S' := T i₀) L hcont hemb
      (hdens i hi).1 (hdens i hi).2
    dsimp [W, 𝕎] at hz ⊢
    exact hz
  let 𝕋 : ι → Tube δ E := fun i => (T i).toTube
  have himg : ∀ i ∈ u, (Tτ.rescaleMap (R : ℝ)) '' (T i).carrier ⊆ ((𝕍 i).toTube).carrier := by
    intro i hi
    simpa [𝕍] using (houter i hi).1
  have hpackage : _root_.Tube.IsComparableReplacementFree u 𝕎 𝕍
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) ((4 * R) ^ 6) Λ c₁ := by
    simpa [hc₁, hdim] using
      (_root_.Tube.exists_comparableReplacement_affine (n := 3) (R := (R : ℝ))
      (κ := ((κ : NNReal) : ℝ)) (s := u) hu hsit (by exact NNReal.coe_nonneg κ)
      hδ (le_trans hδτ hτ1 : δ ≤ 1) Tτ
      𝕋 hxy 𝕎 𝕍
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)) (C := (4 * R) ^ 6) (Λ := Λ)
      (W := W) (μ₀ := μ₀) hCv hΛ hW hμ₀ hcommon hVtube hperp
      (by simpa [𝕋] using hED) himg hshade hsub' hVK hvol hZ)
  let K' : ConvexSpaceBody E := (P).affineImage L.toAffineMap hcont
  have hK'c : K'.carrier ⊆ Metric.closedBall (0 : E) (1 / 4) := by
    rintro _ ⟨z, hzP, rfl⟩
    have hz : Tτ.normalization z ∈ Metric.closedBall Tτ.x (R : ℝ) := by
      exact (hball ⟨z, hzP, rfl⟩)
    have hdistz : dist (Tτ.normalization z) Tτ.x ≤ (R : ℝ) := Metric.mem_closedBall.mp hz
    have h4Rpos : (0 : ℝ) < 4 * (R : ℝ) := by positivity
    have h4R0 : (4 : ℝ) * (R : ℝ) ≠ 0 := ne_of_gt h4Rpos
    have hRdiv : (R : ℝ) / (4 * (R : ℝ)) = (1 : ℝ) / 4 := by
      field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
    rw [hL]
    calc
      dist (Tτ.rescaleMap (R : ℝ) z) (0 : E)
          = dist (Tτ.rescaleMap (R : ℝ) z) (Tτ.rescaleMap (R : ℝ) Tτ.x) := by
            rw [← _root_.Tube.rescaleMap_apply_x]
        _ = dist (Tτ.normalization z) (Tτ.normalization Tτ.x) / (4 * (R : ℝ)) :=
            _root_.Tube.dist_rescaleMap Tτ hR0 z Tτ.x
        _ = dist (Tτ.normalization z) Tτ.x / (4 * (R : ℝ)) := by
            rw [_root_.Tube.normalization_apply_x]
        _ ≤ (R : ℝ) / (4 * (R : ℝ)) := div_le_div_of_nonneg_right hdistz (le_of_lt h4Rpos)
        _ = (1 : ℝ) / 4 := hRdiv
        _ ≤ 1 / 4 := le_rfl
  have hK' : (K' : ConvexSpaceBody E) ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    change K'.carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    exact hK'c.trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hK'vol : volume K'.carrier ≠ 0 := by
    have h1 : volume ((P).affineImage L.toAffineMap hcont).carrier ≠ 0 := by
      rw [ConvexSpaceBody.volume_affineImage]
      have hA : ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| ≠ 0 := by
        exact (ENNReal.ofReal_eq_zero.not).mpr
          (not_le.mpr (abs_pos.mpr (LinearEquiv.isUnit_det' L.linear).ne_zero))
      have hB : volume P.carrier ≠ 0 := hPvol
      exact mul_ne_zero hA hB
    simpa [K'] using h1
  have hWK' : ∀ i ∈ u, (𝕎 i).toConvexSpaceBody ≤ K' := by
    intro i hi
    change (𝕎 i).carrier ⊆ K'.carrier
    rw [hWcarrier i hi]
    rw [← hL]
    exact Set.image_mono (hsub i hi)
  have hratio' : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      ≤ (Cw : ENNReal) * volume K'.carrier := by
    simpa [K', ← hL, ConvexSpaceBody.closedUnitBall_carrier] using hratio
  have hfrodsman : frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
      ≤ (Cw : ENNReal) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' :=
    frostmanConstIn_closedUnitBall_le_of_ambient (u := u) (𝕎 := 𝕎) (K' := K')
      (Cv := Cw) hK' hK'vol hWK' hratio'
  have hF_rel : frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K'
      = frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P := by
    have h := ConvexSpaceBody.frostmanConstIn_affineImage u (fun i => (T i).toConvexSpaceBody)
      P L hcont
    dsimp [𝕎, K']
    exact h
  obtain ⟨u', hu'sub, hu'ne, hVD, _hcard, hmult, hfull, hfrost⟩ :=
    of_comparableReplacementFree (u := u) (𝕎 := 𝕎) (𝕍 := 𝕍)
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)) (Cv := (4 * R) ^ 6)
      (Λ := Λ) (C₁ := c₁) hΛ hCv hC₁ hVK hpackage
  refine ⟨u', hu'sub, hu'ne, 𝕍, ?_⟩
  constructor
  · simpa [𝕍] using hVD
  constructor
  · intro i hi
    simpa [𝕍] using h𝕍ball i (hu'sub hi)
  constructor
  · calc
      ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          = ShadedBody.multiplicity u 𝕎 := by
            simpa [𝕎] using (ShadedBody.multiplicity_affineImage u
              (fun i => (T i).toShadedBody) L hcont hemb).symm
      _ ≤ (c₁ : ENNReal) * (Λ : ENNReal) ^ 2
          * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := hmult
  constructor
  · calc
      (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal)
          = (ShadedBody.fullness u 𝕎 : ENNReal) := by
            simpa [𝕎] using (ShadedBody.fullness_affineImage u
              (fun i => (T i).toShadedBody) L hcont hemb).symm
      _ ≤ (((4 * R) ^ 6 : NNReal) : ENNReal) * (c₁ : ENNReal) * (Λ : ENNReal) ^ 2
          * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal) := hfull
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · calc
        frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody)
            (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
            ≤ (c₁ : ENNReal) * (((4 * R) ^ 6 : NNReal) : ENNReal)
              * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
                  (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by simpa using hfrost
        _ ≤ (c₁ : ENNReal) * (((4 * R) ^ 6 : NNReal) : ENNReal)
            * ((Cw : ENNReal)
              * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K') := by
              exact mul_le_mul_right hfrodsman ((c₁ : ENNReal) * (((4 * R) ^ 6 : NNReal) : ENNReal))
        _ = (c₁ : ENNReal) * (((4 * R) ^ 6 : NNReal) : ENNReal)
            * ((Cw : ENNReal)
              * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P) := by
              rw [hF_rel]
        _ = (c₁ : ENNReal) * (((4 * R) ^ 6 : NNReal) : ENNReal) * (Cw : ENNReal)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P := by ring
    · intro i hi
      rw [← hWcarrier i hi]
      exact hsub' i hi
    · intro i hi
      rw [hshade i hi]
      simp [𝕎, ← hL]
    · intro i hi
      simpa [hWcarrier i hi] using hvol i hi
    · simpa [K', ← hL] using hK'c

/-- **Normalizing the fine fibre to the unit ball** (blueprint `lem:ml1bootFineNormalize`).

Let `C = Kakeya.ml1Boot.fineNormalize.C C_N` be the normalization loss proper, `C_N` being
`Tube.normalization.C 3`, and let `0 < δ ≤ τ ≤ 1`.  Note that this is *not*
`Kakeya.ml1Boot.fineFactor.C`, which is `16 C`: the factor `16` belongs to
`Kakeya.ml1Boot.fine_genKF` and is not spent here.

Let `T_τ` be a `τ`-tube in `B₁ ⊆ ℝ³`, let `𝕌 = (T i)_{i ∈ u}` be a nonempty family of pairwise
essentially distinct shaded `δ`-tubes with `T i ⊆ T_τ`, and suppose the shading densities are
two-sidedly comparable to `μ₀`, with constant `Λ ≥ 1`.  Then there are a nonempty `u' ⊆ u` and
a family `Ṽ` of shaded `Kakeya.ml1Boot.fineScale δ τ`-tubes contained in `B₁` such that

* the tubes `(Ṽ i)_{i ∈ u'}` are pairwise essentially distinct;
* `μ(𝕌, Y) ≤ C Λ² μ(Ṽ, Z̃)`;
* `λ(𝕌, Y) ≤ C Λ² λ(Ṽ, Z̃)`, the blueprint's `λ(Ṽ, Z̃) ≥ (C Λ²)⁻¹ λ(𝕌, Y)`;
* `C_F(Ṽ, B₁) ≤ C · C_F(𝕌, T_τ)`.

Four further clauses, not in the blueprint lemma, expose the construction: writing
`Ψ = Tube.rescaleMap T_τ C_N`, they record `Ψ(T i) ⊆ Ṽ i`, `(Ṽ i).shade = Ψ((T i).shade)` and
`|Ṽ i| ≤ (4 C_N) ^ 6 |Ψ(T i)|` for `i ∈ un`, and `Ψ(T_τ) ⊆ B(0, 1/4)`.  See the same section of
`Kakeya.ml1Boot.exists_fineNormalization_core` for what they are for and, more importantly,
for the one thing they are *not*: there is no `hdilate` clause.

*The ambient index set `un`.*  The containment hypothesis is read at a second index set
`un ⊇ u`, and the four construction-visibility clauses are quantified over `un` rather than over
`u`, while essential distinctness, the density bracket and the multiplicity, fullness and
Frostman items stay on `u` and its refinement `u'`.  This costs nothing: the output family
`Ṽ` is the same total function either way — each `Ṽ i` is the centred extension of the
`Ψ`-image of the core of `T i`, which is defined for every `i : ι` — and the three pointwise
clauses need only the containment `T i ⊆ T_τ` and the resulting length bound, both of which
`hsubn` supplies on all of `un`.  The tilt bound, essential distinctness and the density
bracket are genuinely available on `u` alone and are used only there, inside the selection
package.  Taking `un = u` recovers the previous reading verbatim.

The point of the wider quantifier is that a consumer reading a Frostman constant at a family
indexed by an ambient set — `Kakeya.ml1Boot.exists_fineNormalization_lower`, whose item (iv)
reads `familyIn un Ṽ (2 · T_ρ)` — depends on `Ṽ i` for every `i ∈ un`, and `Ṽ` is a total
function that would otherwise be completely unconstrained off `u`.

## The output scale, and what was wrong with the earlier form

The output scale is `fineScale δ τ = min (δ/τ) (1/4)`, not the bare ratio `δ / τ`.  With
`δ / τ` the statement is **false**: the hypotheses permit `δ = τ`, and then it asks for a
nonempty family of `1`-tubes inside `B₁`, which
`Kakeya.ml1Boot.tube_not_subset_closedBall_of_half_lt` rules out — that is
`Kakeya.ml1Boot.not_exists_fineNormalization`, which refutes the earlier form of this lemma
and is retained above as a record.  Truncating at `1/4` is what removes the obstruction, and
it changes nothing where the earlier form was sound: `fineScale δ τ = δ / τ` as soon as
`δ / τ ≤ 1/4`.  No hypothesis bounding `δ / τ` is added, and none is available: see
`Kakeya.ml1Boot.fineScale` and blueprint `note:ml1bootFineNormalizeScaleObstruction`.

The consumers are insensitive to the truncation because
`(δ/τ)/4 ≤ fineScale δ τ ≤ δ / τ` — the first and third clauses of the conjunction
`Kakeya.ml1Boot.fineScale_bounds` — so the fine-factor bracket changes by at most a factor
`16` (`Kakeya.ml1Boot.fineScale_bracket_le`).  That factor is paid out of the *constant*,
`Kakeya.ml1Boot.fineFactor.C = 16 * Kakeya.ml1Boot.fineNormalize.C C_N`, and is spent exactly
once, in `Kakeya.ml1Boot.fine_genKF`.  It is **not** absorbed into the subpolynomial loss:
that route is unsound in this development, for the reason recorded in blueprint
`note:ml1bootFineScaleWhyConstant`.

## Proof status

**Proved**, and `#print axioms` now gives `[propext, Classical.choice, Quot.sound]`: no
`sorryAx`.  An earlier revision of this paragraph recorded one, entering through
`Tube.exists_comparableReplacement_affine` at the private thin-regime packing count
`Tube.essDistinctTubesInSelfDilate.thin_bound` of `Kakeya/Tube/Rescale.lean`; `thin_bound` has
since been closed, so the debt is discharged rather than outstanding.

The route is the blueprint's — normalize by `Φ_{T_τ}`, apply the homothety `z ↦ z / (4 C_N)`,
replace each image by an honest `fineScale δ τ`-tube, and select an essentially distinct
subfamily — with the homothety ratio raised from `C_N` to `4 C_N` and the constant
`Kakeya.ml1Boot.fineNormalize.C` (not the `16`-times-larger `Kakeya.ml1Boot.fineFactor.C`)
enlarged accordingly.

The selection package it runs on is `Tube.exists_comparableReplacement_affine`
(blueprint `lem:comparableAffineImagesToTubes`), which makes the selection *downstairs* on the
honest `τ`-tubes and counts with `Tube.card_le_mul_card_of_dilateCover_affine`
(blueprint `lem:comparableAffineFibreBound`); the pullback of a dilate is placed inside a
dilate of `T i` of ratio `4 (κ + 2) R C_n` by `Tube.preimage_rescale_dilate_subset_dilate`,
and essential distinctness transfers both ways along the affine equivalence by
`isEssentiallyDistinct_affineImage_iff`.

## How the `7/8` deficit was avoided rather than defeated

Earlier revisions of this docstring recorded two obligations as blocking, both real at the
time: `Tube.normalization_distortion` delivers a sub-segment of length only `7/8` (the trimmed
core has length exactly `1 - 2 C_N⁻¹ ρ`, and **unit length is false** — blueprint
`note:tubeNormalizationNotTubes`), so an honest `Kakeya.Tube`, which needs a core of length
exactly `1`, cannot be fitted by `Tube.exists_comparableReplacement`.

That deficit is not repaired; it is *bypassed*.  The volume comparison the route actually needs
is `Tube.volume_centredExtension_le_mul_volume_rescale_image`
(blueprint `lem:rescaleImageVolumeRatio`), and because the Jacobian of the normalization is
exact, `Tube.le_volume` applied to `T` itself supplies the lower bound with **no sub-segment
required**.  The `7/8` therefore never enters.  It still blocks any route that tries to produce
an honest unit-core tube *inside* a homothetic image, so the statement of
`note:tubeNormalizationNotTubes` stands unaltered.

The blueprint's item (i) also records `|u'| ≤ |u|`, which is `Finset.card_le_card` applied to
`u' ⊆ u` and is therefore not a clause of the conclusion here.  The two-sided density bound
is stated with the individual volumes `|T i|` in place of the common volume `|T|` of a
`δ`-tube: all `δ`-tubes are isometric, so the two readings agree. -/
theorem exists_fineNormalization_constructionVisible_withCard (hdim : Module.finrank ℝ E = 3)
    {δ τ : NNReal} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτ1 : τ ≤ 1)
    {Λ : NNReal} (hΛ : 1 ≤ Λ) {μ₀ : ENNReal} (hμ₀ : 0 < μ₀)
    {ι : Type*} {u un : Finset ι} (Tτ : Tube τ E) (T : ι → ShadedTube δ E)
    (hu : u.Nonempty) (hun : u ⊆ un)
    (hsubn : ∀ i ∈ un, (T i).carrier ⊆ Tτ.carrier)
    (hED : (u : Set ι).Pairwise fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
    (hdens : ∀ i ∈ u, (Λ : ENNReal)⁻¹ * μ₀ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ (Λ : ENNReal) * μ₀ * volume (T i).carrier) :
    ∃ u' ⊆ u, u'.Nonempty ∧ ∃ V : ι → ShadedTube (fineScale δ τ) E,
      (u' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
        (u.card : ENNReal) ≤
          (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) *
            (u'.card : ENNReal) ∧
        (∀ i ∈ u', (V i).carrier ⊆ Metric.closedBall 0 1) ∧
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) * (Λ : ENNReal) ^ 2
            * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) ∧
        (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal)
          ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) * (Λ : ENNReal) ^ 2
            * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ENNReal) ∧
        frostmanConstIn u' (fun i => (V i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall
          ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody)
                Tτ.toConvexSpaceBody ∧
        -- the construction-visibility clauses: `V` is comparable to the image of `T` under the
        -- explicit rescaling map `Ψ = Tube.rescaleMap Tτ C_N`, on all of the ambient set `un`
        (∀ i ∈ un, Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) '' (T i).carrier
          ⊆ (V i).carrier) ∧
        (∀ i ∈ un, (V i).shade
          = Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) '' (T i).shade) ∧
        (∀ i ∈ un, volume (V i).carrier
          ≤ (((4 * _root_.Tube.normalization.C 3) ^ 6 : NNReal) : ENNReal)
            * volume (Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ)
                '' (T i).carrier)) ∧
        (∀ i ∈ un, ∀ h : Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (T i).x ≠
            Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (T i).y,
          (V i).toTube = Tube.centredExtension (fineScale δ τ) h) ∧
        Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) '' Tτ.carrier
          ⊆ Metric.closedBall (0 : E) (1 / 4) := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  have hτ0 : 0 < τ := lt_of_lt_of_le hδ hδτ
  set Cn : NNReal := _root_.Tube.normalization.C 3 with hCn
  set R : ℝ := (Cn : ℝ) with hRdef
  let i₀ : ι := Classical.choose hu
  have hi₀ : i₀ ∈ u := Classical.choose_spec hu
  have hδτ0 : 0 < (δ / τ : NNReal) := by
    rw [← NNReal.coe_lt_coe]
    rw [NNReal.coe_div]
    exact div_pos (by exact_mod_cast hδ) (by exact_mod_cast hτ0)
  have hpos : 0 < fineScale δ τ := by
    dsimp [fineScale]
    exact lt_min hδτ0 (by norm_num)
  have hquarter : (fineScale δ τ : ℝ) ≤ 1 / 4 := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).2.1
  have hratioσ : (fineScale δ τ : ℝ) ≤ (δ : ℝ) / (τ : ℝ) := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).1
  have hρσ : (δ : ℝ) / (τ : ℝ) ≤ 4 * (fineScale δ τ : ℝ) := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).2.2
  have hCn1 : 1 ≤ Cn := _root_.Tube.normalization.one_le_C 3
  have hR1 : (1 : ℝ) ≤ R := by
    dsimp [R]
    exact_mod_cast hCn1
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hsit : _root_.Tube.IsRescalingSituation τ δ (fineScale δ τ) R 3 :=
    ⟨hτ0, hδτ, hτ1, hpos, hquarter, hratioσ, le_rfl⟩
  obtain ⟨L, hL⟩ := _root_.Tube.exists_rescaleEquiv hτ0 hR0 Tτ
  have hcont : Continuous L := AffineEquiv.continuous_of_finiteDimensional L
  have hemb : MeasurableEmbedding L :=
    (AffineEquiv.toContinuousAffineEquiv L).toHomeomorph.measurableEmbedding
  have hxy : ∀ i : ι, Tτ.rescaleMap R (T i).x ≠ Tτ.rescaleMap R (T i).y := by
    intro i h
    rw [← hL] at h
    exact (fun hne => hne (L.injective h)) (fun hxy => by
      have := (T i).toTube.dist_eq_one
      rw [hxy] at this
      simp at this)
  set 𝕎 : ι → ShadedBody E := fun i => ((T i).toShadedBody).affineImage L.toAffineMap hcont hemb
  set 𝕍 : ι → ShadedTube (fineScale δ τ) E := fun i =>
    { toTube := _root_.Tube.centredExtension (fineScale δ τ) (hxy i)
      shade := (𝕎 i).shade ∩ (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).carrier
      measurableSet_shade :=
        (𝕎 i).measurableSet_shade.inter
          (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).isCompact.measurableSet
      shade_subset := Set.inter_subset_right }
  have hdist : ∀ i ∈ un, _root_.Tube.IsNormalizationDistortion Tτ (T i).toTube := fun i hi =>
    _root_.Tube.normalization_distortion hτ0 hδτ hτ1 Tτ (T i).toTube (hsubn i hi)
  have hball0 : Tτ.normalization '' Tτ.carrier ⊆ Metric.closedBall Tτ.x R := by
    have h := _root_.Tube.normalization_image_ambient_subset_closedBall hτ0 hτ1 Tτ
    rw [hdim] at h
    simpa [R, hCn] using h
  have hball : ∀ i ∈ un, Tτ.normalization '' (T i).carrier ⊆ Metric.closedBall Tτ.x R := by
    intro i hi
    exact (Set.image_mono (hsubn i hi)).trans hball0
  have houter := fun i hi => _root_.Tube.rescale_outer_tube
    (hsit := hsit) (hn := hdim) (hR := hR0) (hρσ := hρσ) (T₀ := Tτ)
    (T := (T i).toTube) (hdist := hdist i hi) (hball := hball i hi) (hxy := hxy i)
  have hofR : ENNReal.ofReal ((4 * R) ^ 6) = (((4 * Cn) ^ 6 : NNReal) : ENNReal) := by
    have hRnonneg : (0 : ℝ) ≤ 4 * R := by positivity
    calc
      ENNReal.ofReal ((4 * R) ^ 6) = (ENNReal.ofReal (4 * R)) ^ 6 := by
            rw [ENNReal.ofReal_pow hRnonneg]
      _ = ((4 * Cn : NNReal) : ENNReal) ^ 6 := by
            congr 1
            rw [← ENNReal.ofReal_coe_nnreal]
            congr 1
      _ = (((4 * Cn) ^ 6 : NNReal) : ENNReal) := by
            rw [ENNReal.coe_pow]
  have hWcarrier : ∀ i ∈ un, (𝕎 i).carrier = Tτ.rescaleMap R '' (T i).carrier := by
    intro i hi
    dsimp [𝕎]
    change L.toAffineMap '' (T i).carrier = Tτ.rescaleMap R '' (T i).carrier
    rw [← hL]
  have hsub' : ∀ i ∈ un, (𝕎 i).carrier ⊆ (𝕍 i).carrier := by
    intro i hi
    rw [hWcarrier i hi]
    simpa [𝕍] using (houter i hi).1
  have h𝕍ball : ∀ i ∈ u, (𝕍 i).toTube.carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    simpa [𝕍] using (houter i (hun hi)).2.1
  have hshade : ∀ i ∈ un, (𝕍 i).shade = (𝕎 i).shade := by
    intro i hi
    dsimp [𝕍]
    exact (Set.inter_eq_left).mpr ((𝕎 i).shade_subset.trans (hsub' i hi))
  have hCv : 1 ≤ (4 * Cn) ^ 6 := by
    exact one_le_pow₀ (one_le_mul (by norm_num) hCn1)
  have hVK : ∀ i ∈ u,
      (𝕍 i).toConvexSpaceBody ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    intro i hi
    change (𝕍 i).carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    simpa [𝕍] using h𝕍ball i hi
  let c' : ℝ := 4 * ((2 : ℝ) + 2) * R * Kakeya.Tube.tubeOverlapCoreClose.C 3
  have hc'1 : (1 : ℝ) ≤ c' := by
    dsimp [c']
    have hRgr : (1 : ℝ) ≤ R := hR1
    have hCnR : (1 : ℝ) ≤ (Kakeya.Tube.tubeOverlapCoreClose.C 3 : ℝ) := by
      exact_mod_cast (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3))
    nlinarith
  let c₁ : NNReal := _root_.Tube.essDistinctTubesInSelfDilate.C 3
    (4 * ((2 : ℝ) + 2) * ((_root_.Tube.normalization.C 3 : NNReal) : ℝ)
      * Kakeya.Tube.tubeOverlapCoreClose.C 3)
  have hc₁ : c₁ = _root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * ((2 : ℝ) + 2) * ((_root_.Tube.normalization.C 3 : NNReal) : ℝ)
        * Kakeya.Tube.tubeOverlapCoreClose.C 3) := by
    rfl
  have hC₁ : (1 : NNReal) ≤ c₁ := by
    let 𝕋 : ι → Tube δ E := fun i => (T i).toTube
    have hpw₀ : (({i₀} : Finset ι) : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (𝕋 i).carrier (𝕋 j).carrier) := by
      simp
    have hsub₀ : ∀ j ∈ ({i₀} : Finset ι), (𝕋 j).carrier
        ⊆ (Kakeya.Tube.dilate (𝕋 i₀) c').carrier := by
      intro j hj
      have hji : j = i₀ := by simpa using hj
      subst j
      exact _root_.Tube.subset_dilate (𝕋 i₀) hc'1
    have hcount : (({i₀} : Finset ι).card : ENNReal)
        ≤ (_root_.Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) c' : ENNReal) :=
      _root_.Tube.essDistinctTubesInSelfDilate hc'1 hδ (le_trans hδτ hτ1 : δ ≤ 1) (𝕋 i₀)
        ({i₀} : Finset ι) 𝕋 hpw₀ hsub₀
    exact ENNReal.coe_le_coe.mp (by simpa [c₁, c', R, hCn, hdim] using hcount)
  have hperp : ∀ i ∈ u, ‖(T i).toTube.direction
      - (inner ℝ Tτ.direction (T i).toTube.direction : ℝ) • Tτ.direction‖
      ≤ (2 : ℝ) * (τ : ℝ) := fun i hi =>
    _root_.Tube.perp_norm_direction_le_of_subset Tτ (T i).toTube (hsubn i (hun hi))
  have hVtube : ∀ i ∈ u, (𝕍 i).toTube = _root_.Tube.centredExtension (fineScale δ τ) (hxy i) := by
    intro i hi
    rfl
  have hvol : ∀ i ∈ un, volume (𝕍 i).carrier
      ≤ (((4 * Cn) ^ 6 : NNReal) : ENNReal) * volume (𝕎 i).carrier := by
    intro i hi
    calc
      volume (𝕍 i).carrier
          = volume (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).carrier := by
            simp [𝕍]
      _ ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (Tτ.rescaleMap R '' (T i).carrier) :=
            (houter i hi).2.2
      _ = (((4 * Cn) ^ 6 : NNReal) : ENNReal) * volume (Tτ.rescaleMap R '' (T i).carrier) := by
            rw [hofR]
      _ = (((4 * Cn) ^ 6 : NNReal) : ENNReal) * volume (𝕎 i).carrier := by
            rw [hWcarrier i hi]
  let W : ENNReal := volume (𝕎 i₀).carrier
  have hW : 0 < W := by
    dsimp [W]
    simpa [𝕎] using volume_affineImage_carrier_pos hδ (T i₀) L hcont hemb
  have hcommon : ∀ i ∈ u, volume (𝕎 i).carrier = W := by
    intro i hi
    dsimp [W]
    simpa [𝕎] using volume_affineImage_carrier_eq (T i) (T i₀) L hcont hemb
  have hZ : ∀ i ∈ u, (Λ : ENNReal)⁻¹ * μ₀ * W ≤ volume (𝕎 i).shade ∧
      volume (𝕎 i).shade ≤ (Λ : ENNReal) * μ₀ * W := by
    intro i hi
    have hz := affineImage_shade_bounds (S := T i) (S' := T i₀) L hcont hemb
      (hdens i hi).1 (hdens i hi).2
    dsimp [W, 𝕎] at hz ⊢
    exact hz
  let 𝕋 : ι → Tube δ E := fun i => (T i).toTube
  have himg : ∀ i ∈ u, (Tτ.rescaleMap R) '' (T i).carrier ⊆ ((𝕍 i).toTube).carrier := by
    intro i hi
    simpa [𝕍] using (houter i (hun hi)).1
  have hpackage : _root_.Tube.IsComparableReplacementFree u 𝕎 𝕍
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) ((4 * Cn) ^ 6) Λ c₁ := by
    simpa [hc₁, hdim, R, hCn] using
      (_root_.Tube.exists_comparableReplacement_affine (n := 3) (R := R)
      (κ := (2 : ℝ)) (s := u) hu hsit (by norm_num) hδ (le_trans hδτ hτ1 : δ ≤ 1) Tτ
      𝕋 hxy 𝕎 𝕍
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)) (C := (4 * Cn) ^ 6) (Λ := Λ)
      (W := W) (μ₀ := μ₀) hCv hΛ hW hμ₀ hcommon hVtube hperp
      (by simpa [𝕋] using hED) himg (fun i hi => hshade i (hun hi))
      (fun i hi => hsub' i (hun hi)) hVK (fun i hi => hvol i (hun hi)) hZ)
  let K' : ConvexSpaceBody E := (Tτ.toConvexSpaceBody).affineImage L.toAffineMap hcont
  have hK'c : K'.carrier ⊆ Metric.closedBall (0 : E) (1 / 4) := by
    have h := _root_.Tube.rescale_image_ambient_subset_closedBall hτ0 hτ1 hR0 (by
      dsimp [R]
      rw [hdim]
      rfl) Tτ
    simpa [K', ← hL] using h
  have hK' : (K' : ConvexSpaceBody E) ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    change K'.carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    exact hK'c.trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hK'vol : volume K'.carrier ≠ 0 := by
    have h1 : volume ((Tτ.toConvexSpaceBody).affineImage L.toAffineMap hcont).carrier ≠ 0 := by
      rw [ConvexSpaceBody.volume_affineImage]
      have hA : ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| ≠ 0 := by
        exact (ENNReal.ofReal_eq_zero.not).mpr
          (not_le.mpr (abs_pos.mpr (LinearEquiv.isUnit_det' L.linear).ne_zero))
      have hB : volume (Tτ.toConvexSpaceBody).carrier ≠ 0 := by
        have hle : (_root_.Tube.le_volume.c 3 : ENNReal) * (τ : ENNReal) ^ 2
            ≤ volume (Tτ.toConvexSpaceBody).carrier := by
          simpa [hdim] using _root_.Tube.le_volume Tτ
        have hpos : (0 : ENNReal) < (_root_.Tube.le_volume.c 3 : ENNReal) * (τ : ENNReal) ^ 2 := by
          exact_mod_cast (mul_pos (_root_.Tube.le_volume.c_pos 3) (pow_pos hτ0 2))
        exact ne_of_gt (lt_of_lt_of_le hpos hle)
      exact mul_ne_zero hA hB
    simpa [K'] using h1
  have hWK' : ∀ i ∈ u, (𝕎 i).toConvexSpaceBody ≤ K' := by
    intro i hi
    change (𝕎 i).carrier ⊆ K'.carrier
    rw [hWcarrier i (hun hi)]
    rw [← hL]
    exact Set.image_mono (hsubn i (hun hi))
  have hratio : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      ≤ (((4 * Cn) ^ 6 : NNReal) : ENNReal) * volume K'.carrier := by
    have h := _root_.Tube.volume_closedBall_one_le_mul_volume_rescale_image_ambient
      (E := E) hdim hτ0 hR1 Tτ
    rw [hofR] at h
    simpa [K', ← hL, ConvexSpaceBody.closedUnitBall_carrier] using h
  have hfrodsman : frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
      ≤ (((4 * Cn) ^ 6 : NNReal) : ENNReal)
        * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' :=
    frostmanConstIn_closedUnitBall_le_of_ambient (u := u) (𝕎 := 𝕎) (K' := K')
      (Cv := (4 * Cn) ^ 6) hK' hK'vol hWK' hratio
  have hF_rel : frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K'
      = frostmanConstIn u (fun i => (T i).toConvexSpaceBody) Tτ.toConvexSpaceBody := by
    have h := ConvexSpaceBody.frostmanConstIn_affineImage u (fun i => (T i).toConvexSpaceBody)
      Tτ.toConvexSpaceBody L hcont
    dsimp [𝕎, K']
    exact h
  obtain ⟨u', hu'sub, hu'ne, hVD, hu'card, hmult, hfull, hfrost⟩ :=
    of_comparableReplacementFree (u := u) (𝕎 := 𝕎) (𝕍 := 𝕍)
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)) (Cv := (4 * Cn) ^ 6)
      (Λ := Λ) (C₁ := c₁) hΛ hCv hC₁ hVK hpackage
  refine ⟨u', hu'sub, hu'ne, 𝕍, ?_⟩
  constructor
  · simpa [𝕍] using hVD
  constructor
  · calc
      (u.card : ENNReal) ≤ (c₁ : ENNReal) * (u'.card : ENNReal) := hu'card
      _ ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) *
          (u'.card : ENNReal) := by
        gcongr
        exact_mod_cast (fineNormalize_C_dominates hc₁).1
  constructor
  · intro i hi
    simpa [𝕍] using h𝕍ball i (hu'sub hi)
  constructor
  · calc
      ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          = ShadedBody.multiplicity u 𝕎 := by
            simpa [𝕎] using (ShadedBody.multiplicity_affineImage u
              (fun i => (T i).toShadedBody) L hcont hemb).symm
      _ ≤ (c₁ : ENNReal) * (Λ : ENNReal) ^ 2
          * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := hmult
      _ ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) * (Λ : ENNReal) ^ 2
          * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := by
            gcongr
            exact_mod_cast (fineNormalize_C_dominates hc₁).1
  constructor
  · calc
      (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal)
          = (ShadedBody.fullness u 𝕎 : ENNReal) := by
            simpa [𝕎] using (ShadedBody.fullness_affineImage u
              (fun i => (T i).toShadedBody) L hcont hemb).symm
      _ ≤ (((4 * Cn) ^ 6 : NNReal) : ENNReal) * (c₁ : ENNReal) * (Λ : ENNReal) ^ 2
          * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal) := hfull
      _ ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) * (Λ : ENNReal) ^ 2
          * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal) := by
            gcongr
            exact_mod_cast (fineNormalize_C_dominates hc₁).2.1
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody)
            (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
            ≤ (c₁ : ENNReal) * (((4 * Cn) ^ 6 : NNReal) : ENNReal)
              * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
                  (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := hfrost
        _ ≤ (c₁ : ENNReal) * (((4 * Cn) ^ 6 : NNReal) : ENNReal)
            * ((((4 * Cn) ^ 6 : NNReal) : ENNReal)
              * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K') := by
              exact mul_le_mul_right hfrodsman
                ((c₁ : ENNReal) * (((4 * Cn) ^ 6 : NNReal) : ENNReal))
        _ = (c₁ : ENNReal) * (((4 * Cn) ^ 6 : NNReal) : ENNReal)
            * ((((4 * Cn) ^ 6 : NNReal) : ENNReal)
              * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) Tτ.toConvexSpaceBody) := by
              rw [hF_rel]
        _ = ((c₁ * (4 * Cn) ^ 6 * (4 * Cn) ^ 6 : NNReal) : ENNReal)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) Tτ.toConvexSpaceBody := by
              simp [ENNReal.coe_mul]
              ring
        _ ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) Tτ.toConvexSpaceBody := by
              have hdom : (c₁ * (4 * Cn) ^ 6 * (4 * Cn) ^ 6 : NNReal) ≤ fineNormalize.C Cn := by
                calc
                  (c₁ * (4 * Cn) ^ 6 * (4 * Cn) ^ 6 : NNReal)
                      = c₁ * ((4 * Cn) ^ 6 * (4 * Cn) ^ 6) := by
                        rw [← mul_assoc]
                  _ = c₁ * (4 * Cn) ^ 12 := by
                        rw [← pow_add]
                  _ = ((4 * Cn) ^ 12 : NNReal) * c₁ := by ring
                  _ ≤ fineNormalize.C Cn := (fineNormalize_C_dominates hc₁).2.2
              exact mul_le_mul (by exact_mod_cast hdom) le_rfl (by positivity) (by positivity)
    · intro i hi
      rw [← hWcarrier i hi]
      exact hsub' i hi
    · intro i hi
      rw [hshade i hi]
      simp [𝕎, hL]
    · intro i hi
      rw [← hWcarrier i hi]
      exact hvol i hi
    · intro i _ _
      rfl
    · simpa [K', ← hL] using hK'c

end
end W44NormalizationPort
end ml1Boot
end Kakeya
