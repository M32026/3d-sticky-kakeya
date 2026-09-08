/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.FibrePacking
public import Kakeya.MultiScaleFac.Density
public import Mathlib.Tactic.Linarith.NNRealPreprocessor -- for `linarith` over `NNReal`

/-!
# Per-gap Katz–Tao data from per-gap Frostman bounds

The stopping-time argument of GWZ Lemma 7.7 supplies, for each gap `(σb, σa)` of the scale grid,
a *Frostman* bound `C_F(𝕋_{σb∣σa}[i₀], T_{i₀}^{(σa)}) ≤ X` valid for every anchor `i₀ ∈ s`.  The
multiscale product engine consumes *Katz–Tao* data instead.  This file performs the conversion,
twice.

* Leaf reading (`isKatzTao_gapFibre_of_isFrostmanIn`, blueprint `lem:gap_katzTao_data`).  A
  Frostman bound becomes a Katz–Tao bound once the density of the family in its own anchor body
  is known, and that density is bounded by `densityIn_gapFibre_le` in terms of the branching
  number at the *coarse* scale only.  The fine scale has disappeared from the right-hand side, so
  the resulting constant does not depend on the anchor `i₀`.

* Node reading (`isKatzTao_gapNodeIndex_of_isKatzTao_gapFibre`).  The engine that actually
  cancels the density factors — `maxDensity_le_prod_of_grid_cuts_nodes` — needs the *nodes* of
  the fine uniform structure inside the fattened container `T_{i₁}^{(5σa)}` to be Katz–Tao, one
  body per node.  Passing from leaves to nodes divides the count by the fine branching number
  (`parent_card_mul_branchingN_le_of_subset`), and reaching the fattened container costs a
  dimensional number of re-anchorings of the leaf hypothesis
  (`exists_gapFibre_cover_of_inflated`).  This is why the leaf reading alone is not enough: its
  per-gap constants carry the branching numbers, which do not telescope.

The uniformity hypothesis of every conversion below is the bundle
`Tube.ChainUniformTubeSet s T N σ Cu` together with `1 ≤ Cu` and a level bound
`k ≤ N`, the uniformity scale being the chain scale `σ k`: the coarse scale `σa` for the leaf
reading, the fine scale `σb` for the node reading.  Each proof consumes the per-scale reading
`ChainUniformTubeSet.uniformAt`, whose constant is `Cu ^ 2`, and that is why the constants below
are powers of `Cu ^ 2` rather than of `Cu`.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]


/-- **Per-gap Katz–Tao data from the `δ`-indexed per-gap Frostman bound.**  Same conclusion as
`isKatzTao_gapFibre_of_isFrostmanIn`, but starting from GWZ's own convention: the index set of the
gap family is fixed at the *leaf* level `{i : T_i ⊆ T_{i₀}^{(σa)}}`, its members are thickened to
`σb` afterwards, and the test body is the doubled anchor `T_{i₀}^{(2σa)}`. -/
theorem isKatzTao_gapFibre_of_blockFrostman {ι : Type*} {δ σb Cu : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}
    (𝒰 : ChainUniformTubeSet s T N σ Cu) (hCu : 1 ≤ Cu) {k : ℕ} (hk : k ≤ N)
    (hδσb : δ ≤ σb) (hσb1 : σb ≤ 1) (hσa : 0 < σ k) (hσbσa : σb ≤ σ k) {X Y : ENNReal}
    (hY : X * (((Cu : ENNReal) ^ 2) ^ 2 * (𝒰.branchingN k : ENNReal)
            * ((Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
                * (σb : ENNReal) ^ (Module.finrank ℝ E - 1)))
          ≤ Y * ((Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
              * (σ k : ENNReal) ^ (Module.finrank ℝ E - 1)))
    (i₀ : ι)
    (hFr : ConvexSpaceBody.IsFrostmanIn (fibreIndex s T δ (σ k) i₀) (fibreBodies T σb)
        ((T i₀).rescale (2 * σ k)).toConvexSpaceBody X) :
    ConvexSpaceBody.IsKatzTao (fibreIndex s T σb (σ k) i₀) (fibreBodies T σb) Y := by
  set σa := σ k with hσadef
  set h : Tube.IsUniformAtScale s T σa (Cu ^ 2) := 𝒰.uniformAt hCu hk with hh
  rw [ConvexSpaceBody.IsKatzTao_def]
  set n := Module.finrank ℝ E with hn
  have hA_nonzero : ((Tube.le_volume.c n : ENNReal) * ((σa : ENNReal) ^ (n - 1))) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Tube.le_volume.c_pos n).ne')
      (ENNReal.pow_ne_zero (by exact_mod_cast hσa.ne') (n - 1))
  have hA_finite : ((Tube.le_volume.c n : ENNReal) * ((σa : ENNReal) ^ (n - 1))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  set A := ((Tube.le_volume.c n : ENNReal) * ((σa : ENNReal) ^ (n - 1))) with hA
  have hsubset : ∀ i ∈ fibreIndex s T δ σa i₀,
      fibreBodies T σb i ≤ ((T i₀).rescale (2 * σa)).toConvexSpaceBody := by
    intro i hi
    rw [fibreIndex_self s T σa i₀] at hi
    have hθ : σa + σb ≤ 2 * σa := by linarith
    exact Tube.rescale_le_rescale_of_body_le (T i) ((T i₀).rescale σa) (σ := σb) (θ := 2 * σa)
      hδσb hθ (Finset.mem_filter.mp hi).2
  have hmaxDensity : maxDensity (fibreIndex s T δ σa i₀) (fibreBodies T σb)
      ≤ X * Kakeya.densityIn (fibreIndex s T δ σa i₀) (fibreBodies T σb)
        ((T i₀).rescale (2 * σa)).toConvexSpaceBody :=
    hFr.maxDensity_le_of_carrier_subset hsubset
  have hG_sub : fibreIndex s T σb σa i₀ ⊆ fibreIndex s T δ σa i₀ :=
    fibreIndex_subset_of_member_le hδσb i₀
  have hmaxDensity_mono : maxDensity (fibreIndex s T σb σa i₀) (fibreBodies T σb)
      ≤ maxDensity (fibreIndex s T δ σa i₀) (fibreBodies T σb) :=
    maxDensity_mono (fibreBodies T σb) hG_sub
  have hdensity : Kakeya.densityIn (fibreIndex s T δ σa i₀) (fibreBodies T σb)
      ((T i₀).rescale (2 * σa)).toConvexSpaceBody * A
    ≤ ((Cu : ENNReal) ^ 2) ^ 2 * (h.branchingN : ENNReal)
        * ((Tube.volume_le.C n : ENNReal) * ((σb : ENNReal) ^ (n - 1))) := by
    set t := fibreIndex s T δ σa i₀ with ht
    set W := fibreBodies T σb with hW
    set K := ((T i₀).rescale (2 * σa)).toConvexSpaceBody with hK
    set vhi := ((Tube.volume_le.C n : NNReal) : ENNReal) * ((σb : ENNReal) ^ (n - 1)) with hvhi
    set vlo := ((Tube.le_volume.c n : NNReal) : ENNReal) * ((σa : ENNReal) ^ (n - 1)) with hvlo
    have hband : Kakeya.densityIn t W K * vlo ≤ ((Kakeya.familyIn t W K).card : ENNReal) * vhi :=
      densityIn_mul_le_of_volume_band t W K
        (hW := by
          intro i hi
          calc
            volume ((W i).carrier) = volume ((T i).rescale σb).carrier := by
              simp [W, fibreBodies]
            _ ≤ (Tube.volume_le.C n * σb ^ (n - 1) : ENNReal) :=
              Tube.volume_le hσb1 ((T i).rescale σb)
            _ = vhi := by simp [vhi])
        (hK := by
          calc
            vlo = (Tube.le_volume.c n * σa ^ (n - 1) : ENNReal) := by simp [vlo]
            _ ≤ volume ((T i₀).rescale σa).carrier := Tube.le_volume ((T i₀).rescale σa)
            _ ≤ volume K.carrier :=
              measure_mono (SetLike.coe_subset_coe.mpr
                (Tube.rescale_le_rescale_of_radius_le (T i₀) (by linarith))))
    calc
      Kakeya.densityIn (fibreIndex s T δ σa i₀) (fibreBodies T σb)
          ((T i₀).rescale (2 * σa)).toConvexSpaceBody * A
          = Kakeya.densityIn t W K * vlo := by
        simp [t, W, K, vlo, A, hA]
      _ ≤ ((Kakeya.familyIn t W K).card : ENNReal) * vhi := hband
      _ ≤ ((t.card : ENNReal)) * vhi := by
        have hcard : (Kakeya.familyIn t W K).card ≤ t.card :=
          Finset.card_le_card (Finset.filter_subset (fun i => W i ≤ K) t)
        exact mul_le_mul_left (by exact_mod_cast hcard) _
      _ = (((fibreIndex s T δ σa i₀).card : NNReal) : ENNReal) * vhi := by simp [t]
      _ ≤ ((((Cu ^ 2) ^ 2 * h.branchingN : NNReal) : ENNReal)) * vhi :=
        mul_le_mul_left
          (ENNReal.coe_le_coe.mpr (card_fibreIndex_le_mul_branchingN 𝒰 hCu hk i₀)) _
      _ = ((Cu : ENNReal) ^ 2) ^ 2 * (h.branchingN : ENNReal) * vhi := by
        simp
      _ = ((Cu : ENNReal) ^ 2) ^ 2 * (h.branchingN : ENNReal)
          * ((Tube.volume_le.C n : ENNReal) * ((σb : ENNReal) ^ (n - 1))) := by
        simp [vhi, hn]
  have hchain : maxDensity (fibreIndex s T σb σa i₀) (fibreBodies T σb) * A
      ≤ Y * A :=
    calc
      maxDensity (fibreIndex s T σb σa i₀) (fibreBodies T σb) * A
          ≤ (X * Kakeya.densityIn (fibreIndex s T δ σa i₀) (fibreBodies T σb)
              ((T i₀).rescale (2 * σa)).toConvexSpaceBody) * A :=
        mul_le_mul_left (hmaxDensity_mono.trans hmaxDensity) _
      _ = X * (Kakeya.densityIn (fibreIndex s T δ σa i₀) (fibreBodies T σb)
          ((T i₀).rescale (2 * σa)).toConvexSpaceBody * A) := mul_assoc _ _ _
      _ ≤ X * (((Cu : ENNReal) ^ 2) ^ 2 * (h.branchingN : ENNReal)
          * ((Tube.volume_le.C n : ENNReal) * ((σb : ENNReal) ^ (n - 1)))) :=
        mul_le_mul_right hdensity _
      _ ≤ Y * A := hY
  exact (ENNReal.mul_le_mul_iff_left hA_nonzero hA_finite).mp hchain

/-- **The leaves of a fattened fibre, weighted, are controlled by the gap Katz–Tao constant.**  The
leaves of `𝕋_{δ∣θ}[i₁]` that fit in a test body `K` are distributed among `C(n)` of the gap fibres
`𝕋_{σb∣σa}[i₂]`, and the `σb`-thickening of a `δ`-tube inside `K` lies in the `σb`-thickening of
`K`; applying the Katz–Tao hypothesis of each fibre at that single fattened body gives the bound. -/
private theorem card_gapLeaves_mul_le {ι : Type*} {δ σa σb θ : NNReal}
    {s : Finset ι} {T : ι → Tube δ E}
    (hσa : 0 < σa) (hδσb : δ ≤ σb) (hσb2 : 2 * σb ≤ σa) (hθ : θ ≤ 6 * σa)
    {Y : ENNReal}
    (hKT : ∀ i₂ ∈ s, ConvexSpaceBody.IsKatzTao (fibreIndex s T σb σa i₂) (fibreBodies T σb) Y)
    (i₁ : ι) (K : ConvexSpaceBody E) :
    ((Kakeya.familyIn (fibreIndex s T δ θ i₁) (fun i => (T i).toConvexSpaceBody) K).card : ENNReal)
        * ((Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
            * (σb : ENNReal) ^ (Module.finrank ℝ E - 1))
      ≤ (fibrePackConst (Module.finrank ℝ E) : ENNReal) * Y
          * volume (K.cthickening (σb : ℝ)).carrier := by
  classical
  set n := Module.finrank ℝ E with hn
  set c := Tube.le_volume.c n with hc
  set F := fibreIndex s T δ θ i₁ with hF
  set FK := Kakeya.familyIn F (fun i => (T i).toConvexSpaceBody) K with hFK
  set Kplus := K.cthickening (σb : ℝ) with hKplus
  set cσb := (c : ENNReal) * (σb : ENNReal) ^ (n - 1) with hcσb
  obtain ⟨A, hAs, hAcard, hcov⟩ :=
    exists_gapFibre_cover_of_inflated (s := s) (T := T) hσa hδσb hσb2 hθ i₁
  have h_fibreBody_sub_Kplus : ∀ i ∈ F, (T i).toConvexSpaceBody ≤ K →
      fibreBodies T σb i ≤ Kplus := by
    intro i _ hi_body
    calc
      fibreBodies T σb i = (T i).toConvexSpaceBody.cthickening ((σb : ℝ) - (δ : ℝ)) :=
        ((T i).toConvexBody_cthickening_sub hδσb).symm
      _ ≤ K.cthickening ((σb : ℝ) - (δ : ℝ)) :=
        ConvexSpaceBody.cthickening_mono ((σb : ℝ) - (δ : ℝ)) hi_body
      _ ≤ Kplus := by
        refine SetLike.coe_subset_coe.mp ?_
        exact Metric.cthickening_mono (sub_le_self _ (NNReal.coe_nonneg δ)) (K.carrier : Set E)
  have h_cover_sub : FK ⊆ A.biUnion (fun i₂ =>
      Kakeya.familyIn (fibreIndex s T σb σa i₂) (fibreBodies T σb) Kplus) := by
    intro i hi
    dsimp [FK, Kakeya.familyIn] at hi
    obtain ⟨i₂, hi₂A, hi_fibre⟩ := hcov i (Finset.mem_filter.mp hi).1
    refine Finset.mem_biUnion.mpr ⟨i₂, hi₂A, ?_⟩
    dsimp [Kakeya.familyIn]
    exact Finset.mem_filter.mpr ⟨hi_fibre, h_fibreBody_sub_Kplus i
      (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2⟩
  have h_card_FK_le_sum : (FK.card : ENNReal) ≤
      ∑ i₂ ∈ A,
        ((Kakeya.familyIn (fibreIndex s T σb σa i₂) (fibreBodies T σb) Kplus).card : ENNReal) := by
    exact_mod_cast (Finset.card_le_card h_cover_sub).trans Finset.card_biUnion_le
  have hKTeach : ∀ i₂ ∈ A,
      ((Kakeya.familyIn (fibreIndex s T σb σa i₂) (fibreBodies T σb) Kplus).card : ENNReal) * cσb
      ≤ Y * volume Kplus.carrier := by
    intro i₂ hi₂A
    refine (le_densityIn_mul_of_volume_band (fibreIndex s T σb σa i₂) (fibreBodies T σb) Kplus
      (hW := fun i _ => by
        dsimp [cσb, hc, n, fibreBodies]
        simpa using Tube.le_volume ((T i).rescale σb))
      (hK := le_rfl)).trans ?_
    rw [← Kakeya.sum_volume_eq_densityIn_mul_volume]
    exact (ConvexSpaceBody.isKatzTao_iff _ _ Y).mp (hKT i₂ (hAs hi₂A)) Kplus
  have hAcard_enn : (A.card : ENNReal) ≤ (fibrePackConst n : ENNReal) := by
    exact_mod_cast hAcard
  calc
    ((Kakeya.familyIn (fibreIndex s T δ θ i₁) (fun i => (T i).toConvexSpaceBody) K).card : ENNReal)
        * ((Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
            * (σb : ENNReal) ^ (Module.finrank ℝ E - 1))
        = (FK.card : ENNReal) * cσb := by
      dsimp [FK, cσb, hc, n]
    _ ≤ (∑ i₂ ∈ A,
          ((Kakeya.familyIn (fibreIndex s T σb σa i₂) (fibreBodies T σb) Kplus).card : ENNReal))
        * cσb := mul_le_mul_left h_card_FK_le_sum _
    _ = ∑ i₂ ∈ A,
          (((Kakeya.familyIn (fibreIndex s T σb σa i₂) (fibreBodies T σb) Kplus).card : ENNReal)
            * cσb) := by
      simp [Finset.sum_mul]
    _ ≤ ∑ _i₂ ∈ A, Y * volume Kplus.carrier := Finset.sum_le_sum hKTeach
    _ = (A.card : ENNReal) * Y * volume Kplus.carrier := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ (fibrePackConst n : ENNReal) * Y * volume Kplus.carrier :=
      mul_le_mul_left (mul_le_mul_left hAcard_enn Y) _
    _ = (fibrePackConst (Module.finrank ℝ E) : ENNReal) * Y
        * volume (K.cthickening (σb : ℝ)).carrier := by
      simp [hKplus, hn]

omit [Nontrivial E] in
/-- **Thickening a test body that contains a tube.**  If a `σ`-tube fits inside the convex body
`K`, then `K` contains a ball of radius `σ`, so thickening `K` by `σ` costs only the dimensional
factor `2 ^ n`.  This is the step that lets a Katz–Tao hypothesis about `σ`-thickened members be
evaluated at a test body that only sees the `δ`-cores. -/
theorem volume_cthickening_le_of_tube_le {σ : NNReal} (V : Tube σ E) (K : ConvexSpaceBody E)
    (hVK : V.toConvexSpaceBody ≤ K) :
    volume (K.cthickening (σ : ℝ)).carrier
      ≤ (2 : ENNReal) ^ Module.finrank ℝ E * volume K.carrier := by
  have hball_sub : Metric.closedBall V.x (σ : ℝ) ⊆ (K.carrier : Set E) :=
    (V.closedBall_subset_carrier_of_mem_segment (left_mem_segment ℝ V.x V.y)).trans
      (SetLike.coe_subset_coe.mpr hVK)
  have hvol := volume_cthickening_nat_mul_le_of_ball (K.carrier : Set E) K.convex K.isCompact'
    V.x (r := (σ : ℝ)) (NNReal.coe_nonneg σ) hball_sub 1
  have h_pow : ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E)
      = (2 : ENNReal) ^ Module.finrank ℝ E := by
    rw [ENNReal.ofReal_pow (by norm_num)]; norm_num
  simpa [h_pow] using hvol

/-- **Node-reading Katz–Tao data from leaf-reading Katz–Tao data, per-scale form.**  In any test
body the node count is the leaf count divided by the fine branching number `N_{σb}`, which is the
hypothesis `hΔ`; so the `σb`-nodes contained in `T_{i₁}^{(5σa)}` are `Δ`-Katz–Tao, the container
inflation from `σa` to `5σa` being paid for by the re-anchorings of `card_gapLeaves_mul_le`. -/
theorem isKatzTao_gapNodeIndex_of_isKatzTao_gapFibre_atScale {ι : Type*} {δ σa σb Cu : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} (ub : Tube.IsUniformAtScale s T σb Cu)
    (hσa : 0 < σa) (hδσb : δ ≤ σb) (hσb1 : σb ≤ 1) (hσb2 : 2 * σb ≤ σa)
    {Y Δ : ENNReal}
    (hΔ : (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * (Cu : ENNReal) ^ 2
            * (fibrePackConst (Module.finrank ℝ E) : ENNReal)
            * (2 : ENNReal) ^ Module.finrank ℝ E * Y
        ≤ Δ * ((ub.branchingN : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)))
    (hKT : ∀ i₂ ∈ s, ConvexSpaceBody.IsKatzTao (fibreIndex s T σb σa i₂) (fibreBodies T σb) Y)
    {i₁ : ι} (hi₁ : i₁ ∈ s) :
    ConvexSpaceBody.IsKatzTao (gapNodeIndexAtScale ub i₁ (5 * σa))
      (fun j => (ub.parentTube j).toConvexSpaceBody) Δ := by
  classical
  set n := Module.finrank ℝ E with hn
  set G := gapNodeIndexAtScale ub i₁ (5 * σa) with hG
  set N := ub.branchingN with hN
  set c := (Tube.le_volume.c n : ENNReal) with hc
  set Cv := (Tube.volume_le.C n : ENNReal) with hCv
  set PK := (fibrePackConst n : ENNReal) with hPK
  rw [ConvexSpaceBody.isKatzTao_iff]
  intro K
  set P := G.filter (fun j => (ub.parentTube j).toConvexSpaceBody ≤ K) with hP
  by_cases hP_empty : P = ∅
  · rw [hP_empty, Finset.sum_empty]
    apply zero_le
  · obtain ⟨j₀, hj₀⟩ := Finset.nonempty_iff_ne_empty.mpr hP_empty
    have hvol_thickening : volume (K.cthickening (σb : ℝ)).carrier
        ≤ (2 : ENNReal) ^ n * volume K.carrier :=
      volume_cthickening_le_of_tube_le (ub.parentTube j₀) K (Finset.mem_filter.mp hj₀).2
    have hvol_sum : (∑ j ∈ P, volume ((ub.parentTube j).carrier))
        ≤ (P.card : ENNReal) * (Cv * (σb : ENNReal) ^ (n - 1)) := by
      calc
        (∑ j ∈ P, volume ((ub.parentTube j).carrier))
            ≤ ∑ _j ∈ P, Cv * (σb : ENNReal) ^ (n - 1) := by
          refine Finset.sum_le_sum fun j _ => ?_
          dsimp [Cv, n]
          simpa using Tube.volume_le hσb1 (ub.parentTube j)
        _ = (P.card : ENNReal) * (Cv * (σb : ENNReal) ^ (n - 1)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    set L := fibreIndex s T δ (5 * σa) i₁ with hL
    have hG_sub_parent : G ⊆ ub.parent := by
      rw [hG, gapNodeIndex_atScale_eq_filter ub i₁ (5 * σa)]
      exact Finset.filter_subset _ _
    have hL_sub_s : L ⊆ s := by
      rw [hL, fibreIndex_self s T (5 * σa) i₁]
      exact Finset.filter_subset _ _
    have hleaf : ∀ j ∈ G, ∀ i ∈ s,
        (T i).toConvexSpaceBody ≤ (ub.parentTube j).toConvexSpaceBody → i ∈ L := by
      intro j hj_G i hi_s hi_body
      rw [hG, gapNodeIndex_atScale_eq_filter ub i₁ (5 * σa)] at hj_G
      rw [hL, fibreIndex_self s T (5 * σa) i₁]
      exact Finset.mem_filter.mpr ⟨hi_s, hi_body.trans (Finset.mem_filter.mp hj_G).2⟩
    have hP_sub_G : P ⊆ G := Finset.filter_subset _ _
    have hP_sub_parent : P ⊆ ub.parent := hP_sub_G.trans hG_sub_parent
    have htemp_parent_card : ((P : Finset ι).card : NNReal) * N
        ≤ Cu ^ 2 * ((L.filter (fun i => (T i).toConvexSpaceBody ≤ K)).card : NNReal) := by
      have htemp := parent_card_mul_branchingN_le_of_subset_atScale ub hδσb P L hP_sub_parent
        hL_sub_s (fun j hj i hi_s hi_body => hleaf j (hP_sub_G hj) i hi_s hi_body) K
      rwa [Finset.filter_true_of_mem fun j hj => (Finset.mem_filter.mp hj).2] at htemp
    have hcard_gapLeaves : ((Kakeya.familyIn L (fun i => (T i).toConvexSpaceBody) K).card : ENNReal)
        * (c * (σb : ENNReal) ^ (n - 1)) ≤ PK * Y * volume (K.cthickening (σb : ℝ)).carrier := by
      simpa [L, hL, c, hn, PK] using
        card_gapLeaves_mul_le hσa hδσb hσb2 (mul_le_mul_left (by norm_num) σa) hKT i₁ K
    set ℓ := (L.filter (fun i => (T i).toConvexSpaceBody ≤ K)).card with hℓ
    have hcard_gapLeaves' : (ℓ : ENNReal) * (c * (σb : ENNReal) ^ (n - 1))
        ≤ PK * Y * volume (K.cthickening (σb : ℝ)).carrier := by
      have h_family_card : (Kakeya.familyIn L (fun i => (T i).toConvexSpaceBody) K).card = ℓ := by
        simp [Kakeya.familyIn, ℓ, hL]
      simpa [h_family_card] using hcard_gapLeaves
    have hN_nonzero : (N : ENNReal) ≠ 0 := by
      have hone : 1 ≤ Cu * N := one_le_mul_branchingN_atScale ub hi₁
      simp only [ne_eq, ENNReal.coe_eq_zero]
      intro hzero
      simp [hzero] at hone
    have hc_nonzero : (c : ENNReal) ≠ 0 := by
      rw [hc]
      exact_mod_cast (Tube.le_volume.c_pos n).ne'
    have hNc_pos : (N : ENNReal) * (c : ENNReal) ≠ 0 := mul_ne_zero hN_nonzero hc_nonzero
    have hNc_finite : (N : ENNReal) * (c : ENNReal) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
    have hparent_card_ENNReal :
        (P.card : ENNReal) * (N : ENNReal) ≤ (Cu : ENNReal) ^ 2 * (ℓ : ENNReal) := by
      exact_mod_cast htemp_parent_card
    have hS_mul : (∑ j ∈ P, volume ((ub.parentTube j).carrier)) * ((N : ENNReal) * (c : ENNReal))
        ≤ Δ * volume K.carrier * ((N : ENNReal) * (c : ENNReal)) := by
      calc
        (∑ j ∈ P, volume ((ub.parentTube j).carrier)) * ((N : ENNReal) * (c : ENNReal))
            ≤ ((P.card : ENNReal) * (Cv * (σb : ENNReal) ^ (n - 1)))
                * ((N : ENNReal) * (c : ENNReal)) := mul_le_mul_left hvol_sum _
        _ = ((P.card : ENNReal) * (N : ENNReal)) * (Cv * (σb : ENNReal) ^ (n - 1) * c) := by ring
        _ ≤ ((Cu : ENNReal) ^ 2 * (ℓ : ENNReal)) * (Cv * (σb : ENNReal) ^ (n - 1) * c) :=
          mul_le_mul_left hparent_card_ENNReal _
        _ = (Cu : ENNReal) ^ 2 * Cv * ((ℓ : ENNReal) * (c * (σb : ENNReal) ^ (n - 1))) := by ring
        _ ≤ (Cu : ENNReal) ^ 2 * Cv * (PK * Y * volume (K.cthickening (σb : ℝ)).carrier) :=
          mul_le_mul_right hcard_gapLeaves' _
        _ ≤ (Cu : ENNReal) ^ 2 * Cv * (PK * Y * ((2 : ENNReal) ^ n * volume K.carrier)) :=
          mul_le_mul_right (mul_le_mul_right hvol_thickening _) _
        _ = (Cv * (Cu : ENNReal) ^ 2 * PK * (2 : ENNReal) ^ n * Y) * volume K.carrier := by ring
        _ ≤ (Δ * ((N : ENNReal) * (c : ENNReal))) * volume K.carrier :=
          mul_le_mul_left (by simpa [mul_assoc] using hΔ) _
        _ = Δ * volume K.carrier * ((N : ENNReal) * (c : ENNReal)) := by ring
    have hsum_eq : (∑ j ∈ G with (ub.parentTube j).toConvexSpaceBody ≤ K,
          volume ((ub.parentTube j).carrier))
        = (∑ j ∈ P, volume ((ub.parentTube j).carrier)) := by
      simp [P]
    rw [hsum_eq]
    exact (ENNReal.mul_le_mul_iff_left hNc_pos hNc_finite).mp hS_mul

/-- **Node-reading Katz–Tao data from leaf-reading Katz–Tao data.**  The bundle reading of
`isKatzTao_gapNodeIndex_of_isKatzTao_gapFibre_atScale`: the level-`k` nodes of `𝒰`, at the fine
scale `σ k` and contained in `T_{i₁}^{(5σa)}`, are `Δ`-Katz–Tao.  The hypothesis `hΔ` carries
`((Cu : ENNReal) ^ 2) ^ 2` because those nodes are the parents of `𝒰.uniformAt hCu hk`. -/
theorem isKatzTao_gapNodeIndex_of_isKatzTao_gapFibre {ι : Type*} {δ σa Cu : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}
    (𝒰 : ChainUniformTubeSet s T N σ Cu) (hCu : 1 ≤ Cu) {k : ℕ} (hk : k ≤ N)
    (hσa : 0 < σa) (hδσb : δ ≤ σ k) (hσb1 : σ k ≤ 1) (hσb2 : 2 * σ k ≤ σa)
    {Y Δ : ENNReal}
    (hΔ : (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * ((Cu : ENNReal) ^ 2) ^ 2
            * (fibrePackConst (Module.finrank ℝ E) : ENNReal)
            * (2 : ENNReal) ^ Module.finrank ℝ E * Y
        ≤ Δ * ((𝒰.branchingN k : ENNReal)
            * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)))
    (hKT : ∀ i₂ ∈ s,
      ConvexSpaceBody.IsKatzTao (fibreIndex s T (σ k) σa i₂) (fibreBodies T (σ k)) Y)
    {i₁ : ι} (hi₁ : i₁ ∈ s) :
    ConvexSpaceBody.IsKatzTao (gapNodeIndex 𝒰 k i₁ (5 * σa))
      (fun j => (𝒰.cover.tube k j).toConvexSpaceBody) Δ :=
  isKatzTao_gapNodeIndex_of_isKatzTao_gapFibre_atScale (𝒰.uniformAt hCu hk) hσa hδσb hσb1 hσb2
    (by rw [ENNReal.coe_pow]; exact hΔ) hKT hi₁

end MultiScaleFac

end Kakeya
