/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Prop66BConstructedOuter
public import Kakeya.DimensionThree.Plank.GlobalPlankFactorizationEstimate
public import Kakeya.DimensionThree.Plank.Prop66BUniverseFree
public import Kakeya.DimensionThree.Plank.InnerEDAssembly

/-!
# GWZ Proposition 6.6(B): the multiplicity split over the constructed Proposition-5.1 output

 This file proves
`Kakeya.factoringAndMultPropGlobal_constructed`, the constructed sibling of
`Kakeya.factoringAndMultPropGlobal`
(`Kakeya/DimensionThree/Plank/GlobalPlankFactorizationEstimate.lean`):
GWZ Proposition 5.1's factoring-and-multiplicity split for Part (B), with the outer family
presented on exact `a × b × 1` planks, essentially distinct, full and Katz--Tao at the master scale,
and the inner family normalised, essentially distinct, full, slab-non-concentrated and of controlled
density — **from the datum alone**, with no `Kakeya.Section6PartBData.Remark53Prop51` and no
essential distinctness of the representative planks.  The two prices, both sub-polynomial, are a
`δ ^ (-ηs)` split constant in place of an absolute one and the datum clauses of the residue
`Kakeya.Prop66BPartBChainConstructed`.

It also contains the universe adapter
`Kakeya.KatzTaoEstimate.exists_threshold_multiplicity_bound_univ` for GWZ Lemma 3.7, which the
residue's large-`a` regime needs.

The five steps of the proof are listed in the docstring of the main theorem.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody Filter Topology
open scoped NNReal Real ENNReal

noncomputable section

universe u v w

namespace Kakeya

set_option maxHeartbeats 2000000 in
-- the datum restriction, the constructed output and the inner pipeline are each unfolded once
open Classical in
/-- **GWZ Proposition 5.1 (factoring and multiplicity) for 6.6(B), over the constructed output.**

The constructed sibling of `Kakeya.factoringAndMultPropGlobal`: the same conclusion (the outer
`a × b × 1` plank family with essential distinctness, window, master-scale fullness and Katz--Tao;
the normalised inner plank family with its fullness, density transfer, slab non-concentration and
essential distinctness; the cardinality relation; the multiplicity split), with three differences:

* **no `Kakeya.Section6PartBData.Remark53Prop51`** and **no outer-representative essential
  distinctness** among the hypotheses — the outer family is the plank presentation of the
  constructed Proposition-5.1 output (`Kakeya.PartBLoss.exists_threshold_constructedProp51Output`)
  and its essential distinctness is *extracted* (`Kakeya.exists_pairwise_ED_collarPlank_subfamily`);
* the three datum clauses of the residue `Kakeya.Prop66BPartBChainConstructed` in their place:
  nonempty coarse fibres and plank dimensions of the cell bodies (the third, GWZ Lemma 4.1(ii), is
  not needed by this route);
* the split constant is **`δ ^ (-ηs)`** for an input exponent `ηs`, not an absolute `Csplit`, and
  the cardinality constant is the absolute `2` of the block pigeonhole
  (`Kakeya.BlockCount.exists_restrictCells_block_equalised`).  Both changes follow the design of
  `exists_remark53Prop51_of_datum` on `origin/numina/22`
  (`Kakeya/DimensionThree/Plank/Section6PartBSubpolynomial.lean:779` there; read for strategy only).

**The proof.**  (1) Block pigeonhole to a sub-datum on which the cell blocks are comparable, at the
logarithmic loss `L`
(`Kakeya.Section6PartBData.exists_threshold_dyadicPigeonholeNatConstant_le_rpow_neg`).
(2) The constructed Proposition-5.1 output on that sub-datum, on one family `O`.  (3) The
essentially distinct subfamily of the presented outer family, at the loss `⌈C₀ · cc⌉₊ + 1`, which is
sub-polynomial because `cc = collarConflictPoly · K ^ 6` (`Kakeya.collarConflictConst_eq`).
(4) The tree's inner pipeline `Kakeya.exists_partB_selected_inner_ED_package`, run on the datum
re-shaded with `O`'s inner shades (`Kakeya.Section6PartBData.withShades`) and restricted to `O`'s
outer cells, so that its fibre *is* `O`'s fibre and its inner family *is* `O`'s inner family.
(5) The exponent ledger: the produced `η` is
`min (η'/2) (ηₒ/16) (ηᵢ/8) e (ηs/16)` with `e = min (ηᵢ/6) (ηs/4)`; the split loss is
`L · Cs · (⌈C₀ cc⌉₊ + 1) · (d + 1) ≤ δ ^ (-(e + 10η)) ≤ δ ^ (-ηs)`.

`hKKT` and `hKF` are not needed: the two applications of GWZ Lemma 6.1 are made by the consumer. -/
theorem factoringAndMultPropGlobal_constructed :
    ∃ Cinner : ℝ≥0, 1 ≤ Cinner ∧
      ∀ (ηₒ ηᵢ ηs : ℝ), 0 < ηₒ → 0 < ηᵢ → 0 < ηs → ∀ (b₀ᵢ : ℝ≥0), 0 < b₀ᵢ →
      ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
      ∀ {ι : Type u} (q : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        δ ≤ δ₀ →
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (q : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1),
          δ ≤ ρ → ρ ≤ a → δ + 2 * a ≤ 1 → δ ≤ b₀ᵢ * a →
          ∀ {κ : Type v} (r : Finset κ)
            (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF C₀ K : ℝ≥0),
            C₀ ≤ δ ^ (-η) → CF ≤ δ ^ (-η) → Cfib ≤ δ ^ (-η) → K ≤ δ ^ (-η) →
            ∀ (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀),
            (∀ x ∈ D.factor.cells, (D.factor.coarseFibre x).Nonempty) →
            (∀ x ∈ D.factor.cells, IsPlankOfDimensions K a b (D.factor.body x)) →
            ∃ (ts : Finset D.factor.Cell) (W : D.factor.Cell → ShadedPlank a b hab hb1),
              ts.Nonempty ∧ ts ⊆ D.factor.cells ∧
              ((ts : Set D.factor.Cell).Pairwise
                (fun x y => _root_.IsEssentiallyDistinct (W x).carrier (W y).carrier)) ∧
              (∀ j ∈ ts, (W j).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
              (δ : ℝ≥0) ^ ηₒ ≤ ShadedBody.fullness ts (fun j => (W j).toShadedBody) ∧
              IsKatzTao ts (fun j => (W j).toConvexSpaceBody) (δ ^ (-ηₒ)) ∧
              ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1) (ιj : Type)
                (qj : Finset ιj) (Pj : ιj → ShadedPlank a' b' ha'b' hb'1),
                0 < a' ∧ δ ≤ a' ∧ b' ≤ b₀ᵢ ∧
                ((a' : ENNReal) / (b' : ENNReal) = (a : ENNReal) / (b : ENNReal)) ∧
                (∀ i ∈ qj, (Pj i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
                (qj : Set ιj).Pairwise
                  (fun i j => _root_.IsEssentiallyDistinct (Pj i).carrier (Pj j).carrier) ∧
                (δ : ℝ≥0) ^ ηᵢ ≤ ShadedBody.fullness qj (fun i => (Pj i).toShadedBody) ∧
                maxDensity qj (fun i => (Pj i).toConvexSpaceBody)
                  ≤ (Cinner : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) ∧
                (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a' / b' ≤ φ →
                    ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
                    ((Plank.inWideSlabFamily qj (fun i => (Pj i).toPrism3D) S).card : ℝ≥0)
                      ≤ δ ^ (-ηᵢ) * φ ^ (1 : ℝ) * (qj.card : ℝ≥0)) ∧
                ((ts.card : ENNReal) * (qj.card : ENNReal)
                  ≤ (2 : ENNReal) * (q.card : ENNReal)) ∧
                ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
                  (δ : ENNReal) ^ (-ηs) *
                    ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) *
                    ShadedBody.multiplicity qj (fun i => (Pj i).toShadedBody) := by
  classical
  obtain ⟨Cnorm, Cvol, d, δconf, hCnorm, hCvol, hdpos, hδconfpos, hδconfle, hInner⟩ :=
    exists_partB_selected_inner_ED_package
  refine ⟨Cnorm, hCnorm, ?_⟩
  intro ηₒ ηᵢ ηs hηₒ hηᵢ hηs b₀ᵢ hb₀ᵢ
  -- the exponent budget
  set e : ℝ := min (ηᵢ / 6) (ηs / 4) with he_def
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have he_i : e ≤ ηᵢ / 6 := min_le_left _ _
  have he_s : e ≤ ηs / 4 := min_le_right _ _
  obtain ⟨d₁, hd₁, η', hη', hCons⟩ :=
    PartBLoss.exists_threshold_constructedProp51Output.{u, v}
      (show (0 : ℝ) < ηₒ / 2 by positivity) he
  set η : ℝ := min (η' / 2) (min (ηₒ / 16) (min (ηᵢ / 8) (min e (ηs / 16)))) with hη_def
  have hη : 0 < η := by
    refine lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min he (by positivity))))
  have hηη' : η ≤ η' / 2 := min_le_left _ _
  have hηₒ16 : η ≤ ηₒ / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hηᵢ8 : η ≤ ηᵢ / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηe : η ≤ e := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hηs16 : η ≤ ηs / 16 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  -- thresholds
  obtain ⟨d₂, hd₂, hLfun⟩ :=
    Section6PartBData.exists_threshold_dyadicPigeonholeNatConstant_le_rpow_neg hη
  set Cc : ℝ≥0 := max 1 (collarConflictPoly plankWindowRadius 11 + 2) with hCc
  obtain ⟨d₃, hd₃, hfun₃⟩ := exists_threshold_le_rpow_neg Cc (le_max_left _ _) hη
  set Ce : ℝ≥0 := max 1 (envelopeWindowPoly plankWindowRadius * Metric.volume_comparison.C 3)
    with hCe
  obtain ⟨d₄, hd₄, hfun₄⟩ := exists_threshold_le_rpow_neg Ce (le_max_left _ _) hη
  have hd1 : (1 : ℝ≥0) ≤ (d : ℝ≥0) + 1 := le_add_self
  have hCnd1 : (1 : ℝ≥0) ≤ Cnorm * ((d : ℝ≥0) + 1) :=
    one_le_mul_of_one_le_of_one_le hCnorm hd1
  obtain ⟨d₅, hd₅, hfun₅⟩ :=
    exists_threshold_le_rpow_neg (Cnorm * ((d : ℝ≥0) + 1)) hCnd1
      (show (0 : ℝ) < ηᵢ / 2 by positivity)
  obtain ⟨d₆, hd₆, hfun₆⟩ := exists_threshold_le_rpow_neg ((d : ℝ≥0) + 1) hd1 hη
  set Cslab : ℝ≥0 := max 1 (((d : ℝ≥0) + 1) * (innerCoarseTubeVolumeRatio * Cvol)) with hCslab
  obtain ⟨d₇, hd₇, hfun₇⟩ :=
    exists_threshold_le_rpow_neg Cslab (le_max_left _ _) (show (0 : ℝ) < ηᵢ / 2 by positivity)
  have hconf0 : 0 < Real.toNNReal δconf := Real.toNNReal_pos.mpr hδconfpos
  refine ⟨η, hη, min (min (min d₁ d₂) (min d₃ d₄))
    (min (min d₅ d₆) (min d₇ (min (Real.toNNReal δconf) (1 / 2)))),
    lt_min (lt_min (lt_min hd₁ hd₂) (lt_min hd₃ hd₄))
      (lt_min (lt_min hd₅ hd₆) (lt_min hd₇ (lt_min hconf0 (by norm_num)))), ?_⟩
  intro ι q δ hδ0 T hδ hball hEDq hfull ρ a b hab hb1 hδρ hρa hsmall hδb₀ᵢ κ r R m Cfib CF C₀ K
    hC₀ hCF hCfib hK D hcfne hdimK
  -- unwind the threshold
  have hδd₁ : δ ≤ d₁ :=
    hδ.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hδd₂ : δ ≤ d₂ :=
    hδ.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hδd₃ : δ ≤ d₃ :=
    hδ.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hδd₄ : δ ≤ d₄ :=
    hδ.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hδd₅ : δ ≤ d₅ :=
    hδ.trans (((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hδd₆ : δ ≤ d₆ :=
    hδ.trans (((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hδd₇ : δ ≤ d₇ :=
    hδ.trans (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hδconfN : δ ≤ Real.toNNReal δconf :=
    hδ.trans (((min_le_right _ _).trans (min_le_right _ _)).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hδhalfN : δ ≤ 1 / 2 :=
    hδ.trans (((min_le_right _ _).trans (min_le_right _ _)).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hδconf : (δ : ℝ) ≤ δconf := by
    have h := NNReal.coe_le_coe.mpr hδconfN
    rwa [Real.coe_toNNReal _ hδconfpos.le] at h
  have hδhalf : (δ : ℝ) ≤ 1 / 2 := by
    have h := NNReal.coe_le_coe.mpr hδhalfN
    simpa using h
  -- the scales
  have hδa : δ ≤ a := hδρ.trans hρa
  have ha0 : 0 < a := lt_of_lt_of_le hδ0 hδa
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ0 hδρ
  have hρ1 : ρ ≤ 1 := hρa.trans (hab.trans hb1)
  have ha1 : a ≤ 1 := hab.trans hb1
  have hδ1 : δ ≤ 1 := hδa.trans ha1
  have hδne : δ ≠ 0 := hδ0.ne'
  have hδE0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδne
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hpow : ∀ {s t : ℝ}, s ≤ t → (δ : ℝ≥0) ^ (-s) ≤ δ ^ (-t) :=
    fun hst => NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (neg_le_neg hst)
  have hpow' : ∀ {s t : ℝ}, s ≤ t → (δ : ℝ≥0) ^ t ≤ δ ^ s :=
    fun hst => NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hst
  have hone : (1 : ℝ≥0) ≤ δ ^ (-η) := by
    have := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (show -η ≤ (0 : ℝ) by linarith)
    simpa using this
  have hrpow_add : ∀ s t : ℝ, (δ : ℝ≥0) ^ s * δ ^ t = δ ^ (s + t) :=
    fun s t => (NNReal.rpow_add hδne s t).symm
  -- the plank-dimension constant, made `≥ 1`
  set K' : ℝ≥0 := max 1 K with hK'
  have hK'1 : (1 : ℝ≥0) ≤ K' := le_max_left _ _
  have hK'η : K' ≤ δ ^ (-η) := max_le hone hK
  have hdimK' : ∀ x ∈ D.factor.cells, IsPlankOfDimensions K' a b (D.factor.body x) :=
    fun x hx => (hdimK x hx).mono_constant (le_max_right _ _)
  have hR : (1 : ℝ≥0) ≤ plankWindowRadius := Section6PartBData.one_le_plankWindowRadius
  -- ================================================================
  -- STEP 1: the block pigeonhole
  -- ================================================================
  obtain ⟨cells', hsub, -, -, hcount, href, hmultL⟩ :=
    BlockCount.exists_restrictCells_block_equalised D
  set q' : Finset ι := BlockCount.restrictFine D cells' with hq'
  have hq'sub : q' ⊆ q := fun i hi => (BlockCount.mem_restrictFine_iff.mp hi).1
  set L : ℝ≥0 := (Kakeya.dyadicPigeonholeNatConstant q.card : ℝ≥0) with hL
  have hLE : (L : ENNReal) ≤ (δ : ENNReal) ^ (-η) := by
    have h := hLfun δ hδ0 hδd₂ q T hball hEDq
    simpa [hL] using h
  have hL0 : L ≠ 0 := by
    simp [hL, Kakeya.dyadicPigeonholeNatConstant]
  have hLinv : (δ : ℝ≥0) ^ η ≤ L⁻¹ :=
    PartBLoss.rpow_le_of_coe_rpow_le hδ0 (PartBLoss.rpow_le_inv_of_le_rpow_neg hL0 hLE)
  have hLNN : L ≤ δ ^ (-η) := by
    have h : (L : ENNReal) ≤ ((δ ^ (-η) : ℝ≥0) : ENNReal) := by
      rw [ENNReal.coe_rpow_of_ne_zero hδne]; exact hLE
    exact ENNReal.coe_le_coe.mp h
  -- fullness of the pigeonholed family
  have hfullpos : 0 < ShadedBody.fullness q (fun i => (T i).toShadedBody) :=
    lt_of_lt_of_le (NNReal.rpow_pos hδ0) hfull
  have hshadeq : (∑ i ∈ q, volume ((T i).toShadedBody).shade) ≠ 0 :=
    ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos q (fun i => (T i).toShadedBody) hfullpos
  have hB0q : (∑ i ∈ q, volume ((T i).toShadedBody).carrier) ≠ 0 :=
    ShadedBody.sum_volume_carrier_ne_zero_of_sum_shade_ne_zero q _ hshadeq
  have hBtopq : (∑ i ∈ q, volume ((T i).toShadedBody).carrier) ≠ ⊤ :=
    ShadedBody.sum_volume_carrier_ne_top q _
  have hfullq' : L⁻¹ * ShadedBody.fullness q (fun i => (T i).toShadedBody)
      ≤ ShadedBody.fullness q' (fun i => (T i).toShadedBody) :=
    mul_fullness_le_of_isCRefinement href hB0q hBtopq
  have hfull2η : (δ : ℝ≥0) ^ (2 * η) ≤ ShadedBody.fullness q' (fun i => (T i).toShadedBody) := by
    calc (δ : ℝ≥0) ^ (2 * η) = δ ^ η * δ ^ η := by rw [hrpow_add]; congr 1; ring
      _ ≤ L⁻¹ * ShadedBody.fullness q (fun i => (T i).toShadedBody) := mul_le_mul' hLinv hfull
      _ ≤ _ := hfullq'
  have hfull' : (δ : ℝ≥0) ^ η' ≤ ShadedBody.fullness q' (fun i => (T i).toShadedBody) :=
    (hpow' (by linarith)).trans hfull2η
  have hfullq'pos : 0 < ShadedBody.fullness q' (fun i => (T i).toShadedBody) :=
    lt_of_lt_of_le (NNReal.rpow_pos hδ0) hfull'
  have hmass' : 0 < ∑ i ∈ q', volume (T i).shade :=
    pos_iff_ne_zero.mpr
      (ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos q' (fun i => (T i).toShadedBody)
        hfullq'pos)
  have hball' : ∀ i ∈ q', ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1 := fun i hi => hball i (hq'sub hi)
  have hEDq' : (q' : Set ι).Pairwise (fun i j =>
      _root_.IsEssentiallyDistinct ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :=
    hEDq.mono (Finset.coe_subset.mpr hq'sub)
  have hcfne' : ∀ x ∈ (BlockCount.restrictCells D cells' hsub).factor.cells,
      ((BlockCount.restrictCells D cells' hsub).factor.coarseFibre x).Nonempty := by
    intro x hx
    have hx' : x ∈ cells' := hx
    rw [Section6PartBData.restrictCells_coarseFibre_eq D hsub hx']
    exact hcfne x (hsub hx')
  have hdimK'' : ∀ x ∈ (BlockCount.restrictCells D cells' hsub).factor.cells,
      IsPlankOfDimensions K' a b ((BlockCount.restrictCells D cells' hsub).factor.body x) := by
    intro x hx
    have hx' : x ∈ cells' := hx
    exact hdimK' x (hsub hx')
  -- ================================================================
  -- STEP 2: the constructed Proposition-5.1 output on the pigeonholed datum
  -- ================================================================
  obtain ⟨O, Cs, cref, hO, hCs, hcref⟩ :=
    hCons (BlockCount.restrictCells D cells' hsub) hK'1 hδ0 hδd₁ hδhalf hρ0 hρ1 hδa hb0 hball'
      hmass' hsmall hcfne' hdimK'' hEDq'
      (hK'η.trans (hpow (by linarith))) (hCfib.trans (hpow (by linarith)))
      (hCF.trans (hpow (by linarith))) hfull'
  have hOcells : O.outerSet ⊆ D.factor.cells := hO.outerSet_subset.trans hsub
  -- the presented outer family
  set W : D.factor.Cell → ShadedPlank a b hab hb1 :=
    fun j => collarPlank hR hK'1 hab hb1 (D.factor.body j) (O.outerBody j) with hW
  have hdimO : ∀ j ∈ O.outerSet, IsPlankOfDimensions K' a b (D.factor.body j) :=
    fun j hj => hdimK' j (hOcells hj)
  have hKTO : IsKatzTao O.outerSet D.factor.body (C₀ : ENNReal) :=
    D.factor.isKatzTao.subset hOcells
  -- ================================================================
  -- STEP 3: the essentially distinct outer subfamily
  -- ================================================================
  obtain ⟨ts, htssub, hED, hcardts, hshadets⟩ :=
    exists_pairwise_ED_collarPlank_subfamily hR hK'1 hab hb1 ha0 (C₀ := C₀) O.outerSet
      D.factor.body O.outerBody hdimO hO.presentable hKTO
  set cc : ℝ≥0 := collarConflictConst plankWindowRadius K' 11 with hcc
  set dn : ℕ := ⌈((C₀ * cc : ℝ≥0) : ℝ)⌉₊ with hdn
  set Dext : ℝ≥0 := (dn : ℝ≥0) + 1 with hDext
  have hDextE : ((dn : ENNReal) + 1) = (Dext : ENNReal) := by
    rw [hDext]; push_cast; ring
  have hDext8 : Dext ≤ δ ^ (-(8 * η)) := by
    have hx0 : (0 : ℝ) ≤ ((C₀ * cc : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    have hceil : ((dn : ℕ) : ℝ) < ((C₀ * cc : ℝ≥0) : ℝ) + 1 := Nat.ceil_lt_add_one hx0
    have hDextR : ((Dext : ℝ≥0) : ℝ) ≤ ((C₀ * cc + 2 : ℝ≥0) : ℝ) := by
      rw [hDext]; push_cast at hceil ⊢; linarith
    have hDext1 : Dext ≤ C₀ * cc + 2 := NNReal.coe_le_coe.mp hDextR
    have hcceq : cc = collarConflictPoly plankWindowRadius 11 * K' ^ 6 :=
      collarConflictConst_eq _ _ _
    have hK'6 : K' ^ 6 ≤ δ ^ (-(6 * η)) := by
      calc K' ^ 6 ≤ (δ ^ (-η)) ^ 6 := pow_le_pow_left' hK'η 6
        _ = δ ^ (-(6 * η)) := by
          rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]; congr 1; push_cast; ring
    have hone7 : (1 : ℝ≥0) ≤ δ ^ (-(7 * η)) := by
      have := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (show -(7 * η) ≤ (0 : ℝ) by linarith)
      simpa using this
    have hCcδ : Cc ≤ δ ^ (-η) := hfun₃ δ hδ0 hδd₃
    calc Dext ≤ C₀ * cc + 2 := hDext1
      _ = C₀ * (collarConflictPoly plankWindowRadius 11 * K' ^ 6) + 2 := by rw [hcceq]
      _ ≤ δ ^ (-η) * (collarConflictPoly plankWindowRadius 11 * δ ^ (-(6 * η))) + 2 := by
          gcongr
      _ = collarConflictPoly plankWindowRadius 11 * δ ^ (-(7 * η)) + 2 := by
          rw [show δ ^ (-η) * (collarConflictPoly plankWindowRadius 11 * δ ^ (-(6 * η)))
            = collarConflictPoly plankWindowRadius 11 * (δ ^ (-η) * δ ^ (-(6 * η))) by ring,
            hrpow_add, show -η + -(6 * η) = -(7 * η) by ring]
      _ ≤ collarConflictPoly plankWindowRadius 11 * δ ^ (-(7 * η)) + 2 * δ ^ (-(7 * η)) := by
          gcongr
          calc (2 : ℝ≥0) = 2 * 1 := (mul_one 2).symm
            _ ≤ 2 * δ ^ (-(7 * η)) := by gcongr
      _ = (collarConflictPoly plankWindowRadius 11 + 2) * δ ^ (-(7 * η)) := by ring
      _ ≤ Cc * δ ^ (-(7 * η)) := by gcongr; exact le_max_right _ _
      _ ≤ δ ^ (-η) * δ ^ (-(7 * η)) := by gcongr
      _ = δ ^ (-(8 * η)) := by rw [hrpow_add]; congr 1; ring
  have hDext0 : Dext ≠ 0 := by
    rw [hDext]; positivity
  have hDextinv : (δ : ℝ≥0) ^ (8 * η) ≤ Dext⁻¹ := by
    refine PartBLoss.rpow_le_of_coe_rpow_le hδ0 (PartBLoss.rpow_le_inv_of_le_rpow_neg hDext0 ?_)
    rw [← ENNReal.coe_rpow_of_ne_zero hδne]
    exact_mod_cast hDext8
  -- nonempty, inside the cells
  have htsne : ts.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.card_empty, mul_zero, Nat.le_zero, Finset.card_eq_zero] at hcardts
    exact hO.outerSet_nonempty.ne_empty hcardts
  have htscells : ts ⊆ D.factor.cells := htssub.trans hOcells
  -- the window
  have hWwin : ∀ j ∈ ts, ((W j).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ) := by
    intro j hj
    exact collarPlank_carrier_subset_window hR hK'1 hab hb1 (O.outerBody j)
      (D.body_carrier_subset_window (htscells hj))
  -- the outer fullness
  have hWfullO : (δ : ℝ≥0) ^ (ηₒ / 2)
      ≤ ShadedBody.fullness O.outerSet (fun j => (W j).toShadedBody) := hO.outer_fullness
  have hshadets' : ∑ j ∈ O.outerSet, volume ((W j).toShadedBody).shade
      ≤ (Dext : ENNReal) * ∑ j ∈ ts, volume ((W j).toShadedBody).shade := by
    rw [← hDextE]
    exact hshadets
  have hrefW : ShadedBody.IsCRefinement ts (fun j => (W j).toShadedBody) O.outerSet
      (fun j => (W j).toShadedBody) Dext⁻¹ :=
    ShadedBody.isCRefinement_of_isRefinement_of_sum_le _ _ _ _
      ⟨htssub, fun _ _ => ⟨rfl, subset_rfl⟩⟩ hshadets'
  have hB0W : (∑ j ∈ O.outerSet, volume ((W j).toShadedBody).carrier) ≠ 0 :=
    sum_volume_carrier_collarPlank_ne_zero hR hK'1 hab hb1 ha0 hb0 hO.outerSet_nonempty
      D.factor.body O.outerBody
  have hBtopW : (∑ j ∈ O.outerSet, volume ((W j).toShadedBody).carrier) ≠ ⊤ :=
    ShadedBody.sum_volume_carrier_ne_top _ _
  have hWfull : (δ : ℝ≥0) ^ ηₒ ≤ ShadedBody.fullness ts (fun j => (W j).toShadedBody) := by
    calc (δ : ℝ≥0) ^ ηₒ ≤ δ ^ (8 * η + ηₒ / 2) := hpow' (by linarith)
      _ = δ ^ (8 * η) * δ ^ (ηₒ / 2) := (hrpow_add _ _).symm
      _ ≤ Dext⁻¹ * ShadedBody.fullness O.outerSet (fun j => (W j).toShadedBody) :=
          mul_le_mul' hDextinv hWfullO
      _ ≤ ShadedBody.fullness ts (fun j => (W j).toShadedBody) :=
          mul_fullness_le_of_isCRefinement hrefW hB0W hBtopW
  -- the outer Katz--Tao clause
  have hWKT : IsKatzTao ts (fun j => (W j).toConvexSpaceBody) ((δ : ENNReal) ^ (-ηₒ)) := by
    have hKT0 := isKatzTao_collarPlank hR hK'1 hab hb1 ha0 hb0 O.outerSet D.factor.body
      O.outerBody hO.presentable hdimO hKTO
    refine (hKT0.subset htssub).mono ?_
    set Menv : ℝ≥0 :=
      flatPrismEnvelopeVolumeRatio.C (windowPlankEnvelope.windowConst plankWindowRadius K')
      with hMenv
    have hMenvle : Menv ≤ envelopeWindowPoly plankWindowRadius * K' ^ 6 :=
      flatPrismEnvelopeVolumeRatio_windowConst_le hK'1
    have hK'6 : K' ^ 6 ≤ δ ^ (-(6 * η)) := by
      calc K' ^ 6 ≤ (δ ^ (-η)) ^ 6 := pow_le_pow_left' hK'η 6
        _ = δ ^ (-(6 * η)) := by
          rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]; congr 1; push_cast; ring
    have hCeδ : Ce ≤ δ ^ (-η) := hfun₄ δ hδ0 hδd₄
    have hNN : Menv * (Metric.volume_comparison.C 3 * C₀) ≤ δ ^ (-ηₒ) := by
      calc Menv * (Metric.volume_comparison.C 3 * C₀)
          ≤ (envelopeWindowPoly plankWindowRadius * K' ^ 6)
              * (Metric.volume_comparison.C 3 * C₀) := by gcongr
        _ = (envelopeWindowPoly plankWindowRadius * Metric.volume_comparison.C 3)
              * K' ^ 6 * C₀ := by ring
        _ ≤ Ce * δ ^ (-(6 * η)) * δ ^ (-η) := by
            gcongr
            exact le_max_right _ _
        _ ≤ δ ^ (-η) * δ ^ (-(6 * η)) * δ ^ (-η) := by gcongr
        _ = δ ^ (-(8 * η)) := by
            rw [hrpow_add, hrpow_add]; congr 1; ring
        _ ≤ δ ^ (-ηₒ) := hpow (by linarith)
    calc (flatPrismEnvelopeVolumeRatio.C (windowPlankEnvelope.windowConst plankWindowRadius K')
          : ENNReal) * ((Metric.volume_comparison.C 3 : ENNReal) * (C₀ : ENNReal))
        = ((Menv * (Metric.volume_comparison.C 3 * C₀) : ℝ≥0) : ENNReal) := by
          rw [hMenv]; push_cast; ring
      _ ≤ ((δ ^ (-ηₒ) : ℝ≥0) : ENNReal) := by exact_mod_cast hNN
      _ = (δ : ENNReal) ^ (-ηₒ) := ENNReal.coe_rpow_of_ne_zero hδne _
  -- the outer multiplicity, transported to the extracted subfamily
  have hmultOW : ShadedBody.multiplicity O.outerSet O.outerBody
      = ShadedBody.multiplicity O.outerSet (fun j => (W j).toShadedBody) :=
    (multiplicity_collarPlank hR hK'1 hab hb1 O.outerSet D.factor.body O.outerBody
      hO.presentable).symm
  have hmultWts : ShadedBody.multiplicity O.outerSet (fun j => (W j).toShadedBody)
      ≤ (Dext : ENNReal) * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) :=
    BlockCount.multiplicity_le_mul_of_subset htssub hshadets'
  -- ================================================================
  -- STEP 4: the inner pipeline on the constructed inner family
  -- ================================================================
  have hsubO : O.outerSet ⊆ (BlockCount.restrictCells D cells' hsub).factor.cells :=
    hO.outerSet_subset
  have hYsub : ∀ i, (O.innerBody i).shade ⊆ (T i).carrier := by
    intro i
    have h := (O.innerBody i).shade_subset
    have hcar : ((O.innerBody i).carrier : Set (EuclideanSpace ℝ (Fin 3))) = (T i).carrier :=
      congrArg ConvexSpaceBody.carrier (hO.inner_carrier i)
    rwa [hcar] at h
  set T'' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)) := fun i =>
    (T i).reshade (O.innerBody i).shade (O.innerBody i).measurableSet_shade (hYsub i) with hT''
  set q'' : Finset ι := BlockCount.restrictFine (BlockCount.restrictCells D cells' hsub) O.outerSet
    with hq''
  have hq''eq : q'' = O.innerSet := by
    ext i
    rw [hq'', BlockCount.mem_restrictFine_iff, hO.mem_innerSet_iff i]
  have hq''q' : q'' ⊆ q' := fun i hi => (BlockCount.mem_restrictFine_iff.mp hi).1
  have hq''q : q'' ⊆ q := hq''q'.trans hq'sub
  have hcarT'' : ∀ i, ((T'' i).carrier : Set (EuclideanSpace ℝ (Fin 3))) = (T i).carrier :=
    fun _ => rfl
  have hEDq'' : (q'' : Set ι).Pairwise (fun i j =>
      _root_.IsEssentiallyDistinct ((T'' i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((T'' j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
    intro i hi j hj hij
    exact hEDq (hq''q hi) (hq''q hj) hij
  have hne'' :
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.outerSet.Nonempty :=
    hO.outerSet_nonempty
  have hinnerSet'' :
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.innerSet
      = ({i ∈ q'' |
          ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
            hsubO).withShades (fun i => (O.innerBody i).shade)
            (fun i => (O.innerBody i).measurableSet_shade) hYsub).cellOfFine i ∈
          ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
            hsubO).withShades (fun i => (O.innerBody i).shade)
            (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.outerSet} :
          Finset ι) := by
    change q'' = ({i ∈ q'' | D.cellOfFine i ∈ O.outerSet} : Finset ι)
    symm
    refine Finset.filter_true_of_mem ?_
    intro i hi
    exact (BlockCount.mem_restrictFine_iff.mp hi).2
  have hbody'' : ∀ i ∈ q'', (
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.innerBody
        i).toConvexSpaceBody
      = (T'' i).toConvexSpaceBody := fun _ _ => rfl
  have hcfibne'' : ∀ x ∈
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.outerSet, (
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).factor.coarseFibre x).Nonempty := by
    intro x hx
    have hx' : x ∈ O.outerSet := hx
    change ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
      hsubO).factor.coarseFibre x).Nonempty
    rw [Section6PartBData.restrictCells_coarseFibre_eq (BlockCount.restrictCells D cells' hsub)
      hsubO hx']
    exact hcfne' x (hsubO hx')
  have hsubO'' :
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.outerSet ⊆
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).factor.cells := Finset.Subset.refl _
  -- the constructed inner family has positive fullness
  have hB0q' : (∑ i ∈ q', volume ((T i).toShadedBody).carrier) ≠ 0 :=
    ShadedBody.sum_volume_carrier_ne_zero_of_sum_shade_ne_zero q' _ hmass'.ne'
  have hBtopq' : (∑ i ∈ q', volume ((T i).toShadedBody).carrier) ≠ ⊤ :=
    ShadedBody.sum_volume_carrier_ne_top q' _
  have hfullO : cref * ShadedBody.fullness q' (fun i => (T i).toShadedBody)
      ≤ ShadedBody.fullness O.innerSet O.innerBody :=
    mul_fullness_le_of_isCRefinement hO.refinement hB0q' hBtopq'
  have hfullOlow : (δ : ℝ≥0) ^ (e + 2 * η) ≤ ShadedBody.fullness O.innerSet O.innerBody := by
    calc (δ : ℝ≥0) ^ (e + 2 * η) = δ ^ e * δ ^ (2 * η) := (hrpow_add _ _).symm
      _ ≤ cref * ShadedBody.fullness q' (fun i => (T i).toShadedBody) := mul_le_mul' hcref hfull2η
      _ ≤ _ := hfullO
  have hfullOpos : 0 < ShadedBody.fullness O.innerSet O.innerBody :=
    lt_of_lt_of_le (NNReal.rpow_pos hδ0) hfullOlow
  -- the fine family of the re-shaded datum is the constructed inner family
  have hcarO : ∀ i, ((T'' i).toShadedBody).carrier = (O.innerBody i).carrier := by
    intro i
    exact (congrArg ConvexSpaceBody.carrier (hO.inner_carrier i)).symm
  have hshadeO : ∀ i, ((T'' i).toShadedBody).shade = (O.innerBody i).shade := fun _ => rfl
  have hfull''eq : ShadedBody.fullness
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.innerSet
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.innerBody
      = ShadedBody.fullness O.innerSet O.innerBody := by
    change ShadedBody.fullness q'' (fun i => (T'' i).toShadedBody)
      = ShadedBody.fullness O.innerSet O.innerBody
    rw [← ENNReal.coe_inj, ShadedBody.fullness_def, ShadedBody.fullness_def, hq''eq]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => congrArg volume (hcarO i))
  have hB0r : (∑ i ∈
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.innerSet, volume (
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.innerBody
        i).carrier) ≠ 0 := by
    change (∑ i ∈ q'', volume ((T'' i).toShadedBody).carrier) ≠ 0
    have hshade0 : (∑ i ∈ O.innerSet, volume (O.innerBody i).shade) ≠ 0 :=
      ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos _ _ hfullOpos
    have hcar0 : (∑ i ∈ O.innerSet, volume (O.innerBody i).carrier) ≠ 0 :=
      ShadedBody.sum_volume_carrier_ne_zero_of_sum_shade_ne_zero _ _ hshade0
    have hsumeq : (∑ i ∈ O.innerSet, volume ((T'' i).toShadedBody).carrier)
        = ∑ i ∈ O.innerSet, volume (O.innerBody i).carrier :=
      Finset.sum_congr rfl (fun i _ => congrArg volume (hcarO i))
    rw [hq''eq, hsumeq]
    exact hcar0
  have hBtopr : (∑ i ∈
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.innerSet, volume (
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.innerBody i).carrier)
      ≠ ⊤ := ShadedBody.sum_volume_carrier_ne_top _ _
  obtain ⟨x₀, hx₀, hfibsel, a', b', ha'b', hb'1, ιj, qj, Pj, hSel⟩ :=
    hInner (δ := δ) hδ0 hδconf hEDq'' ha0 hδa hρ0 hρ1 hρa (1 : ℝ≥0) b₀ᵢ
      (by simpa using (hδa.trans hab)) hδb₀ᵢ
          ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
            hsubO).withShades (fun i => (O.innerBody i).shade)
            (fun i => (O.innerBody i).measurableSet_shade) hYsub)
          hne'' hinnerSet'' hbody'' hcfibne'' hsubO''
      hB0r hBtopr
  have hx₀O : x₀ ∈ O.outerSet := hx₀
  rcases hSel with
    ⟨ha'pos, hδa', hb'b₀, hratioENN, hratioNN, hwindowP, hpairP, hcardfib,
      hfullraw, hmaxdP, hslabraw, hmultraw⟩
  -- the pipeline's fibre is the constructed fibre
  have hfibeq :
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.fiber x₀ = O.fiber x₀ := by
    ext i
    change i ∈
        ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
          hsubO).withShades (fun i => (O.innerBody i).shade)
          (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineFibre x₀ ↔ i ∈ O.fiber x₀
    rw [Section6PartBData.mem_fineFibre_iff]
    simp only [ShadedBody.ShadedFactorFamily.fiber, Finset.mem_filter]
    rw [show
        ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
          hsubO).withShades (fun i => (O.innerBody i).shade)
          (fun i => (O.innerBody i).measurableSet_shade) hYsub).cellOfFine i = D.cellOfFine i
        from rfl, ← hq''eq, hO.parent_eq i]
    exact Iff.rfl
  have hmultfib : ShadedBody.multiplicity (
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.fiber x₀)
      ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
        hsubO).withShades (fun i => (O.innerBody i).shade)
        (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.innerBody
      = ShadedBody.multiplicity (O.fiber x₀) O.innerBody := by
    rw [hfibeq]
    exact multiplicity_eq_of_shade_eqOn _ _ _ (fun i _ => hshadeO i)
  -- ================================================================
  -- STEP 5: the inner clauses
  -- ================================================================
  -- inner fullness
  have hfullfib : (δ : ℝ≥0) ^ (e + 2 * η)
      ≤ ShadedBody.fullness (
          ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
            hsubO).withShades (fun i => (O.innerBody i).shade)
            (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.fiber x₀)
          ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
            hsubO).withShades (fun i => (O.innerBody i).shade)
            (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.innerBody := by
    calc (δ : ℝ≥0) ^ (e + 2 * η) ≤ ShadedBody.fullness O.innerSet O.innerBody := hfullOlow
      _ = ShadedBody.fullness
          ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
            hsubO).withShades (fun i => (O.innerBody i).shade)
            (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.innerSet
          ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
            hsubO).withShades (fun i => (O.innerBody i).shade)
            (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.innerBody :=
          hfull''eq.symm
      _ ≤ _ := hfibsel
  have hfullInner : (δ : ℝ≥0) ^ ηᵢ ≤ ShadedBody.fullness qj (fun i => (Pj i).toShadedBody) := by
    refine rpow_le_of_le_mul_of_loss_le hδ0 (C := Cnorm * ((d : ℝ≥0) + 1))
      (small := e + 2 * η) (large := ηᵢ) ?_ hfullfib hfullraw
    refine (hfun₅ δ hδ0 hδd₅).trans (hpow ?_)
    linarith
  -- inner maximal density
  have hmaxdInner : maxDensity qj (fun i => (Pj i).toConvexSpaceBody)
      ≤ (Cnorm : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) := by
    refine hmaxdP.trans ?_
    gcongr
    calc maxDensity q'' (fun i => (T'' i).toConvexSpaceBody)
        = maxDensity q'' (fun i => (T i).toConvexSpaceBody) := rfl
      _ ≤ maxDensity q (fun i => (T i).toConvexSpaceBody) :=
          maxDensity_mono (fun i => (T i).toConvexSpaceBody) hq''q
  -- inner slab clause
  have h8η : 8 * η ≤ ηᵢ := by linarith
  obtain ⟨hslabConst, -⟩ :=
    partB_finalize_selected_inner_bounds (Cprop := 1) hη hηᵢ h8η hδ0 hδ1 le_rfl hCfib hCF
      ((le_max_right _ _).trans (hfun₇ δ hδ0 hδd₇)) (by
        rw [one_mul]
        exact (hfun₅ δ hδ0 hδd₅).trans (hpow (by linarith)))
  have hslab : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a' / b' ≤ φ →
      ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
      ((Plank.inWideSlabFamily qj (fun i => (Pj i).toPrism3D) S).card : ℝ≥0)
        ≤ δ ^ (-ηᵢ) * φ ^ (1 : ℝ) * (qj.card : ℝ≥0) := by
    intro φ hφR hφ S
    calc ((Plank.inWideSlabFamily qj (fun i => (Pj i).toPrism3D) S).card : ℝ≥0)
        ≤ ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol))
            * φ ^ (1 : ℝ) * (qj.card : ℝ≥0) := hslabraw φ hφR hφ S
      _ ≤ δ ^ (-ηᵢ) * φ ^ (1 : ℝ) * (qj.card : ℝ≥0) := by gcongr
  -- the cardinality clause
  have hcardTotal :
      (ts.card : ENNReal) * (qj.card : ENNReal) ≤ (2 : ENNReal) * (q.card : ENNReal) := by
    have hx₀cells' : x₀ ∈ cells' := hsubO hx₀O
    have h1 : (ts.card : ENNReal) ≤ (cells'.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card (htssub.trans hsubO)
    have hfibsub :
        ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
          hsubO).withShades (fun i => (O.innerBody i).shade)
          (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.fiber x₀
        ⊆ (BlockCount.restrictCells D cells' hsub).fineOutput.fiber x₀ := by
      intro i hi
      have hi' : i ∈
          ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
            hsubO).withShades (fun i => (O.innerBody i).shade)
            (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineFibre x₀ := hi
      rw [Section6PartBData.mem_fineFibre_iff] at hi'
      change i ∈ (BlockCount.restrictCells D cells' hsub).fineFibre x₀
      rw [Section6PartBData.mem_fineFibre_iff]
      exact ⟨hq''q' hi'.1, hi'.2⟩
    have h2 : (qj.card : ENNReal)
        ≤ (((BlockCount.restrictCells D cells' hsub).fineOutput.fiber x₀).card : ENNReal) := by
      exact_mod_cast hcardfib.trans (Finset.card_le_card hfibsub)
    have h3 : ((q'.card : ENNReal)) ≤ (q.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card hq'sub
    calc (ts.card : ENNReal) * (qj.card : ENNReal)
        ≤ (cells'.card : ENNReal)
            * (((BlockCount.restrictCells D cells' hsub).fineOutput.fiber x₀).card : ENNReal) :=
          mul_le_mul' h1 h2
      _ ≤ (2 : ℝ≥0) * ((BlockCount.restrictFine D cells').card : ENNReal) := hcount x₀ hx₀cells'
      _ ≤ (2 : ENNReal) * (q.card : ENNReal) := by
          rw [show ((2 : ℝ≥0) : ENNReal) = 2 by norm_num]
          exact mul_le_mul' le_rfl h3
  -- the split
  have hsplitO := hO.split x₀ hx₀O
  have hLossNN : L * Cs * Dext * ((d : ℝ≥0) + 1) ≤ δ ^ (-ηs) := by
    calc L * Cs * Dext * ((d : ℝ≥0) + 1)
        ≤ δ ^ (-η) * δ ^ (-e) * δ ^ (-(8 * η)) * δ ^ (-η) :=
          mul_le_mul' (mul_le_mul' (mul_le_mul' hLNN hCs) hDext8) (hfun₆ δ hδ0 hδd₆)
      _ = δ ^ (-(e + 10 * η)) := by
          rw [hrpow_add, hrpow_add, hrpow_add]; congr 1; ring
      _ ≤ δ ^ (-ηs) := hpow (by linarith)
  have hLossE : ((L * Cs * Dext * ((d : ℝ≥0) + 1) : ℝ≥0) : ENNReal) ≤ (δ : ENNReal) ^ (-ηs) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hδne]
    exact_mod_cast hLossNN
  have hmultTotal : ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
      (δ : ENNReal) ^ (-ηs)
        * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
        * ShadedBody.multiplicity qj (fun i => (Pj i).toShadedBody) := by
    calc ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
        ≤ (L : ENNReal) * ShadedBody.multiplicity q' (fun i => (T i).toShadedBody) := by
          rw [hL, ENNReal.coe_natCast]; exact hmultL
      _ ≤ (L : ENNReal) * ((Cs : ENNReal) * ShadedBody.multiplicity O.outerSet O.outerBody
            * ShadedBody.multiplicity (O.fiber x₀) O.innerBody) := mul_le_mul' le_rfl hsplitO
      _ = (L : ENNReal) * ((Cs : ENNReal)
            * ShadedBody.multiplicity O.outerSet (fun j => (W j).toShadedBody)
            * ShadedBody.multiplicity (
                ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
                  hsubO).withShades (fun i => (O.innerBody i).shade)
                  (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.fiber x₀)
                ((BlockCount.restrictCells (BlockCount.restrictCells D cells' hsub) O.outerSet
                  hsubO).withShades (fun i => (O.innerBody i).shade)
                  (fun i => (O.innerBody i).measurableSet_shade) hYsub).fineOutput.innerBody) := by
          rw [hmultOW, hmultfib]
      _ ≤ (L : ENNReal) * ((Cs : ENNReal)
            * ((Dext : ENNReal) * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody))
            * (((d : ENNReal) + 1)
              * ShadedBody.multiplicity qj (fun i => (Pj i).toShadedBody))) := by
          gcongr
      _ = ((L * Cs * Dext * ((d : ℝ≥0) + 1) : ℝ≥0) : ENNReal)
            * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
            * ShadedBody.multiplicity qj (fun i => (Pj i).toShadedBody) := by
          push_cast; ring
      _ ≤ (δ : ENNReal) ^ (-ηs)
            * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
            * ShadedBody.multiplicity qj (fun i => (Pj i).toShadedBody) := by
          gcongr
  -- ================================================================
  -- assemble
  -- ================================================================
  refine ⟨ts, W, htsne, htscells, hED, hWwin, hWfull, hWKT,
    a', b', ha'b', hb'1, ιj, qj, Pj, ha'pos, hδa', hb'b₀, hratioENN, hwindowP, hpairP,
    hfullInner, hmaxdInner, hslab, hcardTotal, hmultTotal⟩


/-- **GWZ Lemma 3.7 in threshold form, at any index universe.**

`Kakeya.KatzTaoEstimate.multiplicity_bound` quantifies its tube families over the universe of the
Katz--Tao hypothesis.  The residue `Kakeya.Prop66BPartBChainConstructed` quantifies its fine family
over an unrelated universe, so the bound is transported: `Kakeya.KatzTaoEstimate.toTypeZero` puts
the hypothesis at `Type 0`, and the family is re-indexed along `Fin s.card`
(`Kakeya.ShadedBody.multiplicity_map`, `Kakeya.ShadedBody.fullness_map`, `Kakeya.maxDensity_map`).
The window hypothesis is on the family only (`∀ i ∈ s`), which the re-indexing also supplies. -/
theorem KatzTaoEstimate.exists_threshold_multiplicity_bound_univ {β : ℝ} (hβ0 : 0 ≤ β)
    (hKKT : KatzTaoEstimate.{w} (EuclideanSpace ℝ (Fin 3)) β) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧
      ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ →
        ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
          (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody) →
          ShadedBody.multiplicity s (fun i => (T i).toShadedBody) ≤
            (δ : ENNReal) ^ (-ε)
              * (maxDensity s (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
              * (s.card : ENNReal) ^ β := by
  classical
  obtain ⟨η, hη, hev⟩ :=
    KatzTaoEstimate.multiplicity_bound (E := EuclideanSpace ℝ (Fin 3)) hβ0 hKKT.toTypeZero ε hε
  obtain ⟨u, hu0, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨η, hη, u, hu0, ?_⟩
  intro δ hδ0 hδu ι s T hball hfull
  -- reindex along `Fin s.card`
  let e : Fin s.card ↪ ι :=
    ⟨fun k => (s.equivFin.symm k).1, by
      intro k₁ k₂ h
      have h' : s.equivFin.symm k₁ = s.equivFin.symm k₂ := Subtype.ext h
      exact s.equivFin.symm.injective h'⟩
  have hmap : (Finset.univ : Finset (Fin s.card)).map e = s := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      exact (s.equivFin.symm k).2
    · intro hi
      refine ⟨s.equivFin ⟨i, hi⟩, ?_⟩
      change (s.equivFin.symm (s.equivFin ⟨i, hi⟩)).1 = i
      rw [Equiv.symm_apply_apply]
  set T' : Fin s.card → ShadedTube δ (EuclideanSpace ℝ (Fin 3)) := fun k => T (e k) with hT'
  have hball' : ∀ k, (T' k).carrier ⊆ Metric.closedBall 0 1 := by
    intro k
    exact hball _ (s.equivFin.symm k).2
  have hfull' : (ShadedBody.fullness (Finset.univ : Finset (Fin s.card))
      (fun k => (T' k).toShadedBody) : ℝ) ≥ (δ : ℝ) ^ η := by
    have h1 : ShadedBody.fullness (Finset.univ : Finset (Fin s.card))
        (fun k => (T' k).toShadedBody) = ShadedBody.fullness s (fun i => (T i).toShadedBody) := by
      have h := ShadedBody.fullness_map (Finset.univ : Finset (Fin s.card)) e
        (fun i => (T i).toShadedBody)
      rw [hmap] at h
      exact h.symm
    rw [h1]
    have h2 := NNReal.coe_le_coe.mpr hfull
    rw [NNReal.coe_rpow] at h2
    exact h2
  have hres := hsub ⟨hδ0, hδu⟩ (Finset.univ : Finset (Fin s.card)) T' hball' hfull'
  have hmult : ShadedBody.multiplicity (Finset.univ : Finset (Fin s.card))
      (fun k => (T' k).toShadedBody) = ShadedBody.multiplicity s (fun i => (T i).toShadedBody) := by
    have h := ShadedBody.multiplicity_map (Finset.univ : Finset (Fin s.card)) e
      (fun i => (T i).toShadedBody)
    rw [hmap] at h
    exact h.symm
  have hmaxd : maxDensity (Finset.univ : Finset (Fin s.card))
      (fun k => (T' k).toConvexSpaceBody) = maxDensity s (fun i => (T i).toConvexSpaceBody) := by
    have h := maxDensity_map (Finset.univ : Finset (Fin s.card)) e
      (fun i => (T i).toConvexSpaceBody)
    rw [hmap] at h
    exact h.symm
  have hcard : ((Finset.univ : Finset (Fin s.card)).card : ENNReal) = (s.card : ENNReal) := by
    have h := Finset.card_map (s := (Finset.univ : Finset (Fin s.card))) e
    rw [hmap] at h
    rw [← h]
  rw [hmult, hmaxd, hcard] at hres
  exact hres

end Kakeya

end
