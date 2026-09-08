/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.TopLevelWrapper

/-!
# Guardrails for `Kakeya.WangZahl.FrostmanOrDone`

`Kakeya.DimensionThree.MainLemma2.WangZahl.SourcePropositions` carries the obligation
`Kakeya.WangZahl.frostmanOrDone_zero : FrostmanOrDone.{u} 0` as a proposition.
An earlier form of `FrostmanOrDone` was **refuted**, and this file is the compiler-checked
record of that refutation together with the tripwire that makes a silent revert break the
build.

## The defect

The pre-repair `FrostmanOrDone` read

```
∀ epsilon > 0, ∀ eta > 0, ∀ᶠ delta in 𝓝[>] 0, ...
```

with `eta` quantified universally and *independently of* `epsilon`.  Its only consumer,
`Kakeya.WangZahl.katzTaoEstimate_of_assertionD_of_frostmanOrDone`, instantiates it at an
`eta` that is at most `epsilon / 16`, and the Wang--Zahl source
(`blueprint/src/WZ2/250224e_K3.tex`, e.g. the statement at line 198 and Theorem `WZThm52`
at line 2267) always reads "for all `eps > 0` there exists `eta > 0` such that ...".
The universal `eta` was therefore an over-generalisation, and a false one.

## Contents

* `Kakeya.WangZahl.frostmanOrDoneBody` — the body of the dichotomy at a fixed
  `(gamma, epsilon, eta)`, factored out so that the two quantifier prefixes can be compared
  mechanically.
* `Kakeya.WangZahl.frostmanOrDone_eq` — the tripwire.  It is `Iff.rfl`, so it stops
  typechecking the moment either the body or the quantifier prefix of `FrostmanOrDone`
  changes, forcing whoever changes it to read this file.
* `Kakeya.WangZahl.FrostmanOrDoneUnbounded` — the **refuted** pre-repair form: the same body
  with `eta` universally quantified.
* `Kakeya.WangZahl.frostmanOrDone_of_unbounded` — the refuted form implies the repaired one,
  i.e. the repair is a genuine weakening and nothing that used to be available was lost.
* `Kakeya.WangZahl.frostmanOrDone_zero_refuted : ¬ FrostmanOrDoneUnbounded.{0} 0` — the
  refutation.  The witness is `N` copies of one fully shaded `delta`-tube with
  `delta^{-1/2} < N ≤ delta^{-1}`, taken at `epsilon = 1/2`, `eta = 1`.  `FrostmanOrDone`
  has no essential-distinctness hypothesis, so repetition is admissible; the family meets
  every hypothesis and neither conclusion.  Under the repaired prefix the same family is
  unavailable, because it needs `delta^{-epsilon} < N ≤ delta^{-eta}`, which is empty once
  `eta ≤ epsilon`.

## The residual `eta`-versus-`epsilon` budget (not formalised here)

`eta ≤ epsilon` alone is *not* enough either, and this is why the repaired prefix is
`∃ eta0 > 0, ∀ eta ≤ eta0` rather than `eta ≤ epsilon`.  Take a bush of `N = delta^{-1}`
tubes through the origin with `delta`-separated directions inside a cap of angular width
`theta = delta^{1/2}`, and shade each tube by its intersection with `B(0, r)`, `r = delta^eta`.
Then the fullness is `r = delta^eta`; `maxDensity ≈ 1 ≤ delta^{-eta}`; the union of the
shadings is contained in a `2r × 2(theta r + delta) × 2(theta r + delta)` box, so
`∑ |Y_i| / |⋃ Y_i| ≈ r^{-2} = delta^{-2 eta}`, which exceeds `delta^{-epsilon}` whenever
`2 eta > epsilon`; and the family is not `delta^{-eta}`-Frostman in the unit ball, since the
cap hull has volume `≈ theta^2 = delta` and concentrates the family by `theta^{-2} = delta^{-1}`.
So any correct hypothesis must force `eta` below a fixed fraction of `epsilon`, and no
*fixed* fraction is obviously safe: the honest statement is the one the source uses, namely
that `eta` may be taken as small as the prover needs.
-/

@[expose] public section

open MeasureTheory Metric Filter

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### The two quantifier prefixes -/

/-- The body of the `FrostmanOrDone` dichotomy at a fixed `(gamma, epsilon, eta)`. -/
def frostmanOrDoneBody (gamma epsilon eta : Real) : Prop :=
  ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
    ∀ {iota : Type u} (s : Finset iota) (T : iota -> ShadedTube delta Space3),
      s.Nonempty ->
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) ->
      ConvexSpaceBody.IsKatzTao s (fun i => (T i).toConvexSpaceBody)
        ((delta : ENNReal) ^ (-eta)) ->
      ShadedBody.fullness s (fun i => (T i).toShadedBody) >= delta ^ eta ->
      (∑ i ∈ s, volume (T i).shade <=
          (delta : ENNReal) ^ (-epsilon) * (s.card : ENNReal) ^ gamma *
            volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)) ∨
        ConvexSpaceBody.IsFrostmanIn s
          (fun i => (T i).toConvexSpaceBody)
          (ConvexSpaceBody.closedUnitBall (E := Space3))
          ((delta : ENNReal) ^ (-eta))

/-- **Tripwire.**  This is `Iff.rfl`: it stops typechecking the moment the statement of
`Kakeya.WangZahl.FrostmanOrDone` changes, in body or in quantifier prefix.  If it breaks,
read the module docstring before "fixing" it — the previous prefix was refuted below. -/
theorem frostmanOrDone_eq (gamma : Real) :
    FrostmanOrDone.{u} gamma ↔
      ∀ epsilon > (0 : Real), ∃ eta0 > (0 : Real), ∀ eta > (0 : Real), eta ≤ eta0 →
        frostmanOrDoneBody.{u} gamma epsilon eta :=
  Iff.rfl

/-- The **refuted** pre-repair form of `FrostmanOrDone`: `eta` universally quantified and
independent of `epsilon`.  See `frostmanOrDone_zero_refuted`. -/
def FrostmanOrDoneUnbounded (gamma : Real) : Prop :=
  ∀ epsilon > (0 : Real), ∀ eta > (0 : Real), frostmanOrDoneBody.{u} gamma epsilon eta

/-- The refuted form implies the repaired one: the repair is a genuine weakening, so no
consumer lost anything. -/
theorem frostmanOrDone_of_unbounded {gamma : Real}
    (h : FrostmanOrDoneUnbounded.{u} gamma) : FrostmanOrDone.{u} gamma :=
  fun epsilon hepsilon => ⟨1, one_pos, fun eta heta _ => h epsilon hepsilon eta heta⟩

/-! ### The refuting family -/

namespace FrostmanOrDoneGuard

/-- The unit segment centred at the origin, along the first coordinate axis. -/
def refPt : Space3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

lemma dist_ref : dist (-(1/2 : ℝ) • refPt) ((1/2 : ℝ) • refPt) = 1 := by
  rw [dist_eq_norm]
  have : (-(1/2 : ℝ) • refPt) - ((1/2 : ℝ) • refPt) = -refPt := by
    module
  rw [this, norm_neg, refPt, PiLp.norm_single, norm_one]

/-- The reference `δ`-tube: the `δ`-neighbourhood of that segment. -/
def refTube (δ : NNReal) : Tube δ Space3 := Tube.mk' δ dist_ref

lemma refTube_subset_ball {δ : NNReal} (hδ : δ ≤ 1 / 2) :
    (refTube δ).carrier ⊆ closedBall 0 1 := by
  rw [(refTube δ).carrier_eq_cthickening]
  have hseg : segment ℝ (-(1/2 : ℝ) • refPt) ((1/2 : ℝ) • refPt) ⊆
      closedBall (0 : Space3) (1/2) := by
    refine (convex_closedBall _ _).segment_subset ?_ ?_ <;>
      simp [norm_smul, refPt, PiLp.norm_single]
  refine (cthickening_subset_of_subset _ hseg).trans ?_
  rw [cthickening_closedBall (by positivity) (by norm_num)]
  refine closedBall_subset_closedBall ?_
  have : (δ : ℝ) ≤ 1/2 := by exact_mod_cast hδ
  linarith

/-- The reference `δ`-tube with the full shading. -/
def refShaded (δ : NNReal) : ShadedTube δ Space3 where
  toTube := refTube δ
  shade := (refTube δ).carrier
  measurableSet_shade := (refTube δ).isCompact'.measurableSet
  shade_subset := subset_rfl

@[simp] lemma refShaded_carrier (δ : NNReal) :
    (refShaded δ).carrier = (refTube δ).carrier := rfl

@[simp] lemma refShaded_shade (δ : NNReal) :
    (refShaded δ).shade = (refTube δ).carrier := rfl

lemma refVol_pos {δ : NNReal} (hδ : 0 < δ) : 0 < volume (refTube δ).carrier := by
  refine lt_of_lt_of_le ?_ (Tube.le_volume (refTube δ))
  have h3 : Module.finrank ℝ Space3 = 3 := by simp
  rw [h3]
  exact ENNReal.mul_pos (by exact_mod_cast (Tube.le_volume.c_pos 3).ne')
    (by positivity)

lemma refVol_le {δ : NNReal} (hδ1 : δ ≤ 1) :
    volume (refTube δ).carrier ≤ 16 * (δ : ENNReal) ^ 2 := by
  refine (Tube.volume_le hδ1 (refTube δ)).trans (le_of_eq ?_)
  have h3 : Module.finrank ℝ Space3 = 3 := by simp
  rw [h3]
  norm_num [Tube.volume_le.C]

lemma refVol_ne_top {δ : NNReal} (hδ1 : δ ≤ 1) : volume (refTube δ).carrier ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness) (refVol_le hδ1)

/-! ### The `N`-fold repetition family -/

variable {δ : NNReal} {N : ℕ}

/-- `N` copies of the reference `δ`-tube, fully shaded. -/
def repFamily (δ : NNReal) (N : ℕ) : Fin N → ShadedTube δ Space3 := fun _ => refShaded δ

lemma sum_shade (_hN : 0 < N) :
    ∑ i ∈ (Finset.univ : Finset (Fin N)), volume (repFamily δ N i).shade =
      (N : ENNReal) * volume (refTube δ).carrier := by
  simp [repFamily, Finset.sum_const, nsmul_eq_mul]

lemma sum_carrier (_hN : 0 < N) :
    ∑ i ∈ (Finset.univ : Finset (Fin N)), volume (repFamily δ N i).carrier =
      (N : ENNReal) * volume (refTube δ).carrier := by
  simp [repFamily, Finset.sum_const, nsmul_eq_mul]

lemma iUnionShade_rep (hN : 0 < N) :
    ShadedBody.iUnionShade (Finset.univ : Finset (Fin N))
      (fun i => (repFamily δ N i).toShadedBody) = (refTube δ).carrier := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  simp only [ShadedBody.iUnionShade, repFamily, Finset.mem_univ, Set.iUnion_true]
  exact Set.iUnion_const _

lemma fullness_rep (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N) :
    ShadedBody.fullness (Finset.univ : Finset (Fin N))
      (fun i => (repFamily δ N i).toShadedBody) = 1 := by
  have hne : (N : ENNReal) * volume (refTube δ).carrier ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast hN.ne') (refVol_pos hδ0).ne'
  have htop : (N : ENNReal) * volume (refTube δ).carrier ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (refVol_ne_top hδ1)
  have : ShadedBody.fullness' (Finset.univ : Finset (Fin N))
      (fun i => (repFamily δ N i).toShadedBody) = 1 := by
    rw [ShadedBody.fullness']
    rw [show (∑ i ∈ (Finset.univ : Finset (Fin N)),
        volume ((fun i => (repFamily δ N i).toShadedBody) i).shade) =
        (N : ENNReal) * volume (refTube δ).carrier from sum_shade hN,
      show (∑ i ∈ (Finset.univ : Finset (Fin N)),
        volume ((fun i => (repFamily δ N i).toShadedBody) i).carrier) =
        (N : ENNReal) * volume (refTube δ).carrier from sum_carrier hN]
    exact ENNReal.div_self hne htop
  rw [ShadedBody.fullness, this]
  rfl

/-! ### Density of the repetition family -/

lemma densityIn_rep (hN : 0 < N) (K : ConvexSpaceBody Space3)
    (hK : (refTube δ).toConvexSpaceBody ≤ K) :
    densityIn (Finset.univ : Finset (Fin N))
        (fun i => (repFamily δ N i).toConvexSpaceBody) K =
      (N : ENNReal) * volume (refTube δ).carrier / volume K.carrier := by
  rw [densityIn_of_all_le (s := (Finset.univ : Finset (Fin N)))
    (W := fun i => (repFamily δ N i).toConvexSpaceBody) (K := K) (fun i _ => hK)]
  congr 1
  simpa using sum_carrier (δ := δ) (N := N) hN

/-- The repetition family is not `delta^{-eta}`-Frostman in the unit ball unless
`|B(0,1)| <= delta^{-eta} |T|`. -/
lemma frostman_forces (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N) {c : ENNReal}
    (hF : ConvexSpaceBody.IsFrostmanIn (Finset.univ : Finset (Fin N))
      (fun i => (repFamily δ N i).toConvexSpaceBody)
      (ConvexSpaceBody.closedUnitBall (E := Space3)) c)
    (hball : (refTube δ).carrier ⊆ closedBall 0 1) :
    volume (closedBall (0 : Space3) 1) ≤ c * volume (refTube δ).carrier := by
  set V := volume (refTube δ).carrier with hV
  have hV0 : V ≠ 0 := (refVol_pos hδ0).ne'
  have hVtop : V ≠ ⊤ := refVol_ne_top hδ1
  set B := volume (closedBall (0 : Space3) 1) with hB
  have hB0 : B ≠ 0 := (measure_closedBall_pos volume (0 : Space3) one_pos).ne'
  have hBtop : B ≠ ⊤ := measure_closedBall_lt_top.ne
  have hle : (refTube δ).toConvexSpaceBody ≤
      (ConvexSpaceBody.closedUnitBall (E := Space3)) := hball
  have h := hF (refTube δ).toConvexSpaceBody hle
  rw [densityIn_rep hN _ le_rfl, densityIn_rep hN _ hle] at h
  have hBcar : volume (ConvexSpaceBody.closedUnitBall (E := Space3)).carrier = B := rfl
  rw [hBcar] at h
  have hNV : (N : ENNReal) * V / V = (N : ENNReal) := by
    rw [mul_div_assoc, ENNReal.div_self hV0 hVtop, mul_one]
  rw [hNV] at h
  have hN0 : (N : ENNReal) ≠ 0 := by exact_mod_cast hN.ne'
  have hNtop : (N : ENNReal) ≠ ⊤ := by simp
  have hstep : (N : ENNReal) * 1 ≤ (N : ENNReal) * (c * V / B) := by
    rw [mul_one]
    refine h.trans (le_of_eq ?_)
    rw [mul_div_assoc, mul_div_assoc]
    ring
  have h1 : (1 : ENNReal) ≤ c * V / B :=
    (ENNReal.mul_le_mul_iff_right hN0 hNtop).mp hstep
  have := (ENNReal.le_div_iff_mul_le (Or.inl hB0) (Or.inl hBtop)).mp h1
  simpa using this

/-! ### Numeric bridges -/

lemma nat_le_rpow_iff {δ : NNReal} (hδ : δ ≠ 0) (N : ℕ) (y : ℝ) :
    (N : ENNReal) ≤ (δ : ENNReal) ^ y ↔ (N : ℝ) ≤ (δ : ℝ) ^ y := by
  rw [← ENNReal.coe_rpow_of_ne_zero hδ]
  rw [show ((N : ENNReal)) = ((N : NNReal) : ENNReal) by simp, ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe, NNReal.coe_rpow]
  simp

lemma two_le_rpow_neg_half {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 4) :
    2 ≤ r ^ (-(1/2) : ℝ) := by
  have hq : ((1:ℝ)/4) ^ ((1:ℝ)/2) = 1/2 := by
    have h4 : ((1:ℝ)/4) = ((1:ℝ)/2) ^ (2:ℕ) := by norm_num
    rw [h4, ← Real.rpow_natCast ((1:ℝ)/2) 2, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hhalf : r ^ ((1:ℝ)/2) ≤ 1/2 :=
    calc r ^ ((1:ℝ)/2) ≤ ((1:ℝ)/4) ^ ((1:ℝ)/2) :=
          Real.rpow_le_rpow hr0.le hr (by norm_num : (0:ℝ) ≤ 1/2)
      _ = 1/2 := hq
  have hpos : 0 < r ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hr0 _
  have hinvpos : 0 ≤ (r ^ ((1:ℝ)/2))⁻¹ := by positivity
  have hstep : 2 * (r ^ ((1:ℝ)/2)) ≤ 1 := by linarith
  rw [show (-(1/2) : ℝ) = -((1:ℝ)/2) by norm_num, Real.rpow_neg hr0.le]
  calc (2:ℝ) = (2 * (r ^ ((1:ℝ)/2))) * (r ^ ((1:ℝ)/2))⁻¹ := by
        field_simp
    _ ≤ 1 * (r ^ ((1:ℝ)/2))⁻¹ := by gcongr
    _ = _ := one_mul _

lemma exists_middle_nat {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 4) :
    ∃ N : ℕ, 0 < N ∧ r ^ (-(1/2) : ℝ) < (N : ℝ) ∧ (N : ℝ) ≤ r ^ (-(1:ℝ)) := by
  set t : ℝ := r ^ (-(1/2) : ℝ) with ht
  have ht2 : 2 ≤ t := two_le_rpow_neg_half hr0 hr
  have htt : t * t = r ^ (-(1:ℝ)) := by
    rw [ht, ← Real.rpow_add hr0]
    norm_num
  refine ⟨⌈t⌉₊ + 1, Nat.succ_pos _, ?_, ?_⟩
  · have := Nat.le_ceil t
    push_cast
    linarith
  · have hlt : (⌈t⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one (by linarith)
    push_cast
    nlinarith

end FrostmanOrDoneGuard

/-! ### The refutation -/

open FrostmanOrDoneGuard in
theorem frostmanOrDone_zero_refuted : ¬ FrostmanOrDoneUnbounded.{0} 0 := by
  intro H
  set B : ENNReal := volume (closedBall (0 : Space3) 1) with hBdef
  have hB0 : B ≠ 0 := (measure_closedBall_pos volume (0 : Space3) one_pos).ne'
  have hBtop : B ≠ ⊤ := measure_closedBall_lt_top.ne
  set b : NNReal := B.toNNReal with hbdef
  have hbB : (b : ENNReal) = B := ENNReal.coe_toNNReal hBtop
  have hb0 : 0 < b := by
    rw [← ENNReal.coe_pos, hbB]
    exact pos_iff_ne_zero.mpr hB0
  set m : NNReal := min (1/4) (b/16) with hmdef
  have hm0 : 0 < m := lt_min (by norm_num) (by positivity)
  obtain ⟨δ, hfam, hδ0, hδm⟩ :=
    ((H (1/2) (by norm_num) 1 (by norm_num)).and (Ioo_mem_nhdsGT hm0)).exists
  have hδ4 : δ ≤ 1/4 := (hδm.trans_le (min_le_left _ _)).le
  have hδb : δ < b/16 := hδm.trans_le (min_le_right _ _)
  have hq1 : (1/4 : NNReal) ≤ 1 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have hq2 : (1/4 : NNReal) ≤ 1/2 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have hδ1 : δ ≤ 1 := hδ4.trans hq1
  have hδ0' : δ ≠ 0 := hδ0.ne'
  have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0'
  have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- the count
  obtain ⟨N, hN, hNlow, hNhigh⟩ :=
    exists_middle_nat (r := (δ : ℝ)) (by exact_mod_cast hδ0) (by exact_mod_cast hδ4)
  set V : ENNReal := volume (refTube δ).carrier with hVdef
  have hV0 : V ≠ 0 := (refVol_pos hδ0).ne'
  have hVtop : V ≠ ⊤ := refVol_ne_top hδ1
  have hball : (refTube δ).carrier ⊆ closedBall 0 1 :=
    refTube_subset_ball (hδ4.trans hq2)
  -- the hypotheses of the dichotomy
  have hs : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hballs : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      (repFamily δ N i).carrier ⊆ closedBall 0 1 := fun i _ => hball
  have hcard : (Finset.univ : Finset (Fin N)).card = N := Finset.card_univ.trans (by simp)
  have hKT : ConvexSpaceBody.IsKatzTao (Finset.univ : Finset (Fin N))
      (fun i => (repFamily δ N i).toConvexSpaceBody) ((δ : ENNReal) ^ (-(1:ℝ))) := by
    refine (maxDensity_le_card _ _).trans ?_
    rw [hcard]
    exact (nat_le_rpow_iff hδ0' N (-(1:ℝ))).mpr hNhigh
  have hfull : ShadedBody.fullness (Finset.univ : Finset (Fin N))
      (fun i => (repFamily δ N i).toShadedBody) ≥ δ ^ (1:ℝ) := by
    rw [fullness_rep hδ0 hδ1 hN, NNReal.rpow_one]
    exact hδ1
  rcases hfam (Finset.univ : Finset (Fin N)) (repFamily δ N) hs hballs hKT hfull with hdone | hF
  · -- the "done" branch asserts `N ≤ δ^{-1/2}`
    rw [sum_shade hN, iUnionShade_rep hN, ENNReal.rpow_zero, mul_one] at hdone
    have hcancel : (N : ENNReal) ≤ (δ : ENNReal) ^ (-(1/2 : ℝ)) := by
      refine (ENNReal.mul_le_mul_iff_left hV0 hVtop).mp ?_
      simpa [hcard] using hdone
    have := (nat_le_rpow_iff hδ0' N (-(1/2 : ℝ))).mp hcancel
    linarith
  · -- the Frostman branch asserts `|B| ≤ δ^{-1} |T|`
    have hforce := frostman_forces hδ0 hδ1 hN hF hball
    have hVle : V ≤ 16 * (δ : ENNReal) ^ (2:ℕ) := refVol_le hδ1
    have hpow : (δ : ENNReal) ^ (-(1:ℝ)) * (δ : ENNReal) ^ (2:ℕ) = (δ : ENNReal) := by
      rw [← ENNReal.rpow_natCast (δ : ENNReal) 2, ← ENNReal.rpow_add _ _ hδ0E hδtopE]
      norm_num
    have hsmall : (δ : ENNReal) ^ (-(1:ℝ)) * V < B := by
      calc (δ : ENNReal) ^ (-(1:ℝ)) * V
          ≤ (δ : ENNReal) ^ (-(1:ℝ)) * (16 * (δ : ENNReal) ^ (2:ℕ)) := by gcongr
        _ = 16 * ((δ : ENNReal) ^ (-(1:ℝ)) * (δ : ENNReal) ^ (2:ℕ)) := by ring
        _ = 16 * (δ : ENNReal) := by rw [hpow]
        _ = (((16 * δ : NNReal)) : ENNReal) := by push_cast; ring
        _ < (b : ENNReal) := by
            refine ENNReal.coe_lt_coe.mpr ?_
            rw [← NNReal.coe_lt_coe] at hδb ⊢
            push_cast at hδb ⊢
            linarith
        _ = B := hbB
    exact absurd hforce (not_le_of_gt hsmall)

end

end Kakeya.WangZahl

#print axioms Kakeya.WangZahl.frostmanOrDone_eq
#print axioms Kakeya.WangZahl.frostmanOrDone_of_unbounded
#print axioms Kakeya.WangZahl.frostmanOrDone_zero_refuted
