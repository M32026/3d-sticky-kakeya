/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredHandBackUniform
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredCountTransport
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleFactor
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineLineEDMiddle
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleProducer

/-!
# The `hcb`/`hct`/`huni` seam: one `U''` for all three rows at the six middle-factor sites

 The construction returns a family returning `CentredHandBack` and `CountTransport`
on one and the same `U'`.  It had no consumer, and it could not have one: the six middle-factor
sites bind **one** shade family `U'` and ask it for *three* things — `hcb`, `hct` and the folded
`huni` conjunct — and the only supplier of `huni` in the tree
(`Kakeya.ML2Reduction.eventually_outerHuni_ssf`, the estimate) returns a family whose `toTube` is the
**outer family's tube**, while the hand-back's `U'` has the canonical cover's **node** for its
tube.  Two different objects; feeding both to one site would have been the same defect one level
up.

**The required order is**
(`Reduction/SpineCentredHandBackUniform.lean`): *centre, then uniformise
the centred family, then hand back at the uniformiser's output.*  Run that way, the uniformiser
acts on the **centred** family, so its output `U''` has the node for its tube
(`htube : (U'' i).toTube = (U' i).toTube` — the uniformiser shrinks shades and never moves tubes),
and all three rows are about the same object.

Two things were missing, and they are supplied here.

* `exists_centredPushforward_of_outerFamily_data` — the `_data` sibling of the centring, exporting
  the `hmid`/`hfoot`/`hdir` line parameters that `countTransport_of_contractedCover` binds.  The
  existing `exists_centredPushforward_of_outerFamily` calls `exists_centredRepresentatives`, the
  *projection*, and drops them, exactly as the hand-back producer did before 
* `countTransport_of_tubeEq` — `CountTransport` reads `U'` only through `(U' i).toConvexSpaceBody`,
  so it is **invariant** under a shade refinement that keeps the tubes.  This is what carries the
  count clause from the centred family to the uniformiser's output for free, and it is the reason
  the uniformiser may be run after the centring at no cost to the count side.

`exists_centredHandBack_uniform_and_countTransport` is the composite.  Its two retention
hypotheses (`hretfull`, `hretmult`) are Definition 2.2's lower brackets on the subfamilies the
uniformiser can return — the **0-E retention row**, owned elsewhere in this run; they are stated
here by name and are the only hypotheses of the composite that are not site data.

## What it discharges at the six sites

`fullness_ge_of_centredHandBack` derives each site's `hfull` from `hcb`'s own `fullness_ge` field
and the site's `h3qc`, so the composite closes **four** binders per site — `hcb`, `hct`, `huni`,
`hfull` — leaving `U'` and `s'` determined rather than assumed.  The six `example`s at the end of
this file are the adjudication: each feeds the composite's output types into that site's four
slots **by name**, so the elaborator, not a comment, certifies that the rows fit and that they fit
on the same `U''`.
-/

@[expose] public section

open MeasureTheory Metric Kakeya.ML2Reduction
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

universe u




theorem countTransport_of_tubeEq {b δt δ' : NNReal} {R : ℝ}
    {hsit : Tube.IsRescalingSituation b δt δ' R 3} {hR : 0 < R}
    {T₀ : Tube b (EuclideanSpace ℝ (Fin 3))} {m : EuclideanSpace ℝ (Fin 3)} {ϖ ζ : ℝ}
    {α : Type u} {s' : Finset α}
    {Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3))}
    {U' U'' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (htube : ∀ i, (U'' i).toTube = (U' i).toTube)
    (h : CountTransport hsit hR T₀ m ϖ ζ s' Z' U') :
    CountTransport hsit hR T₀ m ϖ ζ s' Z' U'' := by
  intro ρ hρ hyp
  obtain ⟨κ, tρ, Tρ, hED, hused, hcard⟩ := h ρ hρ hyp
  refine ⟨κ, tρ, Tρ, hED, ?_, hcard⟩
  intro j hj
  obtain ⟨i, hi, hle⟩ := hused j hj
  refine ⟨i, hi, ?_⟩
  rwa [show (U'' i).toConvexSpaceBody = (U' i).toConvexSpaceBody from by rw [htube i]]



theorem exists_centredPushforward_of_outerFamily_data
    {b δt δ' : NNReal} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (hδ'0 : 0 < δ') (hδ'20 : (δ' : ℝ) ≤ 1 / 20)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} (fib : Finset α)
    (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ i ∈ fib, (Z' i).carrier ⊆ T₀.carrier) :
    ∃ U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)),
      (∀ i ∈ fib, (U' i).toTube.IsCentred) ∧
      (∀ i ∈ fib, (U' i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
      (∀ i ∈ fib, normalise 0 ''
        (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).carrier ⊆ (U' i).carrier) ∧
      (∀ i ∈ fib, (U' i).shade = normalise 0 ''
        (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).shade) ∧
      (∀ i ∈ fib, ‖(outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.midpoint‖ ≤ 1) ∧
      (∀ i ∈ fib, ‖Tube.lineFoot
          (centringDilate (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.midpoint)
          ((outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.direction)
          - (U' i).toTube.midpoint‖ ≤ (δ' : ℝ) / 4) ∧
      (∀ i ∈ fib, ‖(outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toTube.direction
          - (U' i).toTube.direction‖ ≤ (δ' : ℝ) / 4) := by
  classical
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  set O : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)) :=
    fun i ↦ outerFamily hsit.pos_ambient T₀ hR δ' Z' i with hO
  have hball : ∀ i ∈ fib,
      (O i).toTube.carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    outerFamily_carrier_subset_closedBall hn hsit hR hτσ hsub
  obtain ⟨G, ϖ, hmem, -, hcovD, hcen, hmid, -, -, hfootD, hdirD⟩ :=
    exists_centredRepresentatives_data (E := EuclideanSpace ℝ (Fin 3)) hδ'0 hδ'20 fib
      (fun i ↦ (O i).toTube) hball
  have hcov : ∀ i ∈ fib, normalise 0 '' (O i).carrier ⊆ (ϖ i).carrier := by
    intro i hi
    rw [← centringDilate_image_eq_normalise_zero_image]
    exact hcovD i hi
  refine ⟨fun i ↦ handBackRep (O i) (ϖ i), fun i hi ↦ hcen (ϖ i) (hmem i hi), fun i hi ↦ ?_,
    hcov, fun i hi ↦ handBackRep_shade_eq (O i) (ϖ i) (hcov i hi),
    fun i hi ↦ Tube.norm_midpoint_le_of_subset_ball hδ'0 (O i).toTube (hball i hi),
    hfootD, hdirD⟩
  refine carrier_subset_unitBall_of_isCentred (ϖ i) (hcen (ϖ i) (hmem i hi))
    (R₀ := 2 / 5 + (δ' : ℝ) / 4) (by positivity) (hmid (ϖ i) (hmem i hi)) ?_
  have hr0 : (0 : ℝ) < (δ' : ℝ) / 4 := by positivity
  have hr80 : (δ' : ℝ) / 4 ≤ 1 / 80 := by linarith
  have hreach := canonicalCover_reach_lt hr0 hr80
  linarith


theorem exists_centredHandBack_uniform_and_countTransport (K₀ : ℕ) {α α' : ℝ}
    (hα0 : 0 < α) (hα'0 : 0 < α') :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧
      ∀ {b δt δ' : NNReal} {R : ℝ}
        (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R),
        (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ) →
        0 < δ' → δ' ≤ δ₀ → (δ' : ℝ) ≤ 1 / 20 →
        ∀ (T₀ : Tube b (EuclideanSpace ℝ (Fin 3))) {qc ϖ ζ : ℝ},
        0 < qc → α' ≤ qc →
        (512 : ENNReal) ≤ (δ' : ENNReal) ^ (-qc) →
        0 ≤ ϖ → 0 ≤ 2 + ζ → δ' ^ ϖ ≤ 1 / 2 →
        ∀ {A : Type u} (fib : Finset A) (Z' : A → ShadedTube δt (EuclideanSpace ℝ (Fin 3))),
        fib.Nonempty →
        (∀ i ∈ fib, (Z' i).carrier ⊆ T₀.carrier) →
        ((fib.card : ℝ) ≤ (δ' : ℝ) ^ (-(K₀ : ℝ))) →
        (Kakeya.maxDensity fib
            (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toConvexSpaceBody)
          ≤ (δ' : ENNReal) ^ (-qc)) →
        ((δ' : ENNReal) ^ qc ≤ ShadedBody.fullness fib
          (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)) →
        (∀ t ⊆ fib, (fib.card : ℝ) ≤ (δ' : ℝ) ^ (-α) * (t.card : ℝ) →
          (δ' : ENNReal) ^ qc ≤ (ShadedBody.fullness t
            (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody) : ENNReal)) →
        (∀ t ⊆ fib, (fib.card : ℝ) ≤ (δ' : ℝ) ^ (-α) * (t.card : ℝ) →
          ShadedBody.multiplicity fib
              (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)
            ≤ (δ' : ENNReal) ^ (-(3 * qc - α')) * ShadedBody.multiplicity t
              (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)) →
        ∃ s'' ⊆ fib, ∃ U'' : A → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)),
          ((fib.card : ℝ) ≤ (δ' : ℝ) ^ (-α) * (s''.card : ℝ)) ∧
          CentredHandBack hsit hR T₀ 0 qc fib s'' Z' U'' ∧
          CountTransport hsit hR T₀ 0 ϖ ζ s'' Z' U'' ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ')
            (ShadedTube.ssfUniformConst 3)) := by
  classical
  obtain ⟨δ₀, hδ₀0, -, huni⟩ := ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf
    (E := EuclideanSpace ℝ (Fin 3)) K₀ α α' hα0 hα'0
  refine ⟨δ₀, hδ₀0, ?_⟩
  intro b δt δ' R hsit hR hτσ hδ'0 hδle hδ'20 T₀ qc ϖ ζ hqc0 hα'qc hthr512 hϖ hζ hthr
    A fib Z' hfibne hsub hcard hdens hfull hretfull hretmult
  have hδ'1 : δ' ≤ 1 := by
    have : (δ' : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  obtain ⟨U', hcen, hball, hcov, hsh, hmid, hfoot, hdir⟩ :=
    exists_centredPushforward_of_outerFamily_data hsit hR hτσ hδ'0 hδ'20 T₀ fib Z' hsub
  obtain ⟨s'', hs''sub, U'', htube, hshade, hcardret, hfullret, hstruct⟩ :=
    huni hδ'0 hδle fib U' hball hcard
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 from by simp] at hstruct
  -- `s''` is nonempty, so the shading denominator does not vanish
  have hs''ne : s''.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [hemp] at hcardret
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero] at hcardret
    obtain ⟨i₀, hi₀⟩ := hfibne
    have : (0 : ℝ) < (fib.card : ℝ) := by
      have : 0 < fib.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
      exact_mod_cast this
    linarith
  have hden0 : (∑ i ∈ s'', volume (U' i).carrier) ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hs''ne
    intro hsum
    have h0 : volume (U' i₀).carrier ≠ 0 :=
      (Tube.volume_pos_and_lt_top hδ'0 hδ'1 (U' i₀).toTube).1.ne'
    exact h0 ((Finset.sum_eq_zero_iff.mp hsum) i₀ hi₀)
  have hofReal : ENNReal.ofReal ((δ' : ℝ) ^ (-α')) = (δ' : ENNReal) ^ (-α') := by
    rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ'0), ← ENNReal.ofReal_coe_nnreal, NNReal.coe_rpow]
  have hmass : (∑ i ∈ s'', volume (U' i).shade)
      ≤ (δ' : ENNReal) ^ (-α') * ∑ i ∈ s'', volume (U'' i).shade := by
    have h := sum_shade_le_of_fullness'_le s'' U' U'' htube hden0 hfullret
    rwa [hofReal] at h
  have hcb : CentredHandBack hsit hR T₀ 0 qc fib s'' Z' U'' :=
    centredHandBack_of_uniformised hsit hR hδ'0 hδ'20 T₀ hqc0 hα'0.le hα'qc hthr512
      hs''sub Z' U' U'' hcen hball hcov hsh htube hshade hmass hdens hfull
      (hretfull s'' hs''sub hcardret) (hretmult s'' hs''sub hcardret)
  have hct0 : CountTransport hsit hR T₀ 0 ϖ ζ s'' Z' U' :=
    countTransport_of_contractedCover hsit hR hτσ hδ'0 hϖ hζ hthr T₀ s'' Z' U'
      (fun i hi ↦ hsub i (hs''sub hi)) (fun i hi ↦ hmid i (hs''sub hi))
      (fun i hi ↦ hfoot i (hs''sub hi)) (fun i hi ↦ hdir i (hs''sub hi))
  exact ⟨s'', hs''sub, U'', hcardret, hcb, countTransport_of_tubeEq htube hct0, hstruct⟩


/-- **A site's `hfull` is already inside its `hcb`.**

`CentredHandBack.fullness_ge` is `(δ')^{3qc} ≤ fullness s' U'`, and the six middle-factor sites
bind `h3qc : 3 qc ≤ ηd`; with `δ' ≤ 1` the exponent moves the right way.  So the `hfull` row is
not an extra obligation on the produced family — it is a projection of the hand-back. -/
theorem fullness_ge_of_centredHandBack {b δt δ' : NNReal} {R : ℝ}
    {hsit : Tube.IsRescalingSituation b δt δ' R 3} {hR : 0 < R}
    {T₀ : Tube b (EuclideanSpace ℝ (Fin 3))} {m : EuclideanSpace ℝ (Fin 3)} {qc ηd : ℝ}
    {A : Type u} {fib s' : Finset A}
    {Z' : A → ShadedTube δt (EuclideanSpace ℝ (Fin 3))}
    {U' : A → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd)
    (hcb : CentredHandBack hsit hR T₀ m qc fib s' Z' U') :
    ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd := by
  have hmono : δ' ^ ηd ≤ δ' ^ (3 * qc) :=
    NNReal.rpow_le_rpow_of_exponent_ge hδ'0 hδ'1 h3qc
  have h := hcb.fullness_ge
  rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ'0)] at h
  exact le_trans hmono (by exact_mod_cast h)

end Kakeya.VeryNotSticky

/-! ## The six sites, tied by the elaborator

Each `example` supplies that site's `hcb`, `hct`, `huni` and `hfull` **by name** from the
composite's output types, on one `U''`, and leaves every other binder to be inferred.  A drift in
any of the four types is an elaboration error, not a silent pass; the firing controls for these
ties live in `S9FIBRE_priv/ctl/`. -/

section Ties


variable {b δt δ' : NNReal} {R : ℝ}
  {hsit : Tube.IsRescalingSituation b δt δ' R 3} {hR : 0 < R}
  {T₀ : Tube b (EuclideanSpace ℝ (Fin 3))}
  {A : Type u} {fib s'' : Finset A} {qc ϖ ζ ηd β ζ' m ν cst ε₁ w ηc : ℝ}
  {gain dens : ℝ → ℝ} {k : ℕ} {δ θ τ : NNReal} {Rout : ℝ}
  {hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3} {hRout : 0 < Rout}
  {Tθ : Tube θ (EuclideanSpace ℝ (Fin 3))} {Y : A → ShadedTube τ (EuclideanSpace ℝ (Fin 3))}
  {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))}
  {Z' : A → ShadedTube δt (EuclideanSpace ℝ (Fin 3))}
  {U'' : A → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}

-- TIE 1
example
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ 0 qc fib s'' Z' U'')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ 0 ϖ ζ s'' Z' U'')
    (hstruct : Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ')
      (ShadedTube.ssfUniformConst 3)))
    (habs : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd))
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd) : True := by
  have hfull : ShadedBody.fullness s'' (fun i ↦ (U'' i).toShadedBody) ≥ δ' ^ ηd := by
    have hmono : δ' ^ ηd ≤ δ' ^ (3 * qc) :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ'0 hδ'1 h3qc
    have h := hcb.fullness_ge
    rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ'0)] at h
    exact le_trans hmono (by exact_mod_cast h)
  have _tie := Kakeya.ML2Core.fine_factor_of_lemma91At_of_step8
    (mm := 0) (β := β) (ζ' := ζ') (m := m) (ν := ν) (cst := cst)
    (hcb := hcb) (hct := hct) (huni := ⟨habs, hstruct⟩) (hfull := hfull) (h3qc := h3qc)
  trivial

-- TIE 2
example
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ 0 qc fib s'' Z' U'')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ 0 ϖ ζ s'' Z' U'')
    (hstruct : Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ')
      (ShadedTube.ssfUniformConst 3)))
    (habs : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd))
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd) : True := by
  have hfull : ShadedBody.fullness s'' (fun i ↦ (U'' i).toShadedBody) ≥ δ' ^ ηd := by
    have hmono : δ' ^ ηd ≤ δ' ^ (3 * qc) :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ'0 hδ'1 h3qc
    have h := hcb.fullness_ge
    rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ'0)] at h
    exact le_trans hmono (by exact_mod_cast h)
  have _tie := Kakeya.ML2Core.fine_factor_of_lemma91At_of_edCover
    (mm := 0) (β := β) (ζ' := ζ') (ν := ν) (cst := cst)
    (hcb := hcb) (hct := hct) (huni := ⟨habs, hstruct⟩) (hfull := hfull) (h3qc := h3qc)
  trivial


-- The four nested sites carry `hcoarse`'s two `spineRung` displays in every hypothesis, so
-- the unifier's work is bounded by the site, not by this tie.
set_option maxHeartbeats 1600000 in
-- TIE 3 : Kakeya.ML2Core.middle_factor_of_edNodes_sharp'
example
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ 0 qc fib s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ 0 ϖ ζ s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hstruct : Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ')
      (ShadedTube.ssfUniformConst 3)))
    (habs : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd))
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd) : True := by
  have hfull : ShadedBody.fullness s'' (fun i ↦ (U'' i).toShadedBody) ≥ δ' ^ ηd := by
    have hmono : δ' ^ ηd ≤ δ' ^ (3 * qc) :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ'0 hδ'1 h3qc
    have h := hcb.fullness_ge
    rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ'0)] at h
    exact le_trans hmono (by exact_mod_cast h)
  have _tie := Kakeya.ML2Core.middle_factor_of_edNodes_sharp'
    (mm := 0) (hsitOut := hsitOut) (β := β) (ε₁ := ε₁) (gain := gain) (dens := dens) (k := k)
    (δ := δ) (w := w) (κc := κc) (t' := t') (Zρ := Zρ) (ηc := ηc)
    (cst := cst) (ζ' := ζ')
    (hcb := hcb) (hct := hct) (huni := ⟨habs, hstruct⟩) (hfull := hfull) (h3qc := h3qc)
  trivial

-- The four nested sites carry `hcoarse`'s two `spineRung` displays in every hypothesis, so
-- the unifier's work is bounded by the site, not by this tie.
set_option maxHeartbeats 1600000 in
-- TIE 4 : Kakeya.ML2Core.middle_factor_of_lineEDNodes_sharp
example
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ 0 qc fib s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ 0 ϖ ζ s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hstruct : Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ')
      (ShadedTube.ssfUniformConst 3)))
    (habs : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd))
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd) : True := by
  have hfull : ShadedBody.fullness s'' (fun i ↦ (U'' i).toShadedBody) ≥ δ' ^ ηd := by
    have hmono : δ' ^ ηd ≤ δ' ^ (3 * qc) :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ'0 hδ'1 h3qc
    have h := hcb.fullness_ge
    rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ'0)] at h
    exact le_trans hmono (by exact_mod_cast h)
  have _tie := Kakeya.ML2Core.middle_factor_of_lineEDNodes_sharp
    (mm := 0) (hsitOut := hsitOut) (β := β) (ε₁ := ε₁) (gain := gain) (dens := dens) (k := k)
    (δ := δ) (w := w) (κc := κc) (t' := t') (Zρ := Zρ) (ηc := ηc)
    (cst := cst) (ζ' := ζ')
    (hcb := hcb) (hct := hct) (huni := ⟨habs, hstruct⟩) (hfull := hfull) (h3qc := h3qc)
  trivial

-- The four nested sites carry `hcoarse`'s two `spineRung` displays in every hypothesis, so
-- the unifier's work is bounded by the site, not by this tie.
set_option maxHeartbeats 1600000 in
-- TIE 5 : Kakeya.ML2Core.middle_factor_of_edNodes
example
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ 0 qc fib s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ 0 ϖ ζ s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hstruct : Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ')
      (ShadedTube.ssfUniformConst 3)))
    (habs : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd))
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd) : True := by
  have hfull : ShadedBody.fullness s'' (fun i ↦ (U'' i).toShadedBody) ≥ δ' ^ ηd := by
    have hmono : δ' ^ ηd ≤ δ' ^ (3 * qc) :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ'0 hδ'1 h3qc
    have h := hcb.fullness_ge
    rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ'0)] at h
    exact le_trans hmono (by exact_mod_cast h)
  have _tie := Kakeya.ML2Core.middle_factor_of_edNodes
    (mm := 0) (hsitOut := hsitOut) (β := β) (ε₁ := ε₁) (gain := gain) (dens := dens) (k := k)
    (δ := δ) (w := w) (κc := κc) (t' := t') (Zρ := Zρ) (ηc := ηc)
    (cst := cst) (ζ' := ζ')
    (hcb := hcb) (hct := hct) (huni := ⟨habs, hstruct⟩) (hfull := hfull) (h3qc := h3qc)
  trivial

-- The four nested sites carry `hcoarse`'s two `spineRung` displays in every hypothesis, so
-- the unifier's work is bounded by the site, not by this tie.
set_option maxHeartbeats 1600000 in
-- TIE 6 : Kakeya.ML2Core.middle_factor_of_edNodes_sharp
example
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ 0 qc fib s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ 0 ϖ ζ s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hstruct : Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ')
      (ShadedTube.ssfUniformConst 3)))
    (habs : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd))
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd) : True := by
  have hfull : ShadedBody.fullness s'' (fun i ↦ (U'' i).toShadedBody) ≥ δ' ^ ηd := by
    have hmono : δ' ^ ηd ≤ δ' ^ (3 * qc) :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ'0 hδ'1 h3qc
    have h := hcb.fullness_ge
    rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ'0)] at h
    exact le_trans hmono (by exact_mod_cast h)
  have _tie := Kakeya.ML2Core.middle_factor_of_edNodes_sharp
    (mm := 0) (hsitOut := hsitOut) (β := β) (ε₁ := ε₁) (gain := gain) (dens := dens) (k := k)
    (δ := δ) (w := w) (κc := κc) (t' := t') (Zρ := Zρ) (ηc := ηc)
    (cst := cst) (ζ' := ζ')
    (hcb := hcb) (hct := hct) (huni := ⟨habs, hstruct⟩) (hfull := hfull) (h3qc := h3qc)
  trivial

end Ties

end
