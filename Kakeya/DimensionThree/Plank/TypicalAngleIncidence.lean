/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.TypicalAngle
public import Kakeya.LEApprox
public import Kakeya.Mathlib.MeasureTheory.BoundedOverlap
public import Kakeya.ConstantMultiplicity

/-!
# GWZ Lemma 6.11 (final proof layer)

This module, in namespace `Kakeya`, contains
the good-refinement typical-angle stability lemmas and the uniform and reserve forms of GWZ
Lemma 6.11 (`findingTypicalAngleOfIntersection`).
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real

noncomputable section

namespace Kakeya

variable {ι : Type*}

open scoped Classical in
/-- **A good refinement preserves the typical angle**
(extra6, `lem:typicalAngleSubrefinementStable`, pointwise + density part).
If `(𝒫, Y')` is a good `cgood`-refinement of `(𝒫, Y₁)` (same planks, `Y' i ⊆ Y₁ i`) whose fibres
each keep a `≥ A⁻¹ = (plankAngleScaleA a)⁻¹` fraction of the `Y₁`-fibre (`hkeep`), and `θ` is a
typical angle for `(𝒫, Y₁)` in the operative sense (the pointwise `∼ θ` bound survives any
`≥ A⁻¹`-fraction sub-refinement, `hstab₁`), then `θ` is again a pointwise typical angle for
`(𝒫, Y')`, and the density is preserved: `cgood · λ(𝒫, Y₁) ≤ λ(𝒫, Y')`. This is the pointwise +
density content of blueprint Steps 1-3; the further-sub-refinement stability clause for `Y'` holds
only at the enlarged scale `A² = (plankAngleScaleA a)²` and is deferred (see the blueprint note). -/
theorem typicalAngleSubrefinementStable
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s : Finset ι) (Y₁ Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (P : ι → Plank a b hab hb1) (θ Cθ cgood : ℝ≥0)
    (href : ShadedBody.IsCRefinement s Y' s Y₁ cgood)
    (hkeep : ∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
      (plankAngleScaleA a)⁻¹ * ((shadeFibre s Y₁ x).card : ℝ) ≤ ((shadeFibre s Y' x).card : ℝ))
    (hstab₁ : ∀ x ∈ ⋃ i ∈ s, (Y₁ i).shade, ∀ t ⊆ shadeFibre s Y₁ x,
      (plankAngleScaleA a)⁻¹ * ((shadeFibre s Y₁ x).card : ℝ) ≤ (t.card : ℝ) →
        θ ≤ Cθ * maxPlankAngle P t ∧ maxPlankAngle P t ≤ Cθ * θ) :
    (∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
      θ ≤ Cθ * maxPlankAngle P (shadeFibre s Y' x) ∧
        maxPlankAngle P (shadeFibre s Y' x) ≤ Cθ * θ) ∧
    cgood * ShadedBody.fullness s Y₁ ≤ ShadedBody.fullness s Y' := by
  have hshadesub : ∀ i ∈ s, (Y' i).shade ⊆ (Y₁ i).shade := fun i hi => (href.1.2 i hi).2
  refine ⟨fun x hx => ?_, ?_⟩
  · refine hstab₁ x (Set.iUnion₂_mono hshadesub hx) (shadeFibre s Y' x)
      (fun j hj => ?_) (hkeep x hx)
    rw [mem_shadeFibre] at hj ⊢
    exact ⟨hj.1, hshadesub j hj.1 hj.2⟩
  · have hcarsum : ∑ i ∈ s, volume (Y' i).carrier = ∑ i ∈ s, volume (Y₁ i).carrier :=
      Finset.sum_congr rfl fun i hi =>
        congrArg (fun cb => volume (ConvexSpaceBody.carrier cb)) (href.1.2 i hi).1
    rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ShadedBody.fullness_def, ShadedBody.fullness_def,
      hcarsum, ← mul_div_assoc]
    exact ENNReal.div_le_div_right href.2 _

universe u

/-- **The common core of the uniform and reserve forms of GWZ Lemma 6.11.**

The two scales are abstracted: `SA a` is the sub-fibre cardinality threshold at which the
stability clauses are asserted, and `SB a` is the retention scale of the per-fibre stopping-time
selection.  The ordinary form uses `typicalAngleFibre` and `refineConst_bound_uniform`; the reserve
form uses `typicalAngleFibre_reserve` and `refineConst_bound_uniform_reserve`. -/
private lemma findingTypicalAngleOfIntersection_core {ε : ℝ} (hε : 0 < ε) (C₀ : ℝ≥0) (Nexp : ℝ)
    (SA SB : ℝ≥0 → ℝ) (hSBpos : ∀ a : ℝ≥0, 0 < a → a < 1 → 0 < SB a)
    (Cε : ℝ) (hCεpos : 0 < Cε)
    (hCε : ∀ a : ℝ, 0 < a → a < 1 →
      Real.exp ((Real.log a⁻¹) ^ (3 / 4 : ℝ)) ≤ Cε * a ^ (-ε))
    (Kref : ℝ) (hKref0 : 0 ≤ Kref)
    (hKrefbd : ∀ {a b δ : ℝ≥0}, 0 < a → a < 1 → a ≤ b → b ≤ 1 → 0 < δ → δ ≤ a →
      ∀ sc : ℕ, (sc : ℝ) ≤ (C₀ : ℝ) * (δ : ℝ) ^ (-Nexp) →
        ∀ {c2 : ℝ}, 0 < c2 →
          ((Real.log ((b : ℝ) / a) / Real.log 2 + 2)
              * (Real.log (sc : ℝ) / Real.log 2 + 1))⁻¹ ≤ c2 →
          (δ : ℝ) ^ ε * (c2⁻¹ * SB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ)) ≤ Kref)
    (hfibre : ∀ {κ : Type u} {a b : ℝ≥0} (_ : 0 < a) (_ : a < 1) (hab : a ≤ b)
      (hb1 : b ≤ 1)
      (P : κ → Plank a b hab hb1) (F : Finset κ), F.Nonempty →
      ∃ (θ : ℝ≥0) (G : Finset κ), G ⊆ F ∧ G.Nonempty ∧
        (SB a)⁻¹ * (F.card : ℝ) ≤ (G.card : ℝ) ∧
        maxPlankAngle P G = θ ∧
        (∀ ⦃H : Finset κ⦄, H ⊆ G → (SA a)⁻¹ * (G.card : ℝ) ≤ (H.card : ℝ) →
          (plankAngleScaleB a)⁻¹ * (θ : ℝ) ≤ (maxPlankAngle P H : ℝ) ∧
            (maxPlankAngle P H : ℝ) ≤ (θ : ℝ))) :
    ∃ C : ℝ≥0, 2 ≤ C ∧ C ≤ Kref.toNNReal ⊔ 2 ⊔ (2 * Cε.toNNReal) ∧
      ∀ {κ : Type u} (s : Finset κ) (Y : κ → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        {a b δ : ℝ≥0} (_ : 0 < a) (_ : a < 1) (hab : a ≤ b) (hb1 : b ≤ 1)
        (_ : 0 < δ) (_ : δ ≤ a)
        (P : κ → Plank a b hab hb1),
        (∀ i ∈ s, (Y i).shade ⊆ (P i).carrier) →
        ∀ {η : ℝ}, 0 < η →
        (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s Y →
        (s.card : ℝ≥0) ≤ C₀ * δ ^ (-Nexp) →
        ∃ (Y' : κ → ShadedBody (EuclideanSpace ℝ (Fin 3))) (θ : ℝ≥0),
          ShadedBody.IsCRefinement s Y' s Y (C⁻¹ * δ ^ ε) ∧
          a / b ≤ θ ∧ θ ≤ 1 ∧
          ShadedBody.HasCConstantMultiplicity s Y' C ∧
          (∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
            θ ≤ C * maxPlankAngle P (shadeFibre s Y' x) ∧
              maxPlankAngle P (shadeFibre s Y' x) ≤ C * θ) ∧
          (∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
            ∀ t ⊆ shadeFibre s Y' x,
              (SA a)⁻¹ * ((shadeFibre s Y' x).card : ℝ) ≤ (t.card : ℝ) →
                θ ≤ C * δ ^ (-ε) * maxPlankAngle P t ∧
                  maxPlankAngle P t ≤ C * δ ^ (-ε) * θ) ∧
          (∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
            ∀ t ⊆ shadeFibre s Y' x,
              (SA a)⁻¹ * ((shadeFibre s Y' x).card : ℝ) ≤ (t.card : ℝ) →
                (θ : ℝ) ≤ 2 * plankAngleScaleB a * ((maxPlankAngle P t : ℝ≥0) : ℝ)) ∧
          HasMaxPlankAngleBound s Y' P θ 1 := by -- (extracted by Fuse golfer)
  obtain ⟨C, hC2le, hCKle, hCεle, hCub⟩ :
      ∃ C : ℝ≥0, 2 ≤ C ∧ Kref.toNNReal ≤ C ∧ 2 * Cε.toNNReal ≤ C ∧
        C ≤ Kref.toNNReal ⊔ 2 ⊔ (2 * Cε.toNNReal) :=
    ⟨Kref.toNNReal ⊔ 2 ⊔ (2 * Cε.toNNReal), le_sup_of_le_left le_sup_right,
      le_sup_of_le_left le_sup_left, le_sup_right, le_rfl⟩
  have hC1le : (1:ℝ≥0) ≤ C := one_le_two.trans hC2le
  have hCpos : 0 < C := two_pos.trans_le hC2le
  refine ⟨C, hC2le, hCub, ?_⟩
  intro κ s Y a b δ ha ha1 hab hb1 hδ hδa P hYP η hη hμ hcard
  have hδ1 : δ < 1 := lt_of_le_of_lt hδa ha1
  -- **Step 1.** Replace `(𝒫, Y)` by a `≈ 1`-refinement `(𝒫, Y₁)` of constant multiplicity.
  obtain ⟨Y₁, _hY₁ref, hY₁const, hY₁mass⟩ :=
    ShadedBody.exists_constantMultiplicity_refinement s Y
  -- **Step 2.** Per-fibre stopping-time selection.
  have key : ∀ F : Finset κ, ∃ G : Finset κ, G ⊆ F ∧ (F.Nonempty →
      (SB a)⁻¹ * (F.card : ℝ) ≤ (G.card : ℝ) ∧
      (∀ H ⊆ G, (SA a)⁻¹ * (G.card : ℝ) ≤ (H.card : ℝ) →
        (plankAngleScaleB a)⁻¹ * (maxPlankAngle P G : ℝ) ≤ (maxPlankAngle P H : ℝ) ∧
          (maxPlankAngle P H : ℝ) ≤ (maxPlankAngle P G : ℝ))) := by
    intro F
    by_cases hF : F.Nonempty
    · obtain ⟨θF, G, hGF, -, hmass, hMG, hstab⟩ := hfibre ha ha1 hab hb1 P F hF
      refine ⟨G, hGF, fun _ => ⟨hmass, fun H hHG hHc => ?_⟩⟩
      rw [hMG]; exact hstab hHG hHc
    · exact ⟨∅, Finset.empty_subset _, fun h => absurd h hF⟩
  choose sel hselsub hsel_pos using key
  -- **Glue** (Lemma `pointwiseSelectionRefinement`).
  obtain ⟨Ya, _hYa_shade, _hYa_ref, hYa_fibre, hYa_mass⟩ :=
    pointwiseSelectionRefinement s Y₁ sel hselsub
  -- `Θ := maxPlankAngle P` is fibre-determined and lies in `[a/b, 1]` on `U(Ya)`.
  have hΘ : ∀ x ∈ ⋃ i ∈ s, (Ya i).shade,
      a / b ≤ maxPlankAngle P (shadeFibre s Ya x) ∧ maxPlankAngle P (shadeFibre s Ya x) ≤ 1 := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.1 hx
    exact maxPlankAngle_mem_Icc P ⟨i, (mem_shadeFibre s Ya x i).2 ⟨hi, hix⟩⟩
  -- **Uniformise** (Lemma `constantTypicalAngle`).
  obtain ⟨Y2, θ, c2, hc2pos, _hc2bd, hY2ref, hθlb, hθub, hY2const, hY2fibre, hY2theta⟩ :=
    constantTypicalAngle s Ya ha hab hb1 (maxPlankAngle P) (fun x hx => (hΘ x hx).1)
      (fun x hx => (hΘ x hx).2)
  -- Scale bookkeeping.
  have hBpos : 0 < plankAngleScaleB a := lt_trans one_pos (one_lt_plankAngleScaleB ha ha1)
  have hSpos : 0 < SB a := hSBpos a ha ha1
  obtain ⟨Bnn, hBnn, hBnn_coe⟩ :
      ∃ B : ℝ≥0, B = (plankAngleScaleB a).toNNReal ∧ (B : ℝ) = plankAngleScaleB a :=
    ⟨_, rfl, Real.coe_toNNReal _ hBpos.le⟩
  obtain ⟨lam, hlam⟩ : ∃ l : ℝ≥0, l = ((SB a).toNNReal)⁻¹ := ⟨_, rfl⟩
  have hlam_coe : (lam : ℝ) = (SB a)⁻¹ := by
    rw [hlam, NNReal.coe_inv, Real.coe_toNNReal _ hSpos.le]
  have hYa_isref : ShadedBody.IsCRefinement s Ya s Y₁ lam := by
    refine hYa_mass lam fun F => ?_
    rw [hlam_coe]
    rcases F.eq_empty_or_nonempty with rfl | hF
    · rw [Finset.card_empty, Nat.cast_zero, mul_zero]; exact Nat.cast_nonneg _
    · exact (hsel_pos F hF).1
  -- The composed retained fraction.
  have hk₁pos : 0 < Nat.log 2 s.card + 1 := Nat.succ_pos _
  obtain ⟨frac, hfrac⟩ :
      ∃ f : ℝ≥0, f = c2 * lam * ((Nat.log 2 s.card + 1 : ℕ) : ℝ≥0)⁻¹ := ⟨_, rfl⟩
  -- Composed mass bound: `frac · ∑Y ≤ ∑Y2`.
  have hmass2 : (frac : ENNReal) * ∑ i ∈ s, volume (Y i).shade
      ≤ ∑ i ∈ s, volume (Y2 i).shade := by
    rw [hfrac]
    exact coe_mul_le_of_three_step hk₁pos (by rw [← nsmul_eq_mul]; exact hY₁mass)
      hYa_isref.2 hY2ref.2
  have hBdb : Bnn ≤ Cε.toNNReal * δ ^ (-ε) := by
    rw [hBnn]
    exact toNNReal_le_toNNReal_mul_rpow_neg hBpos hCεpos hδ hδa hε
      (hCε (a:ℝ) (NNReal.coe_pos.2 ha) (NNReal.coe_lt_one.2 ha1))
  -- **a-controlled refinement constant**, via `hKrefbd` (which genuinely uses `hcard`).
  have hcardR : ((s.card : ℕ) : ℝ) ≤ (C₀ : ℝ) * (δ : ℝ) ^ (-Nexp) := by
    have h := NNReal.coe_le_coe.2 hcard
    rwa [NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_natCast] at h
  have ha_nε1 : (1:ℝ≥0) ≤ δ ^ (-ε) := one_le_rpow_neg hε.le hδ hδ1.le
  -- The refinement constant bound `C⁻¹ · a^ε ≤ frac`.
  have hrefbd : C⁻¹ * δ ^ ε ≤ frac := by
    rw [hfrac, hlam]
    refine inv_mul_rpow_le_frac hδ hc2pos hSpos hk₁pos hCpos
      ((hKrefbd ha ha1 hab hb1 hδ hδa s.card hcardR (NNReal.coe_pos.2 hc2pos) _hc2bd).trans ?_)
    rw [← Real.coe_toNNReal Kref hKref0]
    exact NNReal.coe_le_coe.2 hCKle
  -- Transitivity of the refinement relation.
  have hY2_ref_Y : ShadedBody.IsRefinement s Y2 s Y :=
    ⟨subset_rfl, fun i hi =>
      ⟨((hY2ref.1.2 i hi).1.trans (hYa_isref.1.2 i hi).1).trans (_hY₁ref.2 i hi).1,
        (hY2ref.1.2 i hi).2.trans ((hYa_isref.1.2 i hi).2.trans (_hY₁ref.2 i hi).2)⟩⟩
  -- The two stability clauses share all their bookkeeping; prove it once.
  have hstabkey : ∀ x ∈ ⋃ i ∈ s, (Y2 i).shade, ∀ t ⊆ shadeFibre s Y2 x,
      (SA a)⁻¹ * ((shadeFibre s Y2 x).card : ℝ) ≤ (t.card : ℝ) →
        maxPlankAngle P t ≤ θ ∧ θ ≤ 2 * Bnn * maxPlankAngle P t := by
    intro x hx t ht hcardt
    have hfib2 : shadeFibre s Y2 x = sel (shadeFibre s Y₁ x) := by
      rw [hY2fibre x hx, hYa_fibre x]
    obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.1 hx
    have hFne : (shadeFibre s Y₁ x).Nonempty :=
      Finset.Nonempty.mono (hselsub _) (hfib2 ▸ ⟨i, (mem_shadeFibre s Y2 x i).2 ⟨hi, hix⟩⟩)
    have hstab := (hsel_pos (shadeFibre s Y₁ x) hFne).2
    rw [← hfib2] at hstab
    obtain ⟨hlow, hupp⟩ := hstab t ht hcardt
    have hB : maxPlankAngle P (shadeFibre s Y2 x) ≤ Bnn * maxPlankAngle P t := by
      rw [← NNReal.coe_le_coe, NNReal.coe_mul, hBnn_coe]
      exact (inv_mul_le_iff₀ hBpos).1 hlow
    exact ⟨(NNReal.coe_le_coe.1 hupp).trans (hY2theta x hx).1,
      ((hY2theta x hx).2.trans (mul_le_mul_right hB 2)).trans (mul_assoc 2 Bnn _).ge⟩
  have hCa1 : (1:ℝ≥0) ≤ C * δ ^ (-ε) := hC1le.trans (le_mul_of_one_le_right zero_le ha_nε1)
  have h2B : 2 * Bnn ≤ C * δ ^ (-ε) :=
    (mul_le_mul_right hBdb 2).trans ((mul_assoc 2 _ _).ge.trans (mul_le_mul_left hCεle _))
  refine ⟨Y2, θ, ⟨hY2_ref_Y, le_trans (mul_le_mul_left (ENNReal.coe_le_coe.2 hrefbd) _) hmass2⟩,
    hθlb, hθub, fun x hx y hy => (hY2const hx hy).trans (mul_le_mul_left hC2le _),
    fun x hx => ⟨(hY2theta x hx).2.trans (mul_le_mul_left hC2le _),
      (hY2theta x hx).1.trans (le_mul_of_one_le_left zero_le hC1le)⟩,
    fun x hx t ht hcardt => ⟨(hstabkey x hx t ht hcardt).2.trans (mul_le_mul_left h2B _),
      (hstabkey x hx t ht hcardt).1.trans (le_mul_of_one_le_left zero_le hCa1)⟩,
    fun x hx t ht hcardt => ?_, fun x hx => by rw [one_mul]; exact (hY2theta x hx).1⟩
  -- Extra stability at the `plankAngleScaleB a` scale.
  have h := (hstabkey x hx t ht hcardt).2
  rwa [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_mul, hBnn_coe, NNReal.coe_ofNat] at h

/-- **GWZ Lemma 6.11**, at the intrinsic plank scale `a`.

The shared constant `C` is quantified *before* the index type and the finite configuration, and
depends only on the sub-polynomial exponent `ε` and on the two data `C₀`, `Nexp` of the polynomial
plank-count bound `|𝒫| ≤ C₀ · a ^ (-Nexp)`.

This is the quantitative form of the lemma, and it is the form its consumers need.  With `C`
existentially quantified after the configuration, the refinement conclusion
`ShadedBody.IsCRefinement s Y' s Y (C⁻¹ · a ^ ε)` carries no information: `C` could be taken to be
the reciprocal of the actual retained fraction of the finite family at hand.  Here `C` is
`Kref ⊔ 2 ⊔ (2 · Cε)` where `Cε` comes from `Kakeya.subpolyExp` (a function of `ε` alone) and `Kref`
from `Kakeya.refineConst_bound_uniform` (a function of `ε`, `C₀` and `Nexp` alone), so the
refinement loss of the typical-angle step is the explicit `C⁻¹ · a ^ ε` with `C` uniform.  That is
what lets `Kakeya.plankReduction` state explicit lower bounds for its refinement and cardinality
constants `cLam` and `cP`.

There is no auxiliary ambient scale anywhere in this development: the only geometric data are the
plank dimensions `a`, `b` and the exponents `ε`, `η`, `Nexp`.  GWZ state the multiplicity
hypothesis of Lemma 6.11 at an ambient scale `δ`, but their proof only ever uses it at the plank
scale `a`, and GWZ Lemma 6.13 invokes the lemma from `μ(𝒫, Y) ≥ a ^ (-η)` with no independent `δ`;
so the `a`-scale form is the faithful one.  A general `δ ≤ a` form would not buy anything either:
its multiplicity hypothesis `μ(𝒫, Y) ≥ δ ^ (-η)` is stronger while its losses `δ ^ (±ε)` are
weaker, and the one genuinely wider hypothesis, the plank-count bound `|𝒫| ≤ C₀ · δ ^ (-Nexp)`, is
recovered at `δ = a ^ k` by taking `Nexp := k · N`, since `Nexp` is quantified before `C`.

It is obtained from the common stopping-time core at the ordinary scales `plankAngleScaleA a` and
`plankAngleScaleB a`. -/
theorem findingTypicalAngleOfIntersection {ε : ℝ} (hε : 0 < ε) (C₀ : ℝ≥0) (Nexp : ℝ) :
    ∃ C : ℝ≥0, 2 ≤ C ∧
      ∀ {ι : Type*} (s : Finset ι) (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        {a b : ℝ≥0} (_ : 0 < a) (_ : a < 1) (hab : a ≤ b) (hb1 : b ≤ 1)
        (P : ι → Plank a b hab hb1),
        (∀ i ∈ s, (Y i).shade ⊆ (P i).carrier) →
        ∀ {η : ℝ}, 0 < η →
        (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s Y →
        (s.card : ℝ≥0) ≤ C₀ * a ^ (-Nexp) →
        ∃ (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (θ : ℝ≥0),
          ShadedBody.IsCRefinement s Y' s Y (C⁻¹ * a ^ ε) ∧
          a / b ≤ θ ∧ θ ≤ 1 ∧
          ShadedBody.HasCConstantMultiplicity s Y' C ∧
          (∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
            θ ≤ C * maxPlankAngle P (shadeFibre s Y' x) ∧
              maxPlankAngle P (shadeFibre s Y' x) ≤ C * θ) ∧
          (∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
            ∀ t ⊆ shadeFibre s Y' x,
              (plankAngleScaleA a)⁻¹ * ((shadeFibre s Y' x).card : ℝ) ≤ (t.card : ℝ) →
                θ ≤ C * a ^ (-ε) * maxPlankAngle P t ∧
                  maxPlankAngle P t ≤ C * a ^ (-ε) * θ) ∧
          HasMaxPlankAngleBound s Y' P θ 1 := by
  obtain ⟨Kref, hKref0, hKrefbd⟩ := refineConst_bound_uniform_perScale hε C₀ Nexp
  obtain ⟨Cε, hCεpos, hCε⟩ :=
    subpolyExp (show (0:ℝ) ≤ 3/4 by norm_num) (show (3/4:ℝ) < 1 by norm_num) hε
  obtain ⟨C, hC2, -, H⟩ :=
    findingTypicalAngleOfIntersection_core hε C₀ Nexp plankAngleScaleA plankAngleScaleB
      (fun _ ha ha1 => zero_lt_one.trans (one_lt_plankAngleScaleB ha ha1))
      Cε hCεpos hCε
      Kref hKref0 (fun ha ha1 hab hb1 hδ hδa sc hsc (c2 : ℝ) hc2 hc2bd =>
        hKrefbd ha ha1 hab hb1 hδ hδa sc hsc hc2 hc2bd)
      fun ha ha1 hab hb1 P F hF =>
        (typicalAngleFibre ha ha1 hab hb1 P F hF).imp fun _ h => h.imp fun _ h =>
          ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  exact ⟨C, hC2, fun s Y _ _ ha ha1 hab hb1 P hYP _ hη hμ hcard =>
    (H s Y ha ha1 hab hb1 ha le_rfl P hYP hη hμ hcard).imp fun _ h => h.imp fun _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩⟩

/-- **GWZ Lemma 6.11 at an auxiliary scale, with the growth of the comparison constant in the
plank-count constant `C₀` exposed.**

`Kakeya.findingTypicalAngleOfIntersection_scaled` quantifies its constant *after* `C₀`, so
nothing in its statement says how the constant depends on `C₀`.  That is fatal for the one
Section-9 consumer that feeds it a `δ`-dependent `C₀`: the clause
`Kakeya.VeryNotSticky.CaseScale.typicalAngle_const` supplies
`C₀ = C_{plankCard} · C(bd.C₀) · C_bias · δ^{-2ϱ}` and asks the resulting constant to be at
most `(δ/r₁)^{-η/16}`.  With `Kakeya.CaseParams.densityBias` forcing `ϱ > 2^20 η`, no *power*
of `C₀` can satisfy that, and an opaque `Classical.choose` constant offers no other option —
which is exactly why that clause was unprovable as stated.

Here a single `A`, a function of `ε` and `Nexp` alone, works for every `C₀`, at the cost of the
factor `(log⁺C₀ + 1)²`.  The growth is **polylogarithmic**, and polylogarithmic growth is
beaten by every positive power of `δ⁻¹`, so the clause becomes an honest fixed-scale threshold.

The two ingredients are `Kakeya.exists_refineConst_bound_perScale_uniform`, which carries the
whole `C₀`-dependence (through `Kakeya.logargConst`, the dyadic count of the plank family, which
is a *logarithm* of `C₀`), and `Kakeya.subpolyExp`, which does not mention `C₀` at all and is
hoisted out of `findingTypicalAngleOfIntersection_core` for exactly that reason. -/
theorem exists_typicalAngleScaled_uniformBase.{w} {ε : ℝ} (hε : 0 < ε) (Nexp : ℝ) :
    ∃ A : ℝ≥0, ∀ C₀ : ℝ≥0, ∃ C : ℝ≥0, 2 ≤ C ∧
      C ≤ A * (Real.toNNReal (Real.log (C₀ : ℝ)) + 1) ^ 2 ∧
      ∀ {ι : Type w} (s : Finset ι) (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        {a b δ : ℝ≥0} (_ : 0 < a) (_ : a < 1) (hab : a ≤ b) (hb1 : b ≤ 1)
        (_ : 0 < δ) (_ : δ ≤ a) (P : ι → Plank a b hab hb1),
        (∀ i ∈ s, (Y i).shade ⊆ (P i).carrier) →
        ∀ {η : ℝ}, 0 < η →
        (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s Y →
        (s.card : ℝ≥0) ≤ C₀ * δ ^ (-Nexp) →
        ∃ (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (θ : ℝ≥0),
          ShadedBody.IsCRefinement s Y' s Y (C⁻¹ * δ ^ ε) ∧
          a / b ≤ θ ∧ θ ≤ 1 ∧
          ShadedBody.HasCConstantMultiplicity s Y' C ∧
          IsTypicalPlankAngle s Y' P θ (C * δ ^ (-ε))
            (Real.toNNReal (plankAngleScaleA a)) ∧
          (∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
            ComparableScalars C θ (maxPlankAngle P (shadeFibre s Y' x))) ∧
          HasMaxPlankAngleBound s Y' P θ 1 := by
  obtain ⟨A0, hA0, hAbd⟩ := exists_refineConst_bound_perScale_uniform hε Nexp
  obtain ⟨Cε, hCεpos, hCε⟩ :=
    subpolyExp (show (0:ℝ) ≤ 3/4 by norm_num) (show (3/4:ℝ) < 1 by norm_num) hε
  refine ⟨Real.toNNReal A0 ⊔ 2 ⊔ (2 * Real.toNNReal Cε), fun C₀ => ?_⟩
  obtain ⟨C, hC2, hCub, H⟩ :=
    findingTypicalAngleOfIntersection_core.{w} hε C₀ Nexp plankAngleScaleA plankAngleScaleB
      (fun _ ha ha1 => zero_lt_one.trans (one_lt_plankAngleScaleB ha ha1))
      Cε hCεpos hCε
      (A0 * (max (Real.log (C₀ : ℝ)) 0 + 1) ^ 2)
      (by positivity)
      (fun ha ha1 hab hb1 hδ hδa sc hsc (c2 : ℝ) hc2 hc2bd =>
        hAbd C₀ ha ha1 hab hb1 hδ hδa sc hsc hc2 hc2bd)
      (fun ha ha1 hab hb1 P F hF =>
        (typicalAngleFibre ha ha1 hab hb1 P F hF).imp fun _ h => h.imp fun _ h =>
          ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩)
  refine ⟨C, hC2, ?_, ?_⟩
  · -- The growth bound: everything the core's constant is a supremum of is at most `A`, and
    -- the one `C₀`-dependent member is `A₀ · (log⁺C₀ + 1)²`.
    refine hCub.trans ?_
    have hLR : (0:ℝ) ≤ max (Real.log (C₀ : ℝ)) 0 := le_max_right _ _
    have hx0 : (0:ℝ) ≤ max (Real.log (C₀ : ℝ)) 0 + 1 := by linarith
    have hmaxN : Real.toNNReal (max (Real.log (C₀ : ℝ)) 0)
        = Real.toNNReal (Real.log (C₀ : ℝ)) := by
      refine NNReal.coe_injective ?_
      rw [Real.coe_toNNReal', Real.coe_toNNReal', max_assoc, max_self]
    have h1 : Real.toNNReal (max (Real.log (C₀ : ℝ)) 0 + 1)
        = Real.toNNReal (Real.log (C₀ : ℝ)) + 1 := by
      rw [Real.toNNReal_add hLR zero_le_one, Real.toNNReal_one, hmaxN]
    have h3 : Real.toNNReal (A0 * (max (Real.log (C₀ : ℝ)) 0 + 1) ^ 2)
        = Real.toNNReal A0 * (Real.toNNReal (Real.log (C₀ : ℝ)) + 1) ^ 2 := by
      rw [Real.toNNReal_mul hA0, sq, Real.toNNReal_mul hx0, h1, sq]
    have hM1 : (1:ℝ≥0) ≤ (Real.toNNReal (Real.log (C₀ : ℝ)) + 1) ^ 2 := by
      have : (1:ℝ≥0) ≤ Real.toNNReal (Real.log (C₀ : ℝ)) + 1 := le_add_self
      simpa using one_le_pow_of_one_le' this 2
    have hAM : (Real.toNNReal A0 ⊔ 2 ⊔ (2 * Real.toNNReal Cε))
        ≤ (Real.toNNReal A0 ⊔ 2 ⊔ (2 * Real.toNNReal Cε)) *
            (Real.toNNReal (Real.log (C₀ : ℝ)) + 1) ^ 2 :=
      le_mul_of_one_le_right (zero_le') hM1
    rw [h3]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact mul_le_mul_right' (le_sup_of_le_left le_sup_left) _
    · exact le_trans (le_sup_of_le_left le_sup_right) hAM
    · exact le_trans le_sup_right hAM
  intro ι s Y a b δ ha ha1 hab hb1 hδ hδa P hYP η hη hμ hcard
  obtain ⟨Y', θ, href, hθab, hθ1, hconst, hcomp, hstab, -, hmax⟩ :=
    H s Y ha ha1 hab hb1 hδ hδa P hYP hη hμ hcard
  -- `C ≤ C · δ ^ (-ε)`, the constant of the two-sided typicality predicate.
  have hδ1 : δ < 1 := lt_of_le_of_lt hδa ha1
  have hpow1 : (1 : ℝ≥0) ≤ δ ^ (-ε) := one_le_rpow_neg hε.le hδ hδ1.le
  have hCle : C ≤ C * δ ^ (-ε) := le_mul_of_one_le_right zero_le hpow1
  -- The stability threshold, transported from `ℝ` to `ℝ≥0`.
  have hApos : (0 : ℝ) < plankAngleScaleA a := Real.exp_pos _
  have hAcoe : ((Real.toNNReal (plankAngleScaleA a) : ℝ≥0) : ℝ) = plankAngleScaleA a :=
    Real.coe_toNNReal _ hApos.le
  refine ⟨Y', θ, href, hθab, hθ1, hconst, ?_, hcomp, hmax⟩
  intro x hx
  refine ⟨⟨(hcomp x hx).1.trans (by gcongr), (hcomp x hx).2.trans (by gcongr)⟩, ?_⟩
  intro t ht hct
  have hctR : (plankAngleScaleA a)⁻¹ * ((shadeFibre s Y' x).card : ℝ) ≤ (t.card : ℝ) := by
    have h := NNReal.coe_le_coe.2 hct
    rwa [NNReal.coe_mul, NNReal.coe_inv, hAcoe, NNReal.coe_natCast, NNReal.coe_natCast] at h
  exact ⟨(hstab x hx t ht hctR).1, (hstab x hx t ht hctR).2⟩

/-- **GWZ Lemma 6.11 at an auxiliary scale `δ ≤ a`.**

This is `Kakeya.findingTypicalAngleOfIntersection` with every `a`-scale quantity that the *losses*
are measured in replaced by an auxiliary scale `δ ≤ a`: the plank-count hypothesis is
`|𝒫| ≤ C₀ · δ ^ (-Nexp)`, the multiplicity hypothesis is `μ(𝒫, Y) ≥ δ ^ (-η)`, the refinement loss
is `C⁻¹ · δ ^ ε` and the sub-fibre comparability constant is `C · δ ^ (-ε)`.  The *geometric*
scales are untouched: the stability threshold is still `Kakeya.plankAngleScaleA a` and the angle
still satisfies `a / b ≤ θ ≤ 1`.

As in the `a`-scale form, the shared constant `C` is quantified **before** the index type and the
whole geometric configuration, and depends only on `(ε, C₀, Nexp)`.  That is the only order in
which the statement is true.  With `C` existentially quantified *after* the configuration and
pinched from above by `C ≤ δ ^ (-ε)`, the conjunction of that pinch with
`ShadedBody.HasCConstantMultiplicity s Y' C` is refutable: fix `η = 1`, `ε` small, `C₀ = 3`,
`Nexp = 0` and `δ = a = b = 1/2`, so that `δ ^ (-ε)` is as close to `1` as one likes while the
multiplicity hypothesis `2 ≤ δ ^ (-η)` still holds, and take three pairwise essentially distinct
axis-aligned planks whose triple intersection has positive measure, shaded so that the
multiplicity is about `3` on a `99%`-mass core and about `1` on the rest.  Any admissible
refinement deletes a proportion at most `1 - C⁻¹ δ ^ ε`, which tends to `0`, so both a
positive-measure set of multiplicity `3` and one of multiplicity `1` survive, forcing `3 ≤ C`.
Hoisting `C` removes the pinch; a consumer that needs `C ≤ δ ^ (-ε)` now gets it as a *threshold
on `δ`*, which is legitimate precisely because `C` no longer depends on `δ`.

The proof is the common stopping-time core `findingTypicalAngleOfIntersection_core`, whose
refinement bookkeeping is supplied at the auxiliary scale by
`Kakeya.refineConst_bound_uniform_perScale`.  The output is packaged in the
`Kakeya.IsTypicalPlankAngle` form its Section 9 consumers read. -/
theorem findingTypicalAngleOfIntersection_scaled {ε : ℝ} (hε : 0 < ε) (C₀ : ℝ≥0) (Nexp : ℝ) :
    ∃ C : ℝ≥0, 2 ≤ C ∧
      ∀ {ι : Type*} (s : Finset ι) (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        {a b δ : ℝ≥0} (_ : 0 < a) (_ : a < 1) (hab : a ≤ b) (hb1 : b ≤ 1)
        (_ : 0 < δ) (_ : δ ≤ a) (P : ι → Plank a b hab hb1),
        (∀ i ∈ s, (Y i).shade ⊆ (P i).carrier) →
        ∀ {η : ℝ}, 0 < η →
        (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s Y →
        (s.card : ℝ≥0) ≤ C₀ * δ ^ (-Nexp) →
        ∃ (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (θ : ℝ≥0),
          ShadedBody.IsCRefinement s Y' s Y (C⁻¹ * δ ^ ε) ∧
          a / b ≤ θ ∧ θ ≤ 1 ∧
          ShadedBody.HasCConstantMultiplicity s Y' C ∧
          IsTypicalPlankAngle s Y' P θ (C * δ ^ (-ε))
            (Real.toNNReal (plankAngleScaleA a)) ∧
          (∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
            ComparableScalars C θ (maxPlankAngle P (shadeFibre s Y' x))) ∧
          HasMaxPlankAngleBound s Y' P θ 1 := by
  obtain ⟨A, hA⟩ := exists_typicalAngleScaled_uniformBase hε Nexp
  obtain ⟨C, hC2, -, H⟩ := hA C₀
  exact ⟨C, hC2, H⟩

/-- **The `C₀`-free part of the comparison constant of GWZ Lemma 6.11 at an auxiliary scale.**

`typicalAngleScaledBase ε Nexp` is the `A` of
`Kakeya.exists_typicalAngleScaled_uniformBase`: a function of `ε` and `Nexp` alone, valid for
every plank-count constant `C₀`. Outside the intended range `0 < ε` the value is the
placeholder `2`. -/
noncomputable def typicalAngleScaledBase.{w} (ε Nexp : ℝ) : ℝ≥0 :=
  open Classical in
  if h : 0 < ε then (exists_typicalAngleScaled_uniformBase.{w} h Nexp).choose else 2

/-- **The comparison constant of `Kakeya.findingTypicalAngleOfIntersection_scaled`, named.**

Since that lemma binds its constant before every geometric datum, the constant is a *function* of
`(ε, C₀, Nexp)` alone, and naming it is what lets a consumer state the threshold `C ≤ δ ^ (-ε)`
as a hypothesis on `δ`. Outside the intended range `0 < ε` the value is the placeholder `2`.

It is now read off `Kakeya.exists_typicalAngleScaled_uniformBase` rather than off
`Kakeya.findingTypicalAngleOfIntersection_scaled`, which is the same statement with the
constant's growth in `C₀` thrown away. Nothing about
`Kakeya.findingTypicalAngleOfIntersection_scaled_spec` changes; what is *gained* is
`Kakeya.typicalAngleScaledConst_le`, which bounds this constant by
`typicalAngleScaledBase ε Nexp · (log⁺C₀ + 1)²`. -/
noncomputable def typicalAngleScaledConst.{w} (ε : ℝ) (C₀ : ℝ≥0) (Nexp : ℝ) : ℝ≥0 :=
  open Classical in
  if h : 0 < ε then
    ((exists_typicalAngleScaled_uniformBase.{w} h Nexp).choose_spec C₀).choose
  else 2

/-- **The comparison constant of GWZ Lemma 6.11 at an auxiliary scale grows at most
polylogarithmically in the plank-count constant `C₀`.**

`typicalAngleScaledConst ε C₀ Nexp ≤ typicalAngleScaledBase ε Nexp · (log⁺C₀ + 1)²`, with
`typicalAngleScaledBase ε Nexp` independent of `C₀`.

This is the bound `Kakeya.VeryNotSticky.CaseScale.typicalAngle_const` needs and that a
`Classical.choose` constant could not supply. That clause feeds
`C₀ = C_{plankCard} · C(bd.C₀) · C_bias · δ^{-2ϱ}` and demands the result be at most
`(δ/r₁)^{-η/16}`; since `log⁺C₀ = O(log δ⁻¹)`, the left-hand side is `O((log δ⁻¹)²)`, which is
below any fixed positive power of `δ⁻¹` for all small `δ`. Without this bound the clause is
 unprovable from the statement of
`Kakeya.findingTypicalAngleOfIntersection_scaled`, whose constant is quantified after `C₀` and
therefore admits, as far as that statement goes, an arbitrary power of `C₀`. -/
theorem typicalAngleScaledConst_le.{w} {ε : ℝ} (hε : 0 < ε) (C₀ : ℝ≥0) (Nexp : ℝ) :
    typicalAngleScaledConst.{w} ε C₀ Nexp
      ≤ typicalAngleScaledBase.{w} ε Nexp * (Real.toNNReal (Real.log (C₀ : ℝ)) + 1) ^ 2 := by
  simp only [typicalAngleScaledConst, typicalAngleScaledBase, dif_pos hε]
  exact (((exists_typicalAngleScaled_uniformBase.{w} hε Nexp).choose_spec C₀).choose_spec).2.1

/-- `Kakeya.findingTypicalAngleOfIntersection_scaled` read at the named constant
`Kakeya.typicalAngleScaledConst`. -/
theorem findingTypicalAngleOfIntersection_scaled_spec.{w} {ε : ℝ} (hε : 0 < ε) (C₀ : ℝ≥0)
    (Nexp : ℝ) :
    2 ≤ typicalAngleScaledConst.{w} ε C₀ Nexp ∧
      ∀ {ι : Type w} (s : Finset ι) (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        {a b δ : ℝ≥0} (_ : 0 < a) (_ : a < 1) (hab : a ≤ b) (hb1 : b ≤ 1)
        (_ : 0 < δ) (_ : δ ≤ a) (P : ι → Plank a b hab hb1),
        (∀ i ∈ s, (Y i).shade ⊆ (P i).carrier) →
        ∀ {η : ℝ}, 0 < η →
        (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s Y →
        (s.card : ℝ≥0) ≤ C₀ * δ ^ (-Nexp) →
        ∃ (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (θ : ℝ≥0),
          ShadedBody.IsCRefinement s Y' s Y ((typicalAngleScaledConst.{w} ε C₀ Nexp)⁻¹ * δ ^ ε) ∧
          a / b ≤ θ ∧ θ ≤ 1 ∧
          ShadedBody.HasCConstantMultiplicity s Y' (typicalAngleScaledConst.{w} ε C₀ Nexp) ∧
          IsTypicalPlankAngle s Y' P θ (typicalAngleScaledConst.{w} ε C₀ Nexp * δ ^ (-ε))
            (Real.toNNReal (plankAngleScaleA a)) ∧
          (∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
            ComparableScalars (typicalAngleScaledConst.{w} ε C₀ Nexp) θ
              (maxPlankAngle P (shadeFibre s Y' x))) ∧
          HasMaxPlankAngleBound s Y' P θ 1 := by
  simp only [typicalAngleScaledConst, dif_pos hε]
  exact ⟨(((exists_typicalAngleScaled_uniformBase.{w} hε Nexp).choose_spec C₀).choose_spec).1,
    (((exists_typicalAngleScaled_uniformBase.{w} hε Nexp).choose_spec C₀).choose_spec).2.2⟩

/-- **GWZ Lemma 6.11 with the angular stability at the reserve scale `κ · A(a)²`** (extra69,
`rem:findingTypicalAngleStableReserve`).

This strengthens `Kakeya.findingTypicalAngleOfIntersection`: the two sub-fibre stability clauses
are asked at the *reserve* threshold
`(plankReserveScale kappa a)⁻¹ = (κ · plankAngleScaleA a ^ 2)⁻¹` in place of
`(plankAngleScaleA a)⁻¹`, for a `κ ≥ 1` quantified — together with `ε`, `C₀` and `Nexp` — before the
shared constant `C` and hence before every geometric datum.  Since the threshold is smaller,
strictly more sub-fibres are constrained, so this is a strengthening and not a reformulation.

This is the producer the reserve route of extra69 consumes:
`Plank.isTypicalPlankAngle_of_fibreRetention` transports the two-sided
`Kakeya.IsTypicalPlankAngle` across a deletion of retained fraction `q`
subject only to the multiplicative budget `A ≤ q · R`, so with output scale `A = plankAngleScaleA a`
and reserve `R = κ · A ²` the requirement is `q ≥ (κ · A)⁻¹`, which
`Kakeya.exists_natLog_succ_le_mul_plankAngleScaleA` supplies at `κ = C_res` for *every* `0 < a < 1`.
It is not obtainable from the squared per-fibre scale by
`Kakeya.IsTypicalPlankAngle.mono_scale`, which runs the other way since `κ ≥ 1`.

No smallness hypothesis on `a` is needed.  The per-fibre selection is run at the reserve scale by
`Kakeya.typicalAngleFibre_reserve`, whose only cost is the retained fraction of its selected
sub-fibre (`(plankAngleScaleB a * plankReserveLoss kappa a)⁻¹` instead of `(plankAngleScaleB a)⁻¹`).
That retention feeds only the refinement constant, and `Kakeya.refineConst_bound_uniform_reserve`
absorbs it into a larger uniform `C`, which is existentially quantified here anyway.  In particular
the comparability constants of both stability clauses, and the explicit `plankAngleScaleB a` of the
second one, are unchanged. -/
theorem findingTypicalAngleOfIntersection_stable_reserve {kappa : ℝ} (hkappa : 1 ≤ kappa)
    {ε : ℝ} (hε : 0 < ε) (C₀ : ℝ≥0) (Nexp : ℝ) :
    ∃ C : ℝ≥0, 2 ≤ C ∧
      ∀ {ι : Type*} (s : Finset ι) (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        {a b : ℝ≥0} (_ : 0 < a) (_ : a < 1) (hab : a ≤ b) (hb1 : b ≤ 1)
        (P : ι → Plank a b hab hb1),
        (∀ i ∈ s, (Y i).shade ⊆ (P i).carrier) →
        ∀ {η : ℝ}, 0 < η →
        (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s Y →
        (s.card : ℝ≥0) ≤ C₀ * a ^ (-Nexp) →
        ∃ (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (θ : ℝ≥0),
          ShadedBody.IsCRefinement s Y' s Y (C⁻¹ * a ^ ε) ∧
          a / b ≤ θ ∧ θ ≤ 1 ∧
          ShadedBody.HasCConstantMultiplicity s Y' C ∧
          (∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
            θ ≤ C * maxPlankAngle P (shadeFibre s Y' x) ∧
              maxPlankAngle P (shadeFibre s Y' x) ≤ C * θ) ∧
          (∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
            ∀ t ⊆ shadeFibre s Y' x,
              (plankReserveScale kappa a)⁻¹ * ((shadeFibre s Y' x).card : ℝ) ≤ (t.card : ℝ) →
                θ ≤ C * a ^ (-ε) * maxPlankAngle P t ∧
                  maxPlankAngle P t ≤ C * a ^ (-ε) * θ) ∧
          (∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
            ∀ t ⊆ shadeFibre s Y' x,
              (plankReserveScale kappa a)⁻¹ * ((shadeFibre s Y' x).card : ℝ) ≤ (t.card : ℝ) →
                (θ : ℝ) ≤ 2 * plankAngleScaleB a * ((maxPlankAngle P t : ℝ≥0) : ℝ)) ∧
          HasMaxPlankAngleBound s Y' P θ 1 := by
  obtain ⟨Kref, hKref0, hKrefbd⟩ := refineConst_bound_uniform_reserve_perScale kappa hε C₀ Nexp
  obtain ⟨Cε, hCεpos, hCε⟩ :=
    subpolyExp (show (0:ℝ) ≤ 3/4 by norm_num) (show (3/4:ℝ) < 1 by norm_num) hε
  obtain ⟨C, hC2, -, H⟩ := findingTypicalAngleOfIntersection_core hε C₀ Nexp
    (plankReserveScale kappa)
    (fun a => plankAngleScaleB a * plankReserveLoss kappa a)
    (fun a ha ha1 => mul_pos (zero_lt_one.trans (one_lt_plankAngleScaleB ha ha1))
      (plankReserveLoss_pos kappa a)) Cε hCεpos hCε Kref hKref0
    (fun ha ha1 hab hb1 hδ hδa sc hsc (c2 : ℝ) hc2 hc2bd =>
      hKrefbd ha ha1 hab hb1 hδ hδa sc hsc hc2 hc2bd)
    (fun ha ha1 hab hb1 P F hF => by
      obtain ⟨θ, G, h1, h2, -, -, h3, h4, h5⟩ :=
        typicalAngleFibre_reserve hkappa ha ha1 hab hb1 P F hF
      exact ⟨θ, G, h1, h2, h3, h4, h5⟩)
  exact ⟨C, hC2, fun s Y _ _ ha ha1 hab hb1 P hYP _ hη hμ hcard =>
    H s Y ha ha1 hab hb1 ha le_rfl P hYP hη hμ hcard⟩

section boundedOverlap

open Classical in
/-- **Bounded-overlap union estimate** (`lem:boundedOverlapUnionEstimate`).
Let `(𝒫, Y)` be a shaded family of planks and `(𝒫'_S, Y'_S)` for `S ∈ 𝒮` be subfamilies whose
unions `A_S := U(𝒫'_S, Y'_S) = ⋃_{i ∈ 𝒫'_S} (Y'_S i).shade` are measurable, each a subset of
`U(𝒫', Y')` (itself a subset of `U(𝒫, Y)`). Suppose every point lies in at most `C_ov` of the
sets `A_S`. Then the total mass comparison holds:
`|U(𝒫, Y)| >= |U(𝒫', Y')| >= c_3 * sum_S |U(𝒫'_S, Y'_S)|` with `c_3 = C_ov⁻¹`.
The estimate combines the bounded-overlap lemma
	(`MeasureTheory.sum_volume_le_mul_volume_biUnion`)
with the volume monotonicity from the inclusion `(⋃_S A_S) ⊆ U(𝒫, Y)`.

The `C_ov` bound is stated as `card_filter_le`: for each point `x`, the number of indices
`S ∈ 𝒮` with `x ∈ A_S` is at most `C_ov`. -/
theorem boundedOverlapUnionEstimate
    {σ : Type*} (𝒮 : Finset σ) (A : σ → Set (EuclideanSpace ℝ (Fin 3)))
    (hA : ∀ S ∈ 𝒮, MeasurableSet (A S))
    (hAsub : ∀ S ∈ 𝒮, A S ⊆ U) {C_ov : ℕ}
    (hbound : ∀ x, {i ∈ 𝒮 | x ∈ A i}.card ≤ C_ov) :
    ((C_ov : ENNReal)⁻¹ * ∑ S ∈ 𝒮, volume (A S)) ≤ volume U := by
  -- `∑ S, |A S| ≤ C_ov * |⋃ S, A S| ≤ |U| * C_ov`, then divide by `C_ov`.
  rw [← ENNReal.div_eq_inv_mul]
  refine ENNReal.div_le_of_le_mul ((MeasureTheory.sum_volume_le_mul_volume_biUnion
    (s := 𝒮) (A := A) (C := C_ov) (hmeas := hA) (hC := hbound)).trans ?_)
  rw [mul_comm]
  gcongr
  exact Set.iUnion₂_subset hAsub

end boundedOverlap

end Kakeya

end
