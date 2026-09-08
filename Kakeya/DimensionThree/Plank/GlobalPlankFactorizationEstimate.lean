/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform.PerScale
public import Kakeya.DimensionThree.Plank.PlankFactorizationEstimate
public import Kakeya.DimensionThree.Plank.InnerConflictDegree
public import Kakeya.DimensionThree.Plank.InnerMultiplicityTransport
public import Kakeya.DimensionThree.Plank.InnerEDAssembly
public import Kakeya.DimensionThree.Plank.Section6PartBCoarseParent
public import Kakeya.DimensionThree.Plank.Section6PartBProp51
public import Kakeya.DimensionThree.Plank.FibreFullnessSelection

/-!
# GWZ Proposition 6.6(B): global plank factorisation

This module contains the global half of GWZ Proposition 6.6. The local Part (A), shared
real-power bookkeeping, and master-scale interfaces live in `PlankFactorizationEstimate.lean`.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal Classical

noncomputable section

namespace Kakeya

/-- The outer family and the raw Proposition 5.1 data used by the global factorisation assembly. -/
structure Section6PartBData.OuterPackage
    {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {κ : Type*} {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
    {m Cfib CF C₀ : ℝ≥0} (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀)
    (Cprop : ℝ≥0) (ηₒ : ℝ) : Prop where
  outerSet_nonempty : D.fineOutput.outerSet.Nonempty
  outerSet_subset : D.fineOutput.outerSet ⊆ D.factor.cells
  outerPlanks_eq_repr : ∀ x, (D.outerPlanks x).toPrism3D = D.factor.repr x
  outerPlanks_window : ∀ j ∈ D.fineOutput.outerSet,
    ((D.outerPlanks j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      Metric.closedBall 0 (plankWindowRadius : ℝ)
  outer_fullness : δ ^ ηₒ ≤ ShadedBody.fullness D.fineOutput.outerSet
    (fun j => (D.outerPlanks j).toShadedBody)
  outer_katzTao : IsKatzTao D.fineOutput.outerSet
    (fun j => (D.outerPlanks j).toConvexSpaceBody) ((δ : ENNReal) ^ (-ηₒ))
  innerSet_eq : D.fineOutput.innerSet =
    ({i ∈ q | D.cellOfFine i ∈ D.fineOutput.outerSet} : Finset ι)
  innerBody_carrier : ∀ i ∈ q,
    (D.fineOutput.innerBody i).toConvexSpaceBody = (T i).toConvexSpaceBody
  refinement : ShadedBody.IsCRefinement D.fineOutput.innerSet D.fineOutput.innerBody q
    (fun i => (T i).toShadedBody) Cprop⁻¹
  multiplicity_split : ∀ x ∈ D.fineOutput.outerSet,
    ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
      (Cprop : ENNReal) *
        ShadedBody.multiplicity D.fineOutput.outerSet
          (fun y => (D.outerPlanks y).toShadedBody) *
        ShadedBody.multiplicity (D.fineOutput.fiber x) D.fineOutput.innerBody
  fiber_card_comparable : ∀ x ∈ D.fineOutput.outerSet, ∀ y ∈ D.fineOutput.outerSet,
    ((D.fineOutput.fiber x).card : ℝ≥0) ≤
      Cprop * ((D.fineOutput.fiber y).card : ℝ≥0)
  shade_subset : ∀ i ∈ D.fineOutput.innerSet,
    (D.fineOutput.innerBody i).shade ⊆ (D.outerPlanks (D.cellOfFine i)).shade

/-- **The single smallness threshold of Proposition 6.6(B).**

The Part-(B) assembly needs `δ` small for four independent reasons, and it must not scatter four
hypotheses through the public statement.  This lemma intersects them into one `s₀ > 0` consumed as
`δ ≤ s₀ · a`:

* `δ ≤ a₀ · b`, the inner-normalisation threshold of
  `Kakeya.innerFamilySlabNonconcentration` — obtained from `δ ≤ s₀ · a ≤ a₀ · a ≤ a₀ · b` using
  `a ≤ b`;
* `(δ : ℝ) ≤ δconf`, the threshold produced by
  `Kakeya.exists_inner_plank_conflict_degree_bound` — obtained from `a ≤ 1`;
* `Cs ≤ δ ^ (-gap)`, the absorption of the fixed constants (the normalisation constant `Cnorm` and
  the weighted-extraction loss `d + 1`) into the exponent gap `gap = ηᵢ - η > 0`, via
  `Kakeya.exists_threshold_le_rpow_neg`.

All three conclusions are drawn from the *same* `δ ≤ s₀ · a`, which is why the scale relations
`a ≤ b ≤ 1` are hypotheses here: they are exactly what lets one threshold do the work of three. -/
theorem exists_partB_smallness_threshold
    (Cs : ℝ≥0) (hCs : 1 ≤ Cs) {gap : ℝ} (hgap : 0 < gap)
    (a₀ : ℝ≥0) (ha₀ : 0 < a₀) (δconf : ℝ) (hδconf : 0 < δconf) :
    ∃ s₀ : ℝ≥0, 0 < s₀ ∧
      ∀ {δ a b : ℝ≥0}, 0 < δ → a ≤ b → b ≤ 1 → δ ≤ s₀ * a →
        δ ≤ a₀ * b ∧ (δ : ℝ) ≤ δconf ∧ Cs ≤ δ ^ (-gap) := by
  obtain ⟨δ₀C, hδ₀Cpos, hδ₀C⟩ := exists_threshold_le_rpow_neg Cs hCs hgap
  set s₀ : ℝ≥0 := min a₀ (min (Real.toNNReal δconf) δ₀C) with hs₀_def
  have hconf0 : 0 < Real.toNNReal δconf := (Real.toNNReal_pos (r := δconf)).mpr hδconf
  have hs₀pos : 0 < s₀ := by
    rw [hs₀_def]
    exact lt_min ha₀ (lt_min hconf0 hδ₀Cpos)
  refine ⟨s₀, hs₀pos, ?_⟩
  intro δ a b hδ0 hab hb1 hsm
  have ha1 : a ≤ 1 := le_trans hab hb1
  have hs₀_le_a₀ : s₀ ≤ a₀ := by
    rw [hs₀_def]
    exact min_le_left _ _
  have hs₀_le_conf : s₀ ≤ Real.toNNReal δconf := by
    rw [hs₀_def]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hs₀_le_δ₀C : s₀ ≤ δ₀C := by
    rw [hs₀_def]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδs₀ : δ ≤ s₀ := by
    calc
      δ ≤ s₀ * a := hsm
      _ ≤ s₀ * 1 := by gcongr
      _ = s₀ := by rw [mul_one]
  refine ⟨?_, ?_, ?_⟩
  · calc
      δ ≤ s₀ * a := hsm
      _ ≤ a₀ * a := by gcongr
      _ ≤ a₀ * b := by gcongr
  · calc
      (δ : ℝ) ≤ (Real.toNNReal δconf : ℝ) :=
        NNReal.coe_le_coe.mpr (le_trans hδs₀ hs₀_le_conf)
      _ = δconf := Real.coe_toNNReal δconf hδconf.le
  · exact hδ₀C δ hδ0 (le_trans hδs₀ hs₀_le_δ₀C)

/-! ### The outer clauses of Proposition 6.6(B) -/

/-- **Outer fullness at the master scale.**

GWZ Proposition 5.1 item 2, as re-stated for Part (B) by `Kakeya.Section6PartBData.Remark53Prop51`,
is *quadratic*: `λ(𝒲, Y_𝒲) ≥ (rc · C)⁻¹ · λ(𝒯, Y)²`, `rc = Kakeya.remark53Const Cfib CF`.  Feeding
`δ ^ η ≤ λ(𝒯, Y)` gives `δ ^ (2η)` upstairs, and `rc ≤ coarseTubeVolumeRatio · δ ^ (-3η)` because
`Cfib, CF ≤ δ ^ (-η)`.  So the exponent budget needed is `5η ≤ ηₒ`, and the only genuinely absolute
constant left over is `coarseTubeVolumeRatio · C`, absorbed by `habs`. -/
theorem partB_outer_fullness
    {ηₒ η : ℝ} (hη : 0 < η) (h5η : 5 * η ≤ ηₒ)
    {ι : Type*} {q : Finset ι} {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hfull : (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody))
    {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {κ : Type*} {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {m Cfib CF C₀ : ℝ≥0}
    (hCF : CF ≤ δ ^ (-η)) (hCfib : Cfib ≤ δ ^ (-η))
    (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀)
    {Cprop : ℝ≥0} (hCprop : 1 ≤ Cprop) (hRem53 : D.Remark53Prop51 Cprop)
    (habs : coarseTubeVolumeRatio * Cprop
      ≤ δ ^ (-(ηₒ - 5 * η))) :
    (δ : ℝ≥0) ^ ηₒ
      ≤ ShadedBody.fullness D.fineOutput.outerSet
          (fun j => (D.outerPlanks j).toShadedBody) := by
  let rc : ℝ≥0 := remark53Const Cfib CF
  let C : ℝ≥0 := Cprop
  let full := ShadedBody.fullness q (fun i => (T i).toShadedBody)
  let fullOut := ShadedBody.fullness D.fineOutput.outerSet
    (fun j => (D.outerPlanks j).toShadedBody)
  have hδnz : δ ≠ 0 := ne_of_gt hδ0
  have hrcnz : rc ≠ 0 := by
    have hone : 1 ≤ rc := one_le_remark53Const D.decomp.one_le_Cfib D.factor.one_le_CF
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hone)
  have hCnz : C ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hCprop)
  have hrcC : rc * C ≠ 0 := mul_ne_zero hrcnz hCnz
  have hpow2 : (δ ^ (-η)) ^ 2 * δ ^ (-η) = δ ^ (-(3 * η)) := by
    rw [pow_two]
    rw [← NNReal.rpow_add hδnz]
    rw [← NNReal.rpow_add hδnz]
    congr
    ring
  have hStep1 : rc ≤ coarseTubeVolumeRatio * δ ^ (-(3 * η)) := by
    simp only [rc, remark53Const]
    calc
      Cfib ^ 2 * coarseTubeVolumeRatio * CF
          ≤ (δ ^ (-η)) ^ 2 * coarseTubeVolumeRatio * CF := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hCfib 2)
            (by positivity)) (by positivity)
      _ ≤ (δ ^ (-η)) ^ 2 * coarseTubeVolumeRatio * δ ^ (-η) := by
        exact mul_le_mul_of_nonneg_left hCF (by positivity)
      _ = coarseTubeVolumeRatio * ((δ ^ (-η)) ^ 2 * δ ^ (-η)) := by ring
      _ = coarseTubeVolumeRatio * (δ ^ (-(3 * η))) := by rw [hpow2]
  have hrcC_le : rc * C ≤ δ ^ (-(ηₒ - 5 * η)) * δ ^ (-(3 * η)) := by
    calc
      rc * C ≤ (coarseTubeVolumeRatio * δ ^ (-(3 * η))) * C := by
        exact mul_le_mul_of_nonneg_right hStep1 (by positivity)
      _ = (coarseTubeVolumeRatio * C) * δ ^ (-(3 * η)) := by ring
      _ ≤ δ ^ (-(ηₒ - 5 * η)) * δ ^ (-(3 * η)) := by
        exact mul_le_mul_of_nonneg_right habs (by positivity)
  have hprod : (rc * C) * δ ^ ηₒ ≤ (δ ^ η) ^ 2 := by
    calc
      (rc * C) * δ ^ ηₒ
          ≤ δ ^ (-(ηₒ - 5 * η)) * δ ^ (-(3 * η)) * δ ^ ηₒ := by
        exact mul_le_mul' hrcC_le le_rfl
      _ = δ ^ (-(ηₒ - 5 * η) + (-(3 * η)) + ηₒ) := by
        rw [← NNReal.rpow_add hδnz]
        rw [← NNReal.rpow_add hδnz]
      _ = δ ^ (2 * η) := by congr; ring
      _ = δ ^ (η * 2) := by rw [show (2 : ℝ) * η = η * 2 by ring]
      _ = (δ ^ η) ^ (2 : ℝ) := by rw [NNReal.rpow_mul]
      _ = (δ ^ η) ^ 2 := by simp
  have hle1 : (δ : ℝ≥0) ^ ηₒ ≤ (rc * C)⁻¹ * (δ ^ η) ^ 2 := by
    calc
      (δ : ℝ≥0) ^ ηₒ = (rc * C)⁻¹ * ((rc * C) * δ ^ ηₒ) := by
        rw [← mul_assoc, inv_mul_cancel₀ hrcC, one_mul]
      _ ≤ (rc * C)⁻¹ * (δ ^ η) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hprod (by positivity)
  have hle2 : (rc * C)⁻¹ * (δ ^ η) ^ 2 ≤ (rc * C)⁻¹ * full ^ 2 := by
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by simpa [full] using hfull) 2) (by positivity)
  have hfinal : (rc * C)⁻¹ * full ^ 2 ≤ fullOut := by
    have hfullness' : (rc : ENNReal)⁻¹ * (C : ENNReal)⁻¹ * (full : ENNReal) ^ 2
        ≤ (fullOut : ENNReal) := by
      simpa only [rc, C, full, fullOut, mul_assoc] using hRem53.fullness
    have hdesc₀ : (rc⁻¹ : ℝ≥0) * C⁻¹ * full ^ 2 ≤ fullOut := by
      exact_mod_cast hfullness'
    simpa only [mul_inv, mul_assoc] using hdesc₀
  exact le_trans hle1 (le_trans hle2 hfinal)

/-- **Outer Katz--Tao at the master scale.**

`Kakeya.Section6PartBFactorisation.isKatzTao_repr_of_subset` gives the representative planks of the
selected cells the Katz--Tao constant `CF · C₀`, and the outer planks *are* those representatives
(`Kakeya.Section6PartBData.carrier_outerPlanks`).  Both factors are `≤ δ ^ (-η)` by hypothesis, so
`2η ≤ ηₒ` suffices; no absolute constant is left over. -/
theorem partB_outer_katzTao
    {ηₒ η : ℝ} (hη : 0 < η) (h2η : 2 * η ≤ ηₒ)
    {ι : Type*} {q : Finset ι} {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (hρ0 : 0 < ρ)
    {κ : Type*} {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {m Cfib CF C₀ : ℝ≥0}
    (hCF : CF ≤ δ ^ (-η)) (hC₀ : C₀ ≤ δ ^ (-η))
    (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀)
    {Cprop : ℝ≥0} (hRem53 : D.Remark53Prop51 Cprop)
    (hmult : 0 < ShadedBody.multiplicity q (fun i => (T i).toShadedBody)) :
    IsKatzTao D.fineOutput.outerSet (fun j => (D.outerPlanks j).toConvexSpaceBody)
      ((δ : ENNReal) ^ (-ηₒ)) := by
  have hKT : ConvexSpaceBody.IsKatzTao D.fineOutput.outerSet
      (fun x => (D.factor.repr x).toConvexSpaceBody) ((CF * C₀ : ℝ≥0) : ENNReal) :=
    Section6PartBFactorisation.isKatzTao_repr_of_subset D.factor hρ0 hRem53.outerSet_subset
      (fun x hx => D.coarseFibre_nonempty_of_mem_outerSet hRem53 hmult hx)
  have hconst : ((CF * C₀ : ℝ≥0) : ENNReal) ≤ (δ : ENNReal) ^ (-ηₒ) := by
    have hδne : δ ≠ 0 := ne_of_gt hδ0
    have hmul : CF * C₀ ≤ δ ^ (-η) * δ ^ (-η) := by
      gcongr
    have hpow : δ ^ (-η) * δ ^ (-η) = δ ^ (-(2 * η)) := by
      rw [← NNReal.rpow_add hδne]
      congr 1
      ring
    have hle : -ηₒ ≤ -(2 * η) := by linarith
    have hmono : δ ^ (-(2 * η)) ≤ δ ^ (-ηₒ) := by
      exact NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hle
    have hnn : (CF * C₀ : ℝ≥0) ≤ δ ^ (-ηₒ) := by
      calc
        CF * C₀ ≤ δ ^ (-η) * δ ^ (-η) := hmul
        _ = δ ^ (-(2 * η)) := hpow
        _ ≤ δ ^ (-ηₒ) := hmono
    calc
      ((CF * C₀ : ℝ≥0) : ENNReal) ≤ ((δ ^ (-ηₒ) : ℝ≥0) : ENNReal) :=
        ENNReal.coe_le_coe.mpr hnn
      _ = (δ : ENNReal) ^ (-ηₒ) := by
        rw [ENNReal.coe_rpow_of_ne_zero hδne]
  exact ConvexSpaceBody.IsKatzTao.mono hKT hconst

/-- **The outer Proposition-5.1 package of 6.6(B), in one call.**

GWZ Proposition 5.1 (through `Kakeya.Section6PartBData.Remark53Prop51`) is invoked here and nowhere
else in the 6.6(B) assembly.  Besides the six clauses `Kakeya.factoringAndMultPropGlobal` exports
about the outer family, this returns the raw Proposition-5.1 data the inner half still needs — the
refined inner set and bodies, the `⪆ 1` refinement, the multiplicity split, the fibre-cardinality
comparability, and the shading containment — so that the split consumes the explicit presentation
package only once.

The exponent budget is the verified one: outer fullness needs `5 · η ≤ ηₒ` (item 2 is *quadratic*,
and `remark53Const Cfib CF ≤ coarseTubeVolumeRatio · δ ^ (-3η)`), while outer Katz--Tao needs only
`2 · η ≤ ηₒ`. -/
theorem partB_outer_package_of_remark53
    {ηₒ η : ℝ} (hη : 0 < η) (h5η : 5 * η ≤ ηₒ) (h2η : 2 * η ≤ ηₒ)
    {ι : Type*} {q : Finset ι} {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hfull : (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody))
    {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (hρ0 : 0 < ρ)
    {κ : Type*} {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {m Cfib CF C₀ : ℝ≥0}
    (hCF : CF ≤ δ ^ (-η)) (hCfib : Cfib ≤ δ ^ (-η)) (hC₀ : C₀ ≤ δ ^ (-η))
    (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀)
    {Cprop : ℝ≥0} (hCprop : 1 ≤ Cprop) (hRem53 : D.Remark53Prop51 Cprop)
    (hmult : 0 < ShadedBody.multiplicity q (fun i => (T i).toShadedBody))
    (habs : coarseTubeVolumeRatio * Cprop
      ≤ δ ^ (-(ηₒ - 5 * η))) :
    D.OuterPackage Cprop ηₒ := by
  have hfullpos : 0 < ShadedBody.fullness q (fun i => (T i).toShadedBody) := by
    exact lt_of_lt_of_le (NNReal.rpow_pos hδ0) hfull
  refine {
    outerSet_nonempty := ?_
    outerSet_subset := ?_
    outerPlanks_eq_repr := ?_
    outerPlanks_window := ?_
    outer_fullness := ?_
    outer_katzTao := ?_
    innerSet_eq := ?_
    innerBody_carrier := ?_
    refinement := ?_
    multiplicity_split := ?_
    fiber_card_comparable := ?_
    shade_subset := ?_ }
  · exact D.fineOutput_outerSet_nonempty
      (ne_of_gt (lt_of_lt_of_le (by norm_num) hCprop)) hRem53 hfullpos
  · exact hRem53.outerSet_subset
  · exact fun _ => rfl
  · exact D.outerPlanks_window_of_subset hRem53.outerSet_subset
  · exact partB_outer_fullness hη h5η hδ0 hδ1 hfull hCF hCfib D hCprop hRem53 habs
  · exact partB_outer_katzTao hη h2η hδ0 hδ1 hρ0 hCF hC₀ D hRem53 hmult
  · exact hRem53.innerSet_eq
  · exact hRem53.innerBody_carrier
  · exact hRem53.refinement
  · exact hRem53.split
  · exact hRem53.fiber_card_comparable
  · exact hRem53.shade_subset

/-! ### The inner block of Proposition 6.6(B) -/

/-- **The essentially distinct inner plank family of Proposition 6.6(B).**

The whole inner pipeline in one step: normalise the fine tubes inside the outer plank
(`Kakeya.exists_inner_family_of_partB`, whose coarse container is already discharged), bound the
conflict degree of the normalised planks (`Kakeya.exists_inner_plank_conflict_degree_bound`), extract
a pairwise essentially distinct subfamily at the weighted loss `d + 1`
(`Kakeya.exists_inner_ED_factorisation_package`), and transport the multiplicity exactly
(`Kakeya.inner_multiplicity_transport`, constant `1`, because the shade is the exact affine image).

The losses are kept explicit and un-absorbed: `Cnorm` on the carrier-sensitive quantities (fullness,
maximal density) and `d + 1` on the extraction-sensitive ones (fullness, cardinality, slab count,
multiplicity).  Absorbing them into `δ`-powers is the caller's job, through
`Kakeya.exists_partB_smallness_threshold`.

**Quantifier order, and the un-absorbed slab constant.**  The dependency chain is
`kap → Cnorm, Cvol, d, δ₀ → configuration`.  `Cnorm` depends on `kap` alone
(`Kakeya.innerShadedPlankFamily`), `Cvol` on `kap` and `cfac`
(`Kakeya.exists_coarse_container_of_guards`), and the conflict degree `d` and threshold `δ₀` on
`kap` alone (`Kakeya.exists_inner_plank_conflict_degree_bound`).  Nothing here depends on `Cfib`,
`CF`, or any exponent, so Proposition 6.6(B) can fix `Csplit = C · (d + 1)` and `Cinner = Cnorm`
before `ηₒ`, `ηᵢ`, `b₀ₒ`, `b₀ᵢ`.

The slab count is reported with its raw constant `(d + 1) · Cfib² · innerCoarseTubeVolumeRatio ·
CF · Cvol`.  It is deliberately *not* absorbed into a power of `a'` here: the absorption threshold
would depend on `Cfib` and `CF`, which the caller does not have when it must fix `s₀`.  The caller
absorbs it into `δ ^ (-ηᵢ)` instead, using `Cfib, CF ≤ δ ^ (-η)` with `η` small compared to `ηᵢ`. -/
theorem exists_inner_ED_family_of_partB {kap : ℝ} (hkap : 0 < kap)
    (cfac : ℝ≥0) (hcfac : 0 < cfac) :
    ∃ (Cnorm Cvol : ℝ≥0) (d : ℕ) (δ₀ : ℝ),
      1 ≤ Cnorm ∧ 1 ≤ Cvol ∧ 0 < d ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type*} [DecidableEq ι] {ιr : Type*} [DecidableEq ιr]
        {a b δ ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (ha : 0 < a) (hδ0 : 0 < δ) (hδa : δ ≤ a) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hρa : ρ ≤ a)
        (hδconf : (δ : ℝ) ≤ δ₀)
        (a₀ b₀ᵢ : ℝ≥0) (hsmalla : δ ≤ a₀ * b) (hsmallb : δ ≤ b₀ᵢ * a)
        (W : Plank a b hab hb1) (q : Finset ι) (r : Finset ιr)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (R : ιr → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF : ℝ≥0)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0)
        (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))),
        0 < J →
        Plank.IsPlankNormalisation W f kap g →
        (∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E) →
        f '' (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 1 →
        (∀ x ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))), ‖f x - f W.center‖ ≤ 1) →
        cfac ≤ J * (a * b) →
        (∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (q : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct
            ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        ∀ (data : CoarseParentSystem q r T R W Cfib CF m),
          ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1) (ιj : Type)
            (qj : Finset ιj) (P : ιj → ShadedPlank a' b' ha'b' hb'1),
            0 < a' ∧ δ ≤ a' ∧ b' ≤ b₀ᵢ ∧
            a' / b' = a / b ∧
            ((a' : ENNReal) / (b' : ENNReal) = (a : ENNReal) / (b : ENNReal)) ∧
            (∀ i ∈ qj, ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
              ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
            (qj : Set ιj).Pairwise
              (fun i j => _root_.IsEssentiallyDistinct
                ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
                ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
            q.card ≤ (d + 1) * qj.card ∧ qj.card ≤ q.card ∧
            ShadedBody.fullness q (fun i => (T i).toShadedBody)
              ≤ Cnorm * ((d : ℝ≥0) + 1)
                * ShadedBody.fullness qj (fun i => (P i).toShadedBody) ∧
            maxDensity qj (fun i => (P i).toConvexSpaceBody)
              ≤ (Cnorm : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) ∧
            (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a' / b' ≤ φ →
                ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
                ((Plank.inWideSlabFamily qj (fun i => (P i).toPrism3D) S).card : ℝ≥0)
                  ≤ ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol))
                      * φ ^ (1 : ℝ) * (qj.card : ℝ≥0)) ∧
            ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
              ≤ ((d : ENNReal) + 1)
                * ShadedBody.multiplicity qj (fun i => (P i).toShadedBody) := by
  classical
  obtain ⟨Cnorm, Cvol, hCnorm, hCvol, hinner⟩ := exists_inner_family_of_partB kap hkap cfac hcfac
  obtain ⟨d, hdpos, δ₀, hδ₀pos, hδ₀le, hdeg⟩ :=
    exists_inner_plank_conflict_degree_bound hkap
  refine ⟨Cnorm, Cvol, d, δ₀, hCnorm, hCvol, hdpos, hδ₀pos, hδ₀le, ?_⟩
  intro ι _ ιr _ a b δ ρ hab hb1 ha hδ0 hδa hρ0 hρ1 hρa hδconf a₀ b₀ᵢ hsmalla hsmallb
    W q r T R m Cfib CF f J g hJ hnorm hvolf himg hWimg hJab hcarrier hED data
  obtain ⟨a', b', ha'b', hb'1, Pj, ha'def, hb'def, ha'pos, hδa', ha'a₀, hb'b₀, hratioNN,
      hratioENN, hwindow, hfull, hmaxd, hslab, hshade, hcarrimg, halign, hortho⟩ :=
    hinner ha hδ0 hδa hρ0 hρ1 hρa a₀ b₀ᵢ hsmalla hsmallb W q r T R m Cfib CF f J g hJ hnorm hvolf
      himg hWimg hJab hcarrier data
  obtain ⟨F, hF⟩ := Plank.exists_affineEquiv_of_isPlankNormalisation ha W hkap hnorm
  have hJab_deg : J * (a * b) = Real.toNNReal kap ^ 3 :=
    Plank.jacobian_eq ha W hkap hnorm hvolf
  have hvolfF : ∀ E : Set (EuclideanSpace ℝ (Fin 3)),
      volume ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E) =
        (J : ENNReal) * volume E := by
    intro E
    have himg : (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E =
        (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' E :=
      congrArg (fun m : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) => m '' E)
        (funext hF)
    rw [himg]
    exact hvolf E
  have halignlin : ∀ i ∈ q, (Pj i).basis 2 =
      (‖f.linear (T i).direction‖)⁻¹ • (f.linear (T i).direction) := by
    intro i hi
    exact align_linear_of_align_sub (T i).toTube (Pj i).toPrism3D (halign i hi)
  have hdeg' : ∀ i ∈ q, edConflictDegree q (fun j => (Pj j).carrier) i ≤ d := by
    intro i hi
    exact hdeg ha hδ0 hδconf (a' := a') (b' := b') (ha'b' := ha'b') (hb'1 := hb'1)
      ha'def hb'def W q (fun i => (T i).toTube) (fun i => (Pj i).toPrism3D)
      f F J g hF hJ hnorm hJab_deg hvolfF hcarrier hcarrimg halignlin hortho hED i hi
  let hpack := exists_inner_ED_factorisation_package q T Pj Cnorm
    (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol)) hCnorm hwindow hfull hmaxd hslab hdeg'
  let ιj := hpack.choose
  let hpack₁ := hpack.choose_spec
  let qj := hpack₁.choose
  let hpack₂ := hpack₁.choose_spec
  let P := hpack₂.choose
  let hpack₃ := hpack₂.choose_spec
  let _source := hpack₃.choose
  let hrest := hpack₃.choose_spec
  have hwin := hrest.2.2.1
  have hEDpair := hrest.2.2.2.1
  have hcard1 := hrest.2.2.2.2.1
  have hcard2 := hrest.2.2.2.2.2.1
  have hfull' := hrest.2.2.2.2.2.2.2.1
  have hmaxd' := hrest.2.2.2.2.2.2.2.2.1
  have hslab' := hrest.2.2.2.2.2.2.2.2.2.1
  have hmult := hrest.2.2.2.2.2.2.2.2.2.2
  have hmt : ShadedBody.multiplicity q (fun i => (Pj i).toShadedBody)
      = ShadedBody.multiplicity q (fun i => (T i).toShadedBody) :=
    inner_multiplicity_transport ha hkap W hnorm q T Pj hshade
  refine ⟨a', b', ha'b', hb'1, ιj, qj, P, ha'pos, hδa', hb'b₀, hratioNN, hratioENN, hwin,
    hEDpair, hcard1, hcard2, hfull', hmaxd', hslab', ?_⟩
  calc
    ShadedBody.multiplicity q (fun i ↦ (T i).toShadedBody) =
        ShadedBody.multiplicity q (fun i ↦ (Pj i).toShadedBody) := hmt.symm
    _ ≤ ((d : ENNReal) + 1) *
        ShadedBody.multiplicity qj (fun i ↦ (P i).toShadedBody) := hmult

namespace Section6PartBData

/-- The selected, normalised inner plank family and all raw bounds used by the Part (B) assembly. -/
structure SelectedInnerPackage
    {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {κ : Type*} {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
    {m Cfib CF C₀ : ℝ≥0} (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀)
    (x₀ : D.factor.Cell) (b₀ᵢ Cnorm Cvol : ℝ≥0) (d : ℕ)
    (innerA innerB : ℝ≥0) (innerA_le_innerB : innerA ≤ innerB)
    (innerB_le_one : innerB ≤ 1) (ιj : Type) (qj : Finset ιj)
    (P : ιj → ShadedPlank innerA innerB innerA_le_innerB innerB_le_one) where
  innerA_pos : 0 < innerA
  delta_le_innerA : δ ≤ innerA
  innerB_le : innerB ≤ b₀ᵢ
  ratio_ennreal : (innerA : ENNReal) / (innerB : ENNReal) =
    (a : ENNReal) / (b : ENNReal)
  ratio_nnreal : innerA / innerB = a / b
  window : ∀ i ∈ qj,
    ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      Metric.closedBall 0 (plankWindowRadius : ℝ)
  pairwise : (qj : Set ιj).Pairwise
    (fun i j => _root_.IsEssentiallyDistinct ((P i).carrier) ((P j).carrier))
  card_le : qj.card ≤ (D.fineOutput.fiber x₀).card
  fullness : ShadedBody.fullness (D.fineOutput.fiber x₀) D.fineOutput.innerBody ≤
    Cnorm * ((d : ℝ≥0) + 1) * ShadedBody.fullness qj (fun i => (P i).toShadedBody)
  maxDensity_le : maxDensity qj (fun i => (P i).toConvexSpaceBody) ≤
    (Cnorm : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody)
  slab : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), innerA / innerB ≤ φ →
    ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
      ((Plank.inWideSlabFamily qj (fun i => (P i).toPrism3D) S).card : ℝ≥0) ≤
        ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol)) *
          φ ^ (1 : ℝ) * (qj.card : ℝ≥0)
  multiplicity : ShadedBody.multiplicity (D.fineOutput.fiber x₀) D.fineOutput.innerBody ≤
    ((d : ENNReal) + 1) * ShadedBody.multiplicity qj (fun i => (P i).toShadedBody)

end Section6PartBData

set_option maxHeartbeats 1000000 in
/-- **The selected inner essentially-distinct package of 6.6(B).**

Helper 2 of the assembly.  It chooses the cell `x₀` once, by mediant fibre selection
(`Kakeya.exists_fibre_fullness_le`), so that the *same* fibre serves the inner fullness and the
inner multiplicity, and runs the whole inner pipeline on it: the affine normalisation
(`Plank.factorNormalisingAffineEquiv`), the cellwise coarse-parent system
(`Kakeya.Section6PartBData.coarseParentSystem`, re-shaded by
`Kakeya.CoarseParentSystem.ofTubeEq`), and `Kakeya.exists_inner_ED_family_of_partB`.

The fine tubes are re-shaded with the *refined* Proposition-5.1 shades,
`T' i = ⟨(T i).toTube, (D.fineOutput.innerBody i).shade⟩`; the coarse-parent data sees only
carriers, so it transports unchanged.

**All losses are returned raw.**  `Cfib`, `CF`, `Cvol` and `d + 1` are not absorbed into powers of
`δ` here; that is the finalising helper's job, and it is the only place where the sub-polynomial
bounds on `Cfib` and `CF` are used.  This helper never mentions `Remark53Prop51`: it consumes only
the raw refinement data that the outer package already extracted. -/
theorem exists_partB_selected_inner_ED_package :
    ∃ (Cnorm Cvol : ℝ≥0) (d : ℕ) (δconf : ℝ),
      1 ≤ Cnorm ∧ 1 ≤ Cvol ∧ 0 < d ∧ 0 < δconf ∧ δconf ≤ 1 ∧
      ∀ {ι : Type*} [DecidableEq ι] {q : Finset ι} {δ : ℝ≥0} (hδ0 : 0 < δ)
        {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
        (hδconf : (δ : ℝ) ≤ δconf)
        (hEDq : (q : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct
            ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3)))))
        {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (ha : 0 < a) (hδa : δ ≤ a) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hρa : ρ ≤ a)
        (a₀ b₀ᵢ : ℝ≥0) (hsmalla : δ ≤ a₀ * b) (hsmallb : δ ≤ b₀ᵢ * a)
        {κ : Type*} {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
        {m Cfib CF C₀ : ℝ≥0}
        (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀)
        (hne : D.fineOutput.outerSet.Nonempty)
        (hinnerSet : D.fineOutput.innerSet
          = ({i ∈ q | D.cellOfFine i ∈ D.fineOutput.outerSet} : Finset ι))
        (hbody : ∀ i ∈ q, (D.fineOutput.innerBody i).toConvexSpaceBody = (T i).toConvexSpaceBody)
        (hcfibne : ∀ x ∈ D.fineOutput.outerSet, (D.factor.coarseFibre x).Nonempty)
        (hsub : D.fineOutput.outerSet ⊆ D.factor.cells)
        (hB0 : (∑ i ∈ D.fineOutput.innerSet,
          volume (D.fineOutput.innerBody i).carrier) ≠ 0)
        (hBtop : (∑ i ∈ D.fineOutput.innerSet,
          volume (D.fineOutput.innerBody i).carrier) ≠ ⊤),
        ∃ x₀ : D.factor.Cell, x₀ ∈ D.fineOutput.outerSet ∧
          ShadedBody.fullness D.fineOutput.innerSet D.fineOutput.innerBody
            ≤ ShadedBody.fullness (D.fineOutput.fiber x₀) D.fineOutput.innerBody ∧
          ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1)
            (ιj : Type) (qj : Finset ιj)
            (P : ιj → ShadedPlank a' b' ha'b' hb'1),
            D.SelectedInnerPackage x₀ b₀ᵢ Cnorm Cvol d a' b' ha'b' hb'1 ιj qj P := by
  classical
  obtain ⟨kap, cfac, Cfac, hkap, hcfac, hCfac, hnormfam⟩ := Plank.factorNormalisingAffineEquiv
  obtain ⟨Cnorm, Cvol, d, δconf, hCnorm, hCvol, hdpos, hδconfpos, hδconfle, hED⟩ :=
    exists_inner_ED_family_of_partB hkap cfac hcfac
  refine ⟨Cnorm, Cvol, d, δconf, hCnorm, hCvol, hdpos, hδconfpos, hδconfle, ?_⟩
  intro ι _ q δ hδ0 T hδconf hEDq a b ρ hab hb1 ha hδa hρ0 hρ1 hρa a₀ b₀ᵢ hsmalla hsmallb
    κ r R m Cfib CF C₀ D hne hinnerSet hbody hcfibne hsub hB0 hBtop
  -- make the decidability instances used by `Section6PartBData.coarseParentSystem` (which is
  -- `open Classical in`) agree with the ones expected by `CoarseParentSystem.ofTubeEq` and `hED`
  letI : DecidableEq ι := Classical.decEq ι
  -- STEP 1: mediant fibre selection
  obtain ⟨x₀, hx₀, hfull₀⟩ :=
    exists_fibre_fullness_le D.fineOutput.innerSet D.fineOutput.innerBody
      D.fineOutput.outerSet D.fineOutput.parent D.fineOutput.parent_mem hne hB0 hBtop
  -- STEP 2: the fibre is the datum's fine fibre
  have hfib : D.fineOutput.fiber x₀ = D.fineFibre x₀ :=
    D.fineOutput_fiber_eq_fineFibre hinnerSet hx₀
  -- the fibre lies in q
  have hfibq : D.fineOutput.fiber x₀ ⊆ q := by
    intro i hi
    have hi' : i ∈ D.fineOutput.innerSet := by
      simpa [ShadedBody.ShadedFactorFamily.fiber] using (Finset.mem_filter.mp hi).1
    rw [hinnerSet] at hi'
    exact (Finset.mem_filter.mp hi').1
  -- STEP 3: re-shaded fine family
  let T' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)) := fun i =>
    if hiq : i ∈ q then
      { toTube := (T i).toTube
        shade := (D.fineOutput.innerBody i).shade
        measurableSet_shade := (D.fineOutput.innerBody i).measurableSet_shade
        shade_subset := by
          intro x hx
          have hcar : (D.fineOutput.innerBody i).carrier = (T i).carrier := by
            simpa using congrArg (fun B : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) => B.carrier)
              (hbody i hiq)
          simpa [hcar] using (D.fineOutput.innerBody i).shade_subset hx }
    else
      T i
  have hT' : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody := by
    intro i
    by_cases hiq : i ∈ q
    · simp [T', hiq]
    · simp [T', hiq]
  have hshade' : ∀ i ∈ q, (T' i).shade = (D.fineOutput.innerBody i).shade := by
    intro i hiq
    simp [T', hiq]
  -- STEP 4: coarse-parent system, re-shaded
  have hx₀cells : x₀ ∈ D.factor.cells := hsub hx₀
  have hcne : (D.factor.coarseFibre x₀).Nonempty := hcfibne x₀ hx₀
  let data0 := D.coarseParentSystem x₀ hx₀cells hcne
  let data := data0.ofTubeEq hT'
  -- STEP 5: normalisation
  obtain ⟨f, J, g, hJ, hnorm, hvolf, himg, hWimg, hJab, hJabU⟩ := hnormfam ha (D.factor.repr x₀)
  -- side conditions for hED
  have hcarrierT' : ∀ i ∈ D.fineFibre x₀,
      ((T' i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ ((D.factor.repr x₀).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro i hi
    have hiq : i ∈ q := D.fineFibre_subset x₀ hi
    simpa [T', hiq] using D.carrier_subset_repr hi
  have hEDfib : (D.fineFibre x₀ : Set ι).Pairwise
      (fun i j => _root_.IsEssentiallyDistinct
        ((T' i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((T' j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
    intro i hi j hj hne
    have hED : _root_.IsEssentiallyDistinct
        ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
      hEDq (D.fineFibre_subset x₀ hi) (D.fineFibre_subset x₀ hj) hne
    have hiq : i ∈ q := D.fineFibre_subset x₀ hi
    have hjq : j ∈ q := D.fineFibre_subset x₀ hj
    simpa [T', hiq, hjq] using hED
  -- STEP 6: run the inner pipeline
  obtain ⟨a', b', ha'b', hb'1, ιj, qj, P, ha'pos, hδa', hb'b₀, hratioNN, hratioENN,
      hwindow, hpair, hcard1, hcard2, hfull, hmaxd, hslab, hmult⟩ :=
    hED ha hδ0 hδa hρ0 hρ1 hρa hδconf a₀ b₀ᵢ hsmalla hsmallb
      (D.factor.repr x₀) (D.fineFibre x₀) (D.factor.coarseFibre x₀) T' R m Cfib CF
      f J g hJ hnorm hvolf himg hWimg hJab hcarrierT' hEDfib data
  -- STEP 7: package
  have hcardfib : qj.card ≤ (D.fineOutput.fiber x₀).card := by
    simpa [hfib] using hcard2
  have hsum_shade : (∑ i ∈ D.fineOutput.fiber x₀, volume (D.fineOutput.innerBody i).shade)
      = (∑ i ∈ D.fineOutput.fiber x₀, volume ((T' i).toShadedBody).shade) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    congr 1
    exact (hshade' i (hfibq hi)).symm
  have hsum_car : (∑ i ∈ D.fineOutput.fiber x₀, volume (D.fineOutput.innerBody i).carrier)
      = (∑ i ∈ D.fineOutput.fiber x₀, volume ((T' i).toShadedBody).carrier) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    congr 1
    have hiq : i ∈ q := hfibq hi
    have hcar : (D.fineOutput.innerBody i).carrier = (T i).carrier := by
      simpa using congrArg (fun B : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) => B.carrier)
        (hbody i hiq)
    simp [T', hiq, hcar]
  have hfull_eq : ShadedBody.fullness (D.fineOutput.fiber x₀) D.fineOutput.innerBody
      = ShadedBody.fullness (D.fineOutput.fiber x₀) (fun i => (T' i).toShadedBody) := by
    rw [← ENNReal.coe_inj, ShadedBody.fullness_def, ShadedBody.fullness_def]
    rw [hsum_shade, hsum_car]
  have hfullgoal : ShadedBody.fullness (D.fineOutput.fiber x₀) D.fineOutput.innerBody
      ≤ Cnorm * ((d : ℝ≥0) + 1)
        * ShadedBody.fullness qj (fun i => (P i).toShadedBody) := by
    calc
      ShadedBody.fullness (D.fineOutput.fiber x₀) D.fineOutput.innerBody
          = ShadedBody.fullness (D.fineOutput.fiber x₀) (fun i => (T' i).toShadedBody) := hfull_eq
      _ = ShadedBody.fullness (D.fineFibre x₀) (fun i => (T' i).toShadedBody) := by
            rw [hfib]
      _ ≤ Cnorm * ((d : ℝ≥0) + 1)
            * ShadedBody.fullness qj (fun i => (P i).toShadedBody) := hfull
  have hmaxdgoal : maxDensity qj (fun i => (P i).toConvexSpaceBody)
      ≤ (Cnorm : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) := by
    calc
      maxDensity qj (fun i => (P i).toConvexSpaceBody)
          ≤ (Cnorm : ENNReal) * maxDensity (D.fineFibre x₀)
              (fun i => (T' i).toConvexSpaceBody) := hmaxd
      _ ≤ (Cnorm : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) := by
            gcongr
            calc
              maxDensity (D.fineFibre x₀) (fun i => (T' i).toConvexSpaceBody)
                  = maxDensity (D.fineFibre x₀) (fun i => (T i).toConvexSpaceBody) := by
                    simp [hT']
              _ ≤ maxDensity q (fun i => (T i).toConvexSpaceBody) := by
                    exact maxDensity_mono (fun i => (T i).toConvexSpaceBody)
                      (D.fineFibre_subset x₀)
  have hmultgoal : ShadedBody.multiplicity (D.fineOutput.fiber x₀) D.fineOutput.innerBody
      ≤ ((d : ENNReal) + 1)
        * ShadedBody.multiplicity qj (fun i => (P i).toShadedBody) := by
    calc
      ShadedBody.multiplicity (D.fineOutput.fiber x₀) D.fineOutput.innerBody
          = ShadedBody.multiplicity (D.fineOutput.fiber x₀) (fun i => (T' i).toShadedBody) := by
            exact multiplicity_eq_of_shade_eqOn (D.fineOutput.fiber x₀) D.fineOutput.innerBody
              (fun i => (T' i).toShadedBody) (by intro i hi; exact (hshade' i (hfibq hi)).symm)
      _ = ShadedBody.multiplicity (D.fineFibre x₀) (fun i => (T' i).toShadedBody) := by
            rw [hfib]
      _ ≤ ((d : ENNReal) + 1)
            * ShadedBody.multiplicity qj (fun i => (P i).toShadedBody) := hmult
  refine ⟨x₀, hx₀, ?_, a', b', ha'b', hb'1, ιj, qj, P, {
    innerA_pos := ha'pos
    delta_le_innerA := hδa'
    innerB_le := hb'b₀
    ratio_ennreal := hratioENN
    ratio_nnreal := hratioNN
    window := hwindow
    pairwise := hpair
    card_le := hcardfib
    fullness := hfullgoal
    maxDensity_le := hmaxdgoal
    slab := hslab
    multiplicity := hmultgoal }⟩
  simpa [ShadedBody.ShadedFactorFamily.fiber] using hfull₀

/-- **Finalising the raw inner bounds of 6.6(B) into the public `δ`-power form.**

Helper 3 of the assembly, and the only place where the sub-polynomial bounds `Cfib, CF ≤ δ ^ (-η)`
are used.  It is purely scalar: it converts the two raw losses produced by the inner package into
the two `δ`-power clauses `Kakeya.factoringAndMultPropGlobal` exports.

* **Slab.**  The raw coefficient is `(d + 1) · Cfib² · innerCoarseTubeVolumeRatio · CF · Cvol`.
  Two factors of `Cfib` and one of `CF` cost `δ ^ (-3η)`; the remaining absolute constant
  `(d + 1) · innerCoarseTubeVolumeRatio · Cvol` is absorbed by `habsSlab` at the fixed threshold.
  With `8 · η ≤ ηᵢ` the two exponents fit inside `ηᵢ`, since `ηᵢ / 2 + 3η ≤ ηᵢ`.
* **Fullness.**  The raw loss is `Cnorm · (d + 1)`, with no `Cfib` or `CF` in it at all; it is
  absorbed across the exponent gap `ηᵢ - η` by `habsFull`.  It is stated as a transfer between two
  abstract fullness values, so that it applies to the selected fibre without carrying the whole
  configuration.

Neither `Csplit`, `Ccard` nor `Cinner` appears here: those are fixed before any of this, and the
maximal-density clause needs no finalising at all (`Cinner = Cnorm`, verbatim). -/
theorem partB_finalize_selected_inner_bounds
    {ηᵢ η : ℝ} (hη : 0 < η) (hηᵢ : 0 < ηᵢ) (h8η : 8 * η ≤ ηᵢ)
    {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {Cprop Cfib CF Cvol Cnorm : ℝ≥0} (hCprop : 1 ≤ Cprop) {d : ℕ}
    (hCfib : Cfib ≤ δ ^ (-η)) (hCF : CF ≤ δ ^ (-η))
    (habsSlab : ((d : ℝ≥0) + 1) * (innerCoarseTubeVolumeRatio * Cvol) ≤ δ ^ (-(ηᵢ / 2)))
    (habsFull : Cprop * (Cnorm * ((d : ℝ≥0) + 1)) ≤ δ ^ (-(ηᵢ - η))) :
    ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol)) ≤ δ ^ (-ηᵢ) ∧
    (∀ F G : ℝ≥0, Cprop⁻¹ * δ ^ η ≤ F →
      F ≤ Cnorm * ((d : ℝ≥0) + 1) * G → δ ^ ηᵢ ≤ G) := by
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hCfib2 : Cfib ^ 2 ≤ (δ ^ (-η)) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hCfib 2
  have hCfibCF : Cfib ^ 2 * CF ≤ (δ ^ (-η)) ^ 2 * δ ^ (-η) := by
    exact mul_le_mul hCfib2 hCF (by positivity) (by positivity)
  have hpow2 : (δ ^ (-η)) ^ 2 * δ ^ (-η) = δ ^ (-(3 * η)) := by
    rw [pow_two]
    rw [← NNReal.rpow_add hδne]
    rw [← NNReal.rpow_add hδne]
    congr
    ring
  have hmain1 : ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol))
      ≤ δ ^ (-(ηᵢ / 2)) * δ ^ (-(3 * η)) := by
    calc
      ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol))
          = (((d : ℝ≥0) + 1) * (innerCoarseTubeVolumeRatio * Cvol)) * (Cfib ^ 2 * CF) := by
        ring
      _ ≤ δ ^ (-(ηᵢ / 2)) * (Cfib ^ 2 * CF) := by
        exact mul_le_mul_of_nonneg_right habsSlab (by positivity)
      _ ≤ δ ^ (-(ηᵢ / 2)) * ((δ ^ (-η)) ^ 2 * δ ^ (-η)) := by
        exact mul_le_mul_of_nonneg_left hCfibCF (by positivity)
      _ = δ ^ (-(ηᵢ / 2)) * δ ^ (-(3 * η)) := by
        rw [hpow2]
  have hle : -ηᵢ ≤ -(ηᵢ / 2) - 3 * η := by
    have hηᵢ_nonneg : 0 ≤ ηᵢ := le_of_lt hηᵢ
    linarith
  have hmono : δ ^ (-(ηᵢ / 2) - 3 * η) ≤ δ ^ (-ηᵢ) := by
    exact NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hle
  have hfinal1 : ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol))
      ≤ δ ^ (-ηᵢ) := by
    calc
      ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol))
          ≤ δ ^ (-(ηᵢ / 2)) * δ ^ (-(3 * η)) := hmain1
      _ = δ ^ (-(ηᵢ / 2) + -(3 * η)) := by
        rw [← NNReal.rpow_add hδne]
      _ = δ ^ (-(ηᵢ / 2) - 3 * η) := by rfl
      _ ≤ δ ^ (-ηᵢ) := hmono
  constructor
  · exact hfinal1
  · intro F G hF hFG
    have hCne : Cprop ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hCprop)
    have hpow_le : δ ^ η ≤ Cprop * F := by
      calc
        δ ^ η = Cprop * (Cprop⁻¹ * δ ^ η) := by
          rw [← mul_assoc, mul_inv_cancel₀ hCne, one_mul]
        _ ≤ Cprop * F := mul_le_mul_of_nonneg_left hF (by positivity)
    have hFG' : Cprop * F ≤ (Cprop * (Cnorm * ((d : ℝ≥0) + 1))) * G := by
      calc
        Cprop * F ≤ Cprop * (Cnorm * ((d : ℝ≥0) + 1) * G) :=
          mul_le_mul_of_nonneg_left hFG (by positivity)
        _ = (Cprop * (Cnorm * ((d : ℝ≥0) + 1))) * G := by ring
    exact rpow_le_of_le_mul_of_loss_le hδ0 habsFull hpow_le hFG'

/-- **The scalar and measure-theoretic side conditions of the 6.6(B) assembly.**

Helper 4.  It creates no geometry: no selected cells, no chosen fibre, no inner plank family.  It
only discharges the three classes of fact that the composition would otherwise have to manufacture
inline.

* **Positivity.**  `0 < μ(𝒯, Y)`, via `ShadedBody.multiplicity_pos_of_fullness_pos`.  This is what
  `Kakeya.partB_outer_package_of_remark53` and
  `Kakeya.Section6PartBData.coarseFibre_nonempty_of_mem_outerSet` need, and it is *not* a
  monotonicity statement: it goes through the total shade mass.
* **Carrier masses.**  Both `≠ 0` and `≠ ⊤`, for the original family and for the refined one.
  Finiteness is compactness.  Nonvanishing comes from the positive fullness for `𝒯`, and for the
  refined family from the mass half of the refinement — no geometric hypothesis is added, and in
  particular no `δ`-tube volume bound is needed.
* **Absorption.**  `Kakeya.exists_partB_smallness_threshold` is invoked **once**, against a single
  majorant `Cs` built with `max` from the three fixed constants that Helpers 1 and 3 ask to absorb:
  `coarseTubeVolumeRatio · C` at gap `ηₒ - 5η`, `(d + 1) · innerCoarseTubeVolumeRatio · Cvol` at
  gap `ηᵢ / 2`, and `Cnorm · (d + 1)` at gap `ηᵢ - η`.  Its single output `Cs ≤ δ ^ (-gap)` with
  `gap` the minimum of the three is then spread back over them.  The exponent budgets of Helpers 1
  and 3 are untouched.

The refined family enters abstractly, as any `ShadedBody.IsCRefinement` of `(q, T)`; the helper
never mentions `Section6PartBData` or `fineOutput`, so it carries no Proposition-5.1 dependency. -/
theorem partB_assembly_side_conditions
    {ηₒ ηᵢ η : ℝ} (hη : 0 < η) (hηᵢ : 0 < ηᵢ)
    (hgapₒ : 5 * η < ηₒ) (hgapᵢ : η < ηᵢ)
    (Cprop Cnorm Cvol : ℝ≥0) (hCprop : 1 ≤ Cprop) (d : ℕ)
    {δconf : ℝ} (hδconfpos : 0 < δconf) :
    ∃ s₀ : ℝ≥0, 0 < s₀ ∧
      ∀ {ι : Type*} {q : Finset ι} {δ : ℝ≥0}, 0 < δ →
        ∀ {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))},
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ {a b : ℝ≥0}, a ≤ b → b ≤ 1 → δ ≤ s₀ * a →
        ∀ {s' : Finset ι} {V' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))},
        ShadedBody.IsCRefinement s' V' q (fun i => (T i).toShadedBody)
          Cprop⁻¹ →
        0 < ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ∧
        (∑ i ∈ q, volume ((T i).toShadedBody).carrier) ≠ 0 ∧
        (∑ i ∈ q, volume ((T i).toShadedBody).carrier) ≠ ⊤ ∧
        (∑ i ∈ s', volume (V' i).carrier) ≠ 0 ∧
        (∑ i ∈ s', volume (V' i).carrier) ≠ ⊤ ∧
        δ ≤ 1 * b ∧ (δ : ℝ) ≤ δconf ∧
        coarseTubeVolumeRatio * Cprop
          ≤ δ ^ (-(ηₒ - 5 * η)) ∧
        ((d : ℝ≥0) + 1) * (innerCoarseTubeVolumeRatio * Cvol) ≤ δ ^ (-(ηᵢ / 2)) ∧
        Cprop * (Cnorm * ((d : ℝ≥0) + 1)) ≤ δ ^ (-(ηᵢ - η)) := by
  classical
  set gap : ℝ := min (ηₒ - 5 * η) (min (ηᵢ / 2) (ηᵢ - η)) with hgap_def
  have hgap : 0 < gap := by
    refine lt_min ?_ (lt_min ?_ ?_) <;> linarith
  let C₁ := coarseTubeVolumeRatio * Cprop
  let C₂ := ((d : ℝ≥0) + 1) * (innerCoarseTubeVolumeRatio * Cvol)
  let C₃ := Cprop * (Cnorm * ((d : ℝ≥0) + 1))
  let Cs := fixedLossMajorant C₁ C₂ C₃
  obtain ⟨s₀, hs₀pos, hs₀⟩ :=
    exists_partB_smallness_threshold Cs (one_le_fixedLossMajorant C₁ C₂ C₃) hgap 1
      (by norm_num : (0 : ℝ≥0) < 1) δconf hδconfpos
  refine ⟨s₀, hs₀pos, ?_⟩
  intro ι q δ hδ0 T hfull a b hab hb1 hδs₀ s' V' hrefine
  obtain ⟨hsmalla, hδconf, habsCs⟩ := hs₀ hδ0 hab hb1 hδs₀
  have hδ1 : δ ≤ 1 := le_trans (by simpa [one_mul] using hsmalla) hb1
  have hδpos_η : 0 < (δ : ℝ≥0) ^ η := NNReal.rpow_pos hδ0
  have hfullpos : 0 < ShadedBody.fullness q (fun i => (T i).toShadedBody) :=
    lt_of_lt_of_le hδpos_η hfull
  have hmult : 0 < ShadedBody.multiplicity q (fun i => (T i).toShadedBody) :=
    ShadedBody.multiplicity_pos_of_fullness_pos q (fun i => (T i).toShadedBody) hfullpos
  have hshadeq : (∑ i ∈ q, volume ((T i).toShadedBody).shade) ≠ 0 :=
    ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos q (fun i => (T i).toShadedBody) hfullpos
  have hcar_q_ne0 : (∑ i ∈ q, volume ((T i).toShadedBody).carrier) ≠ 0 :=
    ShadedBody.sum_volume_carrier_ne_zero_of_sum_shade_ne_zero q (fun i => (T i).toShadedBody) hshadeq
  have hcar_q_neTop : (∑ i ∈ q, volume ((T i).toShadedBody).carrier) ≠ ⊤ :=
    ShadedBody.sum_volume_carrier_ne_top q (fun i => (T i).toShadedBody)
  have hcar_s'_neTop : (∑ i ∈ s', volume (V' i).carrier) ≠ ⊤ :=
    ShadedBody.sum_volume_carrier_ne_top s' V'
  have hcne : Cprop⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (lt_of_lt_of_le (by norm_num) hCprop))
  have hshade'_zero : (∑ i ∈ s', volume (V' i).shade) ≠ 0 :=
    ShadedBody.sum_volume_shade_ne_zero_of_isCRefinement
      (s := q) (V := fun i => (T i).toShadedBody) hrefine hcne hshadeq
  have hcar_s'_ne0 : (∑ i ∈ s', volume (V' i).carrier) ≠ 0 :=
    ShadedBody.sum_volume_carrier_ne_zero_of_sum_shade_ne_zero s' V' hshade'_zero
  have hgap_le1 : gap ≤ ηₒ - 5 * η := min_le_left _ _
  have hgap_le2 : gap ≤ ηᵢ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hgap_le3 : gap ≤ ηᵢ - η := le_trans (min_le_right _ _) (min_le_right _ _)
  have htarget1 : C₁ ≤ δ ^ (-(ηₒ - 5 * η)) :=
    fixedLoss_le_rpow_neg_of_majorant (le_fixedLossMajorant_left C₁ C₂ C₃)
      habsCs hδ0 hδ1 hgap_le1
  have htarget2 : C₂ ≤ δ ^ (-(ηᵢ / 2)) :=
    fixedLoss_le_rpow_neg_of_majorant (le_fixedLossMajorant_middle C₁ C₂ C₃)
      habsCs hδ0 hδ1 hgap_le2
  have htarget3 : C₃ ≤ δ ^ (-(ηᵢ - η)) :=
    fixedLoss_le_rpow_neg_of_majorant (le_fixedLossMajorant_right C₁ C₂ C₃)
      habsCs hδ0 hδ1 hgap_le3
  exact ⟨hmult, hcar_q_ne0, hcar_q_neTop, hcar_s'_ne0, hcar_s'_neTop,
    hsmalla, hδconf, htarget1, htarget2, htarget3⟩

set_option maxHeartbeats 2000000 in
/-- **GWZ Proposition 6.6(B), granted GWZ Remark 5.3.**

`Kakeya.factoringAndMultPropGlobal` with its single external input made explicit.  The proof is the
composition of four helpers and nothing else:

* `Kakeya.partB_assembly_side_conditions` — the scalar and measure side conditions, including the
  single absorption threshold;
* `Kakeya.partB_outer_package_of_remark53` — the outer family and the raw Proposition-5.1 data.
  This is the only invocation of the explicit Section 6 presentation;
* `Kakeya.exists_partB_selected_inner_ED_package` — the fibre selection and the inner pipeline,
  with every loss returned raw;
* `Kakeya.partB_finalize_selected_inner_bounds` — the absorption of those raw losses into
  `δ ^ (-ηᵢ)`.

**Constant order.**  `Cnorm`, `Cvol`, `d`, `δconf` come out of the inner package and depend only on
the absolute normalisation data of `Plank.factorNormalisingAffineEquiv`.  The three public constants
are fixed immediately from them,

`Csplit = factoringAndMultPropCombined.C * (d + 1)`, `Ccard = factoringAndMultPropCombined.C`,
`Cinner = Cnorm`,

before `ηₒ`, `ηᵢ`, `b₀ₒ`, `b₀ᵢ` are introduced and hence before `Cfib` and `CF` exist.  `Ccard`
carries no `d + 1`: the cardinality clause has no `δ`-power to absorb anything into, and the
fibre-comparability constant of `Remark53Prop51.fiber_card_comparable` is already absolute. -/
theorem factoringAndMultPropGlobal_of_remark53 (Cprop : ℝ≥0) (hCprop : 1 ≤ Cprop)
    {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) :
    ∃ Csplit Ccard Cinner : ℝ≥0, 1 ≤ Csplit ∧ 1 ≤ Ccard ∧ 1 ≤ Cinner ∧
      ∀ (ηₒ ηᵢ : ℝ), 0 < ηₒ → 0 < ηᵢ → ∀ (b₀ₒ b₀ᵢ : ℝ≥0), 0 < b₀ₒ → 0 < b₀ᵢ →
      ∃ η > (0 : ℝ), ∃ s₀ > (0 : ℝ≥0),
      ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (q : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1),
          0 < a → b ≤ b₀ₒ → δ ≤ ρ → ρ ≤ a → δ ≤ b₀ᵢ * a → δ ≤ s₀ * a →
          ∀ {κ : Type*} (r : Finset κ)
            (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF C₀ : ℝ≥0),
            C₀ ≤ δ ^ (-η) → CF ≤ δ ^ (-η) → Cfib ≤ δ ^ (-η) →
            ∀ (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀),
            D.Remark53Prop51 Cprop →
            (D.factor.cells : Set D.factor.Cell).Pairwise
              (fun x y => _root_.IsEssentiallyDistinct
                (D.factor.repr x).carrier (D.factor.repr y).carrier) →
            ∃ (ts : Finset D.factor.Cell) (W : D.factor.Cell → ShadedPlank a b hab hb1),
              ts.Nonempty ∧ ts ⊆ D.factor.cells ∧
              ((ts : Set D.factor.Cell).Pairwise
                (fun x y => _root_.IsEssentiallyDistinct (W x).carrier (W y).carrier)) ∧
              (∀ j ∈ ts, (W j).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
              (δ : ℝ≥0) ^ ηₒ ≤ ShadedBody.fullness ts
                (fun j => (W j).toShadedBody) ∧
              IsKatzTao ts (fun j => (W j).toConvexSpaceBody) (δ ^ (-ηₒ)) ∧
              ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1) (ιj : Type)
                (qj : Finset ιj) (Pj : ιj → ShadedPlank a' b' ha'b' hb'1),
                0 < a' ∧ δ ≤ a' ∧ b' ≤ b₀ᵢ ∧
                ((a' : ENNReal) / (b' : ENNReal) = (a : ENNReal) / (b : ENNReal)) ∧
                (∀ i ∈ qj, (Pj i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
                (qj : Set ιj).Pairwise
                  (fun i j => _root_.IsEssentiallyDistinct (Pj i).carrier (Pj j).carrier) ∧
                (δ : ℝ≥0) ^ ηᵢ ≤ ShadedBody.fullness qj
                  (fun i => (Pj i).toShadedBody) ∧
                maxDensity qj (fun i => (Pj i).toConvexSpaceBody)
                  ≤ (Cinner : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) ∧
                (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a' / b' ≤ φ →
                    ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
                    ((Plank.inWideSlabFamily qj (fun i => (Pj i).toPrism3D) S).card : ℝ≥0)
                      ≤ δ ^ (-ηᵢ) * φ ^ (1 : ℝ) * (qj.card : ℝ≥0)) ∧
                ((ts.card : ENNReal) * (qj.card : ENNReal)
                  ≤ (Ccard : ENNReal) * (q.card : ENNReal)) ∧
                ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
                  (Csplit : ENNReal) *
                    ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) *
                    ShadedBody.multiplicity qj (fun i => (Pj i).toShadedBody) := by
  classical
  obtain ⟨Cnorm, Cvol, d, δconf, hCnorm, hCvol, hdpos, hδconfpos, hδconfle, hInner⟩ :=
    exists_partB_selected_inner_ED_package
  refine ⟨Cprop * ((d : ℝ≥0) + 1), Cprop, Cnorm, ?_, hCprop, hCnorm, ?_⟩
  · calc
      1 ≤ Cprop := hCprop
      _ = Cprop * 1 := (mul_one Cprop).symm
      _ ≤ Cprop * ((d : ℝ≥0) + 1) := by gcongr; norm_num
  intro ηₒ ηᵢ hηₒ hηᵢ b₀ₒ b₀ᵢ hb₀ₒ hb₀ᵢ
  set η : ℝ := min (ηₒ / 8) (ηᵢ / 8) with hη_def
  have hη : 0 < η := lt_min (by linarith) (by linarith)
  have hηo : η ≤ ηₒ / 8 := min_le_left _ _
  have hηi : η ≤ ηᵢ / 8 := min_le_right _ _
  have h5η : 5 * η ≤ ηₒ := by linarith
  have h2η : 2 * η ≤ ηₒ := by linarith
  have h8η : 8 * η ≤ ηᵢ := by linarith
  have hgapₒ : 5 * η < ηₒ := by linarith
  have hgapᵢ : η < ηᵢ := by linarith
  obtain ⟨s₀, hs₀pos, hSide⟩ :=
    partB_assembly_side_conditions hη hηᵢ hgapₒ hgapᵢ Cprop Cnorm Cvol hCprop d hδconfpos
  refine ⟨η, hη, s₀, hs₀pos, ?_⟩
  intro ι q δ hδ0 T hwin hEDq hfullq ρ a b hab hb1 ha hb₀ₒ hδρ hρa hδb₀ᵢ hδs₀
  intro κ r R m Cfib CF C₀ hC₀ hCF hCfib D hRem hDED
  have hδa : δ ≤ a := hδρ.trans hρa
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ0 hδρ
  have hρ1 : ρ ≤ 1 := le_trans hρa (le_trans hab hb1)
  have hδ1 : δ ≤ 1 := le_trans hδa (le_trans hab hb1)
  obtain ⟨hmultpos, hB0q, hBtopq, hB0r, hBtopr, hsmalla, hδconf, habsOuter, habsSlab, habsFull⟩ :=
    hSide hδ0 hfullq hab hb1 hδs₀ hRem.refinement
  have hOuter :=
    partB_outer_package_of_remark53 hη h5η h2η hδ0 hδ1 hfullq hρ0 hCF hCfib hC₀ D hCprop
      hRem hmultpos habsOuter
  obtain ⟨x₀, hx₀, hfibsel, a', b', ha'b', hb'1, ιj, qj, P, hSelected⟩ :=
    hInner (δ := δ) hδ0 hδconf hEDq ha hδa hρ0 hρ1 hρa (1 : ℝ≥0) b₀ᵢ hsmalla hδb₀ᵢ D
      hOuter.outerSet_nonempty hOuter.innerSet_eq hOuter.innerBody_carrier
      (fun x hx => D.coarseFibre_nonempty_of_mem_outerSet hRem hmultpos hx)
      hOuter.outerSet_subset hB0r hBtopr
  rcases hSelected with
    ⟨ha'pos, hδa', hb'b₀, hratioENN, hratioNN, hwindowP, hpairP, hcardfib,
      hfullraw, hmaxdP, hslabraw, hmultraw⟩
  obtain ⟨hslabConst, hfullTransfer⟩ :=
    partB_finalize_selected_inner_bounds hη hηᵢ h8η hδ0 hδ1 hCprop hCfib hCF habsSlab
      habsFull
  -- Inner fullness
  have hinnerraw : Cprop⁻¹ * (δ : ℝ≥0) ^ η ≤
      ShadedBody.fullness (D.fineOutput.fiber x₀) D.fineOutput.innerBody := by
    have href := mul_fullness_le_of_isCRefinement hOuter.refinement hB0q hBtopq
    calc
      Cprop⁻¹ * δ ^ η
          ≤ Cprop⁻¹ * ShadedBody.fullness q (fun i => (T i).toShadedBody) := by
            exact mul_le_mul_of_nonneg_left hfullq (by positivity)
      _ ≤ ShadedBody.fullness D.fineOutput.innerSet D.fineOutput.innerBody := href
      _ ≤ ShadedBody.fullness (D.fineOutput.fiber x₀) D.fineOutput.innerBody := hfibsel
  have hfullInner : (δ : ℝ≥0) ^ ηᵢ ≤
      ShadedBody.fullness qj (fun i => (P i).toShadedBody) :=
    hfullTransfer (ShadedBody.fullness (D.fineOutput.fiber x₀) D.fineOutput.innerBody)
      (ShadedBody.fullness qj (fun i => (P i).toShadedBody)) hinnerraw hfullraw
  -- Cardinality
  have hcardTotal : (D.fineOutput.outerSet.card : ENNReal) * (qj.card : ENNReal)
      ≤ (Cprop : ENNReal) * (q.card : ENNReal) := by
    have hcardNN : (D.fineOutput.outerSet.card : ℝ≥0) * (qj.card : ℝ≥0)
        ≤ Cprop * (q.card : ℝ≥0) := by
      calc
        (D.fineOutput.outerSet.card : ℝ≥0) * (qj.card : ℝ≥0)
            ≤ (D.fineOutput.outerSet.card : ℝ≥0) *
                ((D.fineOutput.fiber x₀).card : ℝ≥0) := by
              gcongr
        _ ≤ Cprop * (q.card : ℝ≥0) := by
              exact D.card_mul_card_fiber_le hRem
                (hOuter.fiber_card_comparable x₀ hx₀)
    exact_mod_cast hcardNN
  -- Multiplicity
  have hmultTotal : ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
      ((Cprop * ((d : ℝ≥0) + 1) : ℝ≥0) : ENNReal)
        * ShadedBody.multiplicity D.fineOutput.outerSet (fun j => (D.outerPlanks j).toShadedBody)
        * ShadedBody.multiplicity qj (fun i => (P i).toShadedBody) := by
    calc
      ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
          ≤ (Cprop : ENNReal)
              * ShadedBody.multiplicity D.fineOutput.outerSet
                  (fun j => (D.outerPlanks j).toShadedBody)
              * ShadedBody.multiplicity (D.fineOutput.fiber x₀) D.fineOutput.innerBody :=
            hOuter.multiplicity_split x₀ hx₀
      _ ≤ (Cprop : ENNReal)
              * ShadedBody.multiplicity D.fineOutput.outerSet
                  (fun j => (D.outerPlanks j).toShadedBody)
              * (((d : ENNReal) + 1) *
                  ShadedBody.multiplicity qj (fun i => (P i).toShadedBody)) := by
            gcongr
      _ = ((Cprop * ((d : ℝ≥0) + 1) : ℝ≥0) : ENNReal)
              * ShadedBody.multiplicity D.fineOutput.outerSet
                  (fun j => (D.outerPlanks j).toShadedBody)
              * ShadedBody.multiplicity qj (fun i => (P i).toShadedBody) := by
            push_cast
            ring
  -- Outer essential distinctness, on the family Proposition 5.1 is presented on.
  -- `Kakeya.Section6PartBData.outerPlanks` is the Prop-5.1 shading re-presented on
  -- `D.factor.repr`, so its carrier *is* the representative's
  -- (`Kakeya.Section6PartBData.carrier_outerPlanks`, `rfl`) and the datum's hypothesis
  -- transports verbatim.  See `Kakeya.pairwise_isEssentiallyDistinct_of_toPrism3D_eq` for the
  -- same step stated for a general presentation.
  have hWED : (D.fineOutput.outerSet : Set D.factor.Cell).Pairwise
      (fun x y => _root_.IsEssentiallyDistinct
        (D.outerPlanks x).carrier (D.outerPlanks y).carrier) := by
    intro x hx y hy hxy
    have hx' : x ∈ (D.factor.cells : Set D.factor.Cell) :=
      (Finset.coe_subset.mpr hOuter.outerSet_subset) hx
    have hy' : y ∈ (D.factor.cells : Set D.factor.Cell) :=
      (Finset.coe_subset.mpr hOuter.outerSet_subset) hy
    simpa only [D.carrier_outerPlanks] using hDED hx' hy' hxy
  refine ⟨D.fineOutput.outerSet, D.outerPlanks, hOuter.outerSet_nonempty,
      hOuter.outerSet_subset, hWED, hOuter.outerPlanks_window,
      hOuter.outer_fullness, hOuter.outer_katzTao,
      a', b', ha'b', hb'1, ιj, qj, P, ha'pos, hδa', hb'b₀, hratioENN, hwindowP, hpairP, ?_⟩
  refine ⟨hfullInner, hmaxdP, ?_, hcardTotal, hmultTotal⟩
  intro φ hφR hφ S
  calc
    ((Plank.inWideSlabFamily qj (fun i => (P i).toPrism3D) S).card : ℝ≥0)
        ≤ ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol))
            * φ ^ (1 : ℝ) * (qj.card : ℝ≥0) := hslabraw φ hφR hφ S
    _ ≤ δ ^ (-ηᵢ) * φ ^ (1 : ℝ) * (qj.card : ℝ≥0) := by
          have h1 : ((d : ℝ≥0) + 1) * (Cfib ^ 2 * (innerCoarseTubeVolumeRatio * CF * Cvol))
              * φ ^ (1 : ℝ) ≤ δ ^ (-ηᵢ) * φ ^ (1 : ℝ) := by
            exact mul_le_mul hslabConst le_rfl (by positivity) (by positivity)
          exact mul_le_mul h1 le_rfl (by positivity) (by positivity)

/-- **GWZ Proposition 5.1 (factoring and multiplicity), Lean-facing μ-split for 6.6(B).**
The *global* sibling of `factoringAndMultPropCombined`, now proved from
`Kakeya.factoringAndMultPropGlobal_of_remark53`: here a single
factorisation of the coarse `ρ`-tube family (rather than one factorisation per coarse tube)
is given, and the split is the abstract product of GWZ eq. `boundMuByWandTTW`,

`μ(𝒯, Y) ≤ Csplit · μ(𝒲, Y_𝒲) · μ(𝒯_j, Y')`,

with *no* pre-multiplied inner factor: for 6.6(B) both factors are estimated by GWZ Lemma 6.1
(`plankKTUnified`), the outer one with `γ = 0` (legitimate because the outer plank family is
Katz--Tao, from `Fz.isKatzTao`) and the inner one with `γ = 1`.

The output records, besides the split:
* the outer `a × b × 1` plank family `𝒲 = (W j)_{j ∈ ts}` with compatible shadings, presented on
  the representative planks of the input datum, with master-scale fullness
  `δ^ηₒ ≤ λ(𝒲, Y_𝒲)` (GWZ Prop 5.1 item 2) and `IsKatzTao 𝒲 (δ^(-ηₒ))`;
* the *normalised* inner plank family `(Pj i)_{i ∈ qj}` at the inner scale `a' ≈ δ/b`,
  `b' ≈ δ/a`, of preserved eccentricity `a'/b' = a/b` (blueprint
  `lem:geometryTubeFamilyInsidePlankNormalisation`), with `δ ≤ a'`, its own fullness, the
  max-density transfer `Δ_max(inner) ≤ Cinner · Δ_max(𝒯)` and the `γ = 1` slab non-concentration
  bound supplied by `Plank.slabNonconcentration_of_factorization` /
  `Plank.katzTaoTransverseFactorBound`;
* the two-sided cardinality relation from GWZ Prop 5.1 item 4 (constant inner multiplicity),
  in the form `|ts| · |qj| ≤ Ccard · |q|`.

**The factorisation datum** is `D : Kakeya.Section6PartBData`, not a bare
`Kakeya.GlobalComparableBodyFactorization` together with the existential cover
`∀ i ∈ q, ∃ k ∈ r, T i ≤ R k`.  The bare datum is strictly weaker than what Section 6.6(B) uses,
in three respects, all of them documented in `Kakeya/DimensionThree/Plank/Section6CoarseFactorisation.lean`:
the proof needs a fine-to-coarse assignment *function* with two-sided comparable fibres (field
`decomp`), it needs the coarse fibre over each outer cell to be Frostman *in that cell's
representative plank* (field `factor.coarse_fibre_frostman`, GWZ Remark 5.3 — the *fine* fibres are
not Frostman and must not be assumed so), and it needs the representative `a × b × 1` plank of each
cell as data rather than as an existential (field `factor.repr`).  A
`Kakeya.GlobalComparableBodyFactorization` supplies the geometry and nothing else; the analytic Section-4.2
clauses are added by `Kakeya.Section6PartBFactorisation.ofGlobalPlankFactorization`.  The weak
existential cover is recovered from the datum by `Kakeya.Section6PartBData.exists_parent`, so no
consumer loses anything.

The actual cell body and its representative plank stay strictly separate: no outer body is ever
assumed to *be* a plank.  That hypothesis is unsatisfiable — an outer body is the convex hull of a
union of `ρ`-tubes, a box vertex is an extreme point of such a hull, so it would lie in one of the
(round) tubes, whose inscribed `ρ`-ball cannot reach the corner; comparing two transverse
coordinates gives `√2 ρ ≤ ρ`, i.e. `ρ = 0` (`Kakeya.not_plankFactorization_tubes_of_pos`).  The
scale relation `ρ ≤ a` is not affected by this: it is honest, and is in fact forced by the datum
(`Kakeya.Section6PartBData.rho_le`).

**Essential distinctness.**  Neither plank family's essential
distinctness is claimed out of thin air.  The *outer* clause is what the consumer's `γ = 0`
application of Lemma 6.1 actually needs, and it is now what the conclusion carries:

`(ts : Set D.factor.Cell).Pairwise fun x y => IsEssentiallyDistinct (W x).carrier (W y).carrier`,

with the datum's own pairwise essential distinctness of the *representative* planks as a new
hypothesis.  It is discharged here through
`Kakeya.Section6PartBData.carrier_outerPlanks` — the Proposition-5.1 shading re-presented on
`D.factor.repr` has the representative's carrier, by `rfl` — so nothing is assumed that the previous
form did not already give: `Kakeya.pairwise_isEssentiallyDistinct_of_toPrism3D_eq` is exactly the
implication *old form ⟹ new form*, and every producer of the old form is a producer of this one.

**Why the identification `(W x).toPrism3D = D.factor.repr x` is no longer exported.**  It was the
previous form of this clause, and it is **false for the only outer family Proposition 5.1
constructs**.  Proposition 5.1 returns its outer shading on the `scale`-collar of the cell body,
which does not fit inside an `a × b × 1` plank (the long half-width is pinned at `1` and the collar
reaches `1 + s`), so the shading has to be presented by a homothety: `Kakeya.collarPlank`, whose
prism is `Kakeya.comparablePlankEnvelope.plank …` — a function of the *body* alone, with no
dependence on the representative.  Two cells with equal bodies and distinct representatives satisfy
every hypothesis available at the call site and refute the identification;
`Kakeya.CollarPlankRefute.not_statement_of_universal_presentedPlank_eq_repr` is that refutation, and
`Kakeya.CollarPlankRefute.not_statement_of_universal_presentedPlank_ED` refutes the transport
`ED(reprs) ⟹ ED(presented planks)` on the same witness.  So a presented outer family owes this
clause an extraction, not a transport; the tool for it is
`Kakeya.exists_pairwise_plank_subset_of_isThickeningNonconcentrated`.  The *inner*
clause is kept — the consumers' application of Lemma 6.1 to the inner family needs it — and its
honest source is the new hypothesis that the fine `δ`-tube family is pairwise essentially distinct:
essential distinctness is invariant under invertible affine maps (both sides of
`|U ∩ V| ≤ ½ max(|U|,|V|)` scale by `|det|`), and the inner planks are the images of the fine tubes
under the normalisation of the outer plank.

**The density transfer** carries a constant.  `Δ_max(inner) ≤ Δ_max(𝒯)` with no loss is false after
the affine normalisation of an `a × b × 1` plank to the unit ball: the normalisation is anisotropic,
so shade and body volumes are rescaled by different factors, and only a bounded ratio survives.  The
weakest useful form, `Δ_max(inner) ≤ Cinner · Δ_max(𝒯)` with `1 ≤ Cinner` quantified first (with
`Csplit` and `Ccard`, before all scales and families, so that no consumer can be handed a
`δ`-dependent constant), is what the conclusion claims.  Consumers absorb it into their
sub-polynomial budget exactly as they already absorb `Csplit · Ccard ^ β`.

The inner threshold `b₀ᵢ` is an input and `b' ≤ b₀ᵢ` is part of the conclusion: the leaf absorbs
the reduction to a small inner scale (the degenerate regime `a ≈ δ`, where the inner family is at
scale `≈ 1`). Likewise the two fullness exponents `ηₒ` (outer) and `ηᵢ` (inner) demanded by the two
applications of Lemma 6.1 are inputs, and the leaf *produces* the fine-family exponent `η`: GWZ
Prop 5.1 item 2 only gives `λ(𝒲, Y_𝒲) ≳ C⁻¹ λ(𝒯, Y)²`, so the fine exponent has to be chosen small
relative to the exponents the consumers need, not the other way round.

**All fullness, Katz--Tao and slab clauses are at the master scale `δ`, not at the plank scales `a`
and `a'`.**  The plank-scale forms `a ^ ηₒ ≤ λ(𝒲, Y_𝒲)` and `Δ_max(𝒲) ≤ a ^ (-ηₒ)` are *not*
consequences of Proposition 5.1: item 2 gives `λ(𝒲, Y_𝒲) ⪆ λ(𝒯, Y) ^ 2 ≥ δ ^ (2η)`, and
`δ ^ (2η) ≥ a ^ ηₒ` fails whenever `a` stays above a fixed constant while `δ → 0` (see
`Kakeya.PlankEstimateAtMasterScale` for the computation).  The master-scale forms `δ ^ ηₒ ≤ λ` and
`Δ_max ≤ δ ^ (-ηₒ)` *are*: the first holds as soon as the produced `η` satisfies `2η ≤ ηₒ`, the
second because the datum's outer Katz--Tao constant is `C₀ ≤ δ ^ (-η)`.  The same argument applies
verbatim to the *inner* family: Proposition 5.1 controls the fine family at the master scale, and the
affine normalisation that produces the inner planks cannot manufacture an `a'`-scale bound out of a
`δ`-scale one, so the inner fullness and inner slab clauses are `δ ^ ηᵢ ≤ λ(inner)` and
`|(qj)_S| ≤ δ ^ (-ηᵢ) · φ · |qj|`.  The price is paid by the consumers, which must apply GWZ
Lemma 6.1 in its master-scale readings (`Kakeya.PlankEstimateAtMasterScale` for the Katz--Tao
`γ = 0` outer application, `Kakeya.PlankEstimateAtMasterScaleWithDensity` for the `γ = 1` inner one)
rather than the plank-scale readings currently in the repository.

**The inner scale threshold `δ ≤ b₀ᵢ · a`.**  The inner family lives at scales `a' ≈ δ/b`,
`b' ≈ δ/a`, so the conclusion `b' ≤ b₀ᵢ` — which the inner application of Lemma 6.1 needs, and which
the old contract claimed unconditionally — is simply false when `a ≈ δ`: then `b' ≈ 1`.  The
hypothesis `δ ≤ b₀ᵢ · a` is exactly `b' ≤ b₀ᵢ` read through `b' ≈ δ/a`, and it is the honest price of
that clause.  It is not vacuous and it is not free: the complementary regime `b₀ᵢ · a < δ`, i.e.
`ρ ≈ a ≈ δ`, is the degenerate one where the coarse family is comparable to the fine family, and it
needs its own argument.  Consumers therefore carry the same threshold (`s₀` in
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` and `Kakeya.globalCoarsePlankFallback`).

**Sub-polynomial control of the new constants.**  `C₀`, `CF` and `Cfib` are all required to be at
most `δ ^ (-η)`.  Without that, the Frostman constant of the coarse fibres and the fibre-comparability
constant of the decomposition would enter the split with no bound, and the conclusion — whose only
losses are the absolute constants `Csplit`, `Ccard`, `Cinner` — could not hold.

**What is *not* claimed here.**  `δ ≤ a` is not part of the conclusion: it follows from `δ ≤ ρ ≤ a`.
`0 < a` is now a *hypothesis*: it does follow from `0 < δ ≤ ρ ≤ a`, but the leaf must not present as
output a fact that its own hypotheses already force, and every consumer has it at hand.

**External dependency.**  This is proved from an explicitly supplied
`Kakeya.Section6PartBData.Remark53Prop51` presentation.  The canonical Proposition 5.1
Remark-5.3 theorem for the fine family and actual cell bodies is already available; the explicit
contract adds only the representative-plank and cardinality geometry owned by Section 6.

Everything else in the chain is proved: the inner normalisation of a fine tube family inside an
`a × b × 1` plank (blueprint `lem:geometryTubeFamilyInsidePlankNormalisation`), the `γ = 1` inner
slab non-concentration bound, the essentially-distinct extraction, and the multiplicity transport.
No hidden Proposition 5.1 axiom is used by this assembly. -/
theorem factoringAndMultPropGlobal (Cprop : ℝ≥0) (hCprop : 1 ≤ Cprop)
    {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) :
    ∃ Csplit Ccard Cinner : ℝ≥0, 1 ≤ Csplit ∧ 1 ≤ Ccard ∧ 1 ≤ Cinner ∧
      ∀ (ηₒ ηᵢ : ℝ), 0 < ηₒ → 0 < ηᵢ → ∀ (b₀ₒ b₀ᵢ : ℝ≥0), 0 < b₀ₒ → 0 < b₀ᵢ →
      ∃ η > (0 : ℝ), ∃ s₀ > (0 : ℝ≥0),
      ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (q : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1),
          0 < a → b ≤ b₀ₒ → δ ≤ ρ → ρ ≤ a → δ ≤ b₀ᵢ * a → δ ≤ s₀ * a →
          ∀ {κ : Type*} (r : Finset κ)
            (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF C₀ : ℝ≥0),
            C₀ ≤ δ ^ (-η) → CF ≤ δ ^ (-η) → Cfib ≤ δ ^ (-η) →
            ∀ (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀),
            D.Remark53Prop51 Cprop →
            (D.factor.cells : Set D.factor.Cell).Pairwise
              (fun x y => _root_.IsEssentiallyDistinct
                (D.factor.repr x).carrier (D.factor.repr y).carrier) →
            ∃ (ts : Finset D.factor.Cell) (W : D.factor.Cell → ShadedPlank a b hab hb1),
              ts.Nonempty ∧ ts ⊆ D.factor.cells ∧
              ((ts : Set D.factor.Cell).Pairwise
                (fun x y => _root_.IsEssentiallyDistinct (W x).carrier (W y).carrier)) ∧
              (∀ j ∈ ts, (W j).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
              (δ : ℝ≥0) ^ ηₒ ≤ ShadedBody.fullness ts
                (fun j => (W j).toShadedBody) ∧
              IsKatzTao ts (fun j => (W j).toConvexSpaceBody) (δ ^ (-ηₒ)) ∧
              ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1) (ιj : Type)
                (qj : Finset ιj) (Pj : ιj → ShadedPlank a' b' ha'b' hb'1),
                0 < a' ∧ δ ≤ a' ∧ b' ≤ b₀ᵢ ∧
                ((a' : ENNReal) / (b' : ENNReal) = (a : ENNReal) / (b : ENNReal)) ∧
                (∀ i ∈ qj, (Pj i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
                (qj : Set ιj).Pairwise
                  (fun i j => _root_.IsEssentiallyDistinct (Pj i).carrier (Pj j).carrier) ∧
                (δ : ℝ≥0) ^ ηᵢ ≤ ShadedBody.fullness qj
                  (fun i => (Pj i).toShadedBody) ∧
                maxDensity qj (fun i => (Pj i).toConvexSpaceBody)
                  ≤ (Cinner : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) ∧
                (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a' / b' ≤ φ →
                    ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
                    ((Plank.inWideSlabFamily qj (fun i => (Pj i).toPrism3D) S).card : ℝ≥0)
                      ≤ δ ^ (-ηᵢ) * φ ^ (1 : ℝ) * (qj.card : ℝ≥0)) ∧
                ((ts.card : ENNReal) * (qj.card : ENNReal)
                  ≤ (Ccard : ENNReal) * (q.card : ENNReal)) ∧
                ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
                  (Csplit : ENNReal) *
                    ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) *
                    ShadedBody.multiplicity qj (fun i => (Pj i).toShadedBody) := by
  obtain ⟨Csplit, Ccard, Cinner, hCsplit, hCcard, hCinner, hmain⟩ :=
    factoringAndMultPropGlobal_of_remark53 Cprop hCprop hβpos hβle
  refine ⟨Csplit, Ccard, Cinner, hCsplit, hCcard, hCinner, ?_⟩
  intro ηₒ ηᵢ hηₒ hηᵢ b₀ₒ b₀ᵢ hb₀ₒ hb₀ᵢ
  obtain ⟨η, hη, s₀, hs₀, hcfg⟩ := hmain ηₒ ηᵢ hηₒ hηᵢ b₀ₒ b₀ᵢ hb₀ₒ hb₀ᵢ
  refine ⟨η, hη, s₀, hs₀, ?_⟩
  intro ι q δ hδ0 T hwin hEDq hfullq ρ a b hab hb1 ha hbb₀ hδρ hρa hδb₀ᵢ hδs₀
  intro κ r R m Cfib CF C₀ hC₀ hCF hCfib D hRem hDED
  exact hcfg q hδ0 T hwin hEDq hfullq ρ a b hab hb1 ha hbb₀ hδρ hρa hδb₀ᵢ hδs₀
    r R m Cfib CF C₀ hC₀ hCF hCfib D hRem hDED

-- the master-6.1 application with `γ = 1` unfolds a large dependent type
set_option maxHeartbeats 1000000 in
/-- **Large-`b` fallback for GWZ 6.6(B)** (the `slab1` fallback in the global case; the analogue of
`coarseSlabFallback` for part (A), and our own addition — the blueprint's 6.6(B) proof does not
spell out this regime).  When the outer plank width `b` exceeds the threshold supplied by GWZ
Lemma 6.1, the `γ = 0` *outer* application of that lemma is unavailable; GWZ Lemma 6.9 replaces it.

**Proved**, as a corollary of Lemma 6.9.  The route is the paper's (page 22): the outer family `𝒲` of
`a × b × 1` planks is widened to a family of `a × 1 × 1` *slabs* — which costs only the factor `b`,
bounded below by `b₀` in this regime — and Lemma 6.9 bounds its multiplicity by `Δ_max / λ` up to the
logarithmic typical-angle loss.  With the Katz--Tao and fullness data of the factorisation this is
sub-polynomial (`Kakeya.ShadedPlank.multiplicity_le_of_isKatzTao_of_large`).  The `(a/b) ^ β`
eccentricity factor of the target is *not* produced by Lemma 6.9: it comes, as in the small-`b`
branch, from the `γ = 1` application of Lemma 6.1 to the inner rescaled family, and the two are
combined by `Kakeya.combineGlobalFactorFallback`.

Two features of the signature deserve comment.

* The fullness exponent `η` is now *produced* rather than consumed.  It has to be: the proof calls
  `Kakeya.factoringAndMultPropGlobal`, whose own exponent is only available after the call, and the
  hypotheses `λ(𝒯, Y) ≥ δ ^ η`, `C ≤ δ ^ (-η)`, `C₀ ≤ δ ^ (-η)` must be read at *that* exponent.  The
  caller intersects it with the other exponents, exactly as it already does for the split leaf.
* The outer threshold handed to `Kakeya.factoringAndMultPropGlobal` is `1`, so its `b ≤ b₀ₒ`
  hypothesis is vacuous here — that hypothesis exists only for the outer Lemma 6.1 application, which
  this branch does not make.

**Migration (interface repair of the Proposition 5.1 leaf).**  The factorisation input is now
`Kakeya.Section6PartBData`, the Section-4.2-complete datum, rather than a bare
`Kakeya.GlobalComparableBodyFactorization` together with the existential cover `∀ i ∈ q, ∃ k ∈ r, T i ≤ R k`;
see `Kakeya.factoringAndMultPropGlobal` for why the bare datum is insufficient.  Two further
hypotheses are new: the fine `δ`-tube family is pairwise essentially distinct (the honest source of
the inner plank family's essential distinctness), and the coarse-fibre Frostman and
fibre-comparability constants `CF`, `Cfib` of the datum are sub-polynomial.

**The cell essential distinctness hypothesis is not used on this branch**.  It is
carried only because this branch obtains its split from `Kakeya.factoringAndMultPropGlobal`, whose
outer clause is now the essential distinctness of the outer family itself; the large-`b` outer
estimate `ShadedPlank.multiplicity_le_of_isKatzTao_of_large'` consumes Katz--Tao and fullness
only, and the clause is destructured away.  Its single call site
(`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_masterScaleLemma61`) already has it.  The outer bound is now
taken at the master scale `δ`, since that is where Proposition 5.1 supplies the outer fullness and
Katz--Tao data (`ShadedPlank.multiplicity_le_of_isKatzTao_of_large'` with `d := δ`); this
branch needs no master-scale form of Lemma 6.1, because it does not apply Lemma 6.1 to the outer
family at all.

The factorisation presentation is an explicit hypothesis; this theorem introduces no hidden
Proposition 5.1 dependency. -/
theorem globalCoarsePlankFallback (Cprop : ℝ≥0) (hCprop : 1 ≤ Cprop)
    {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (h61δΔ : PlankEstimateAtMasterScaleWithDensity.{0} β)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ b₀ : ℝ≥0, 0 < b₀ →
      ∃ Ccoarse : ℝ≥0, 1 ≤ Ccoarse ∧ ∃ η > (0 : ℝ), ∃ s₀ > (0 : ℝ≥0),
        ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ)
          (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
          (q : Set ι).Pairwise
            (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
          (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
          ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
            {κ : Type*} (r : Finset κ)
            (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF C₀ : ℝ≥0),
            C₀ ≤ δ ^ (-η) → CF ≤ δ ^ (-η) → Cfib ≤ δ ^ (-η) →
            δ ≤ ρ → ρ ≤ a → δ ≤ s₀ * a →
            ∀ (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀),
            D.Remark53Prop51 Cprop →
            (D.factor.cells : Set D.factor.Cell).Pairwise
              (fun x y => _root_.IsEssentiallyDistinct
                (D.factor.repr x).carrier (D.factor.repr y).carrier) →
            b₀ < b →
            ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
              (Ccoarse : ENNReal) *
                ((δ : ENNReal) ^ (-ε)
                  * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
                  * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β) := by
  intro b₀ hb₀
  have hε3 : 0 < ε / 3 := by positivity
  have hε9 : 0 < ε / 9 := by positivity
  obtain ⟨ηᵢ, hηᵢ, b₀ᵢ, hb₀ᵢ, h61⟩ := h61δΔ (ε / 3) hε3
  obtain ⟨K, hKwin⟩ := ShadedSlab.exists_numAngleWindows_le (ε := ε / 9) hε9
  obtain ⟨Csplit, Ccard, Cinner, hCs1, hCc1, hCi1, hSpFun⟩ :=
    factoringAndMultPropGlobal Cprop hCprop hβpos hβle
  obtain ⟨ηsplit, hηsplit, s₀split, hs₀split, hcfg⟩ :=
    hSpFun (ε / 9) ηᵢ hε9 hηᵢ (1 : ℝ≥0) b₀ᵢ one_pos hb₀ᵢ
  let Cout : ℝ≥0 := 196520 * K * (8 * b₀ ^ 2)⁻¹
  let Comb : ℝ≥0 := Csplit * Cout * Ccard ^ β
  refine ⟨max 1 (Comb * Cinner), le_max_left _ _, ηsplit, hηsplit,
    min b₀ᵢ s₀split, lt_min hb₀ᵢ hs₀split, ?_⟩
  intro ι q δ hδ0 T hball hcross hfull ρ a b hab hb1 κ r R m Cfib CF C₀
    hC₀η hCFη hCfibη hδρ hρa hscale D hRem hDED hbb₀
  have hδa : δ ≤ a := hδρ.trans hρa
  have ha0 : 0 < a := lt_of_lt_of_le hδ0 hδa
  have ha1 : a ≤ 1 := hab.trans hb1
  have hδ1 : δ ≤ 1 := hδa.trans ha1
  have hscaleb : δ ≤ b₀ᵢ * a :=
    le_trans hscale (mul_le_mul_right' (min_le_left b₀ᵢ s₀split) a)
  have hscales : δ ≤ s₀split * a :=
    le_trans hscale (mul_le_mul_right' (min_le_right b₀ᵢ s₀split) a)
  have hrest := hcfg q hδ0 T hball hcross hfull ρ a b hab hb1 ha0 hb1 hδρ hρa
    hscaleb hscales r R m Cfib CF C₀ hC₀η hCFη hCfibη D hRem hDED
  -- the outer essential distinctness is not used on this branch: the large-`b` outer estimate
  -- `ShadedPlank.multiplicity_le_of_isKatzTao_of_large'` needs Katz--Tao and fullness only
  rcases hrest with ⟨ts, W, hts_ne, hts_sub, -, hWb, hWfull, hWKT, a', b', hb', hb'1,
    ιj, qj, Pj, ha'pos, hδa', hb'thr, hratio, hPjball, hPjed, hjfull, hS, hshapextra, hcardle,
    hsplitineq⟩
  have hWbound := ShadedPlank.multiplicity_le_of_isKatzTao_of_large' (ε := ε / 9) (η := ε / 9)
    hb₀ hKwin ts W ha0 hbb₀.le hts_ne hδ0 hδa (by positivity : 0 ≤ ε / 9) hε9 hWKT hWfull
  have hexp : -(ε / 9 + 2 * (ε / 9)) = -(ε / 3) := by ring
  rw [hexp] at hWbound
  let Δ₀ : ENNReal := maxDensity q (fun i => (T i).toConvexSpaceBody)
  have hinner : ShadedBody.multiplicity qj (fun i => (Pj i).toShadedBody) ≤
      (δ : ENNReal) ^ (-(ε / 3))
      * (maxDensity qj (fun i => (Pj i).toConvexSpaceBody)) ^ (1 - β)
      * ((a' : ENNReal) / (b' : ENNReal)) ^ ((1 : ℝ) * β) * (qj.card : ENNReal) ^ β :=
    h61 qj hb' hb'1 Pj hδ0 hδa' hb'thr hPjball hPjed hjfull
      (1 : ℝ) zero_le_one le_rfl hshapextra
  have hTj : ShadedBody.multiplicity qj (fun i => (Pj i).toShadedBody) ≤
      (δ : ENNReal) ^ (-(ε / 3))
      * ((Cinner : ENNReal) * Δ₀) ^ (1 - β)
      * ((a : ENNReal) / (b : ENNReal)) ^ β * (qj.card : ENNReal) ^ β := by
    have h_nonneg : 0 ≤ 1 - β := by linarith
    have hΔle : (maxDensity qj (fun i => (Pj i).toConvexSpaceBody)) ^ (1 - β)
        ≤ ((Cinner : ENNReal) * Δ₀) ^ (1 - β) :=
      ENNReal.rpow_le_rpow hS h_nonneg
    have hmid : (δ : ENNReal) ^ (-(ε / 3))
        * (maxDensity qj (fun i => (Pj i).toConvexSpaceBody)) ^ (1 - β)
        ≤ (δ : ENNReal) ^ (-(ε / 3)) * ((Cinner : ENNReal) * Δ₀) ^ (1 - β) := by
      exact mul_le_mul le_rfl hΔle (by positivity) (by positivity)
    calc
      ShadedBody.multiplicity qj (fun i => (Pj i).toShadedBody) ≤
          (δ : ENNReal) ^ (-(ε / 3))
          * (maxDensity qj (fun i => (Pj i).toConvexSpaceBody)) ^ (1 - β)
          * ((a' : ENNReal) / (b' : ENNReal)) ^ ((1 : ℝ) * β) * (qj.card : ENNReal) ^ β :=
        hinner
      _ ≤ (δ : ENNReal) ^ (-(ε / 3))
          * ((Cinner : ENNReal) * Δ₀) ^ (1 - β)
          * ((a' : ENNReal) / (b' : ENNReal)) ^ ((1 : ℝ) * β) * (qj.card : ENNReal) ^ β := by
        exact mul_le_mul (mul_le_mul hmid le_rfl (by positivity) (by positivity))
            le_rfl (by positivity) (by positivity)
      _ = (δ : ENNReal) ^ (-(ε / 3))
          * ((Cinner : ENNReal) * Δ₀) ^ (1 - β)
          * ((a : ENNReal) / (b : ENNReal)) ^ ((1 : ℝ) * β) * (qj.card : ENNReal) ^ β := by
        rw [hratio]
      _ = (δ : ENNReal) ^ (-(ε / 3))
          * ((Cinner : ENNReal) * Δ₀) ^ (1 - β)
          * ((a : ENNReal) / (b : ENNReal)) ^ β * (qj.card : ENNReal) ^ β := by
        simp [one_mul]
  have hcomb := Kakeya.combineGlobalFactorFallback hβpos hβle hε hδ0 hδ1 hδa
    (Csplit := Csplit) (Ccard := Ccard) (Cout := Cout) hCs1 hCc1
    (Finset.card_ne_zero.mpr hts_ne) hWbound hTj hsplitineq hcardle
  have h_nonneg_1mβ : 0 ≤ 1 - β := by linarith
  have hCinner_rpow : (Cinner : ENNReal) ^ (1 - β) ≤ (Cinner : ENNReal) := by
    calc
      (Cinner : ENNReal) ^ (1 - β) ≤ (Cinner : ENNReal) ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast hCi1) (by linarith : 1 - β ≤ 1)
      _ = (Cinner : ENNReal) := ENNReal.rpow_one _
  have hCinner_mul : ((Cinner : ENNReal) * Δ₀) ^ (1 - β) ≤ (Cinner : ENNReal) * Δ₀ ^ (1 - β) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ h_nonneg_1mβ]
    exact mul_le_mul hCinner_rpow le_rfl (by positivity) (by positivity)
  have hCombC : (Comb : ENNReal) * (Cinner : ENNReal) ≤
      ((max 1 (Comb * Cinner) : ℝ≥0) : ENNReal) := by
    rw [← ENNReal.coe_mul]
    exact_mod_cast (le_max_right (1 : ℝ≥0) (Comb * Cinner))
  refine hcomb.trans ?_
  calc
    (Comb : ENNReal) * ((δ : ENNReal) ^ (-ε) * ((Cinner : ENNReal) * Δ₀) ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β)
      ≤ (Comb : ENNReal) * ((δ : ENNReal) ^ (-ε) * ((Cinner : ENNReal) * Δ₀ ^ (1 - β))
          * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β) := by
        gcongr
    _ = ((Comb : ENNReal) * (Cinner : ENNReal)) * ((δ : ENNReal) ^ (-ε) * Δ₀ ^ (1 - β)
          * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β) := by
        ring
    _ ≤ ((max 1 (Comb * Cinner) : ℝ≥0) : ENNReal) * ((δ : ENNReal) ^ (-ε) * Δ₀ ^ (1 - β)
          * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β) := by
        gcongr


/-- The `γ = 0` slab hypothesis of GWZ Lemma 6.1 is automatic: `θ ^ (0 : ℝ) = 1`, the slab
sub-family is a sub-family, and `1 ≤ a ^ (-η)` for `a ≤ 1`, `0 ≤ η`. This is the precise form of
GWZ Remark 6.2 ("the slab hypothesis is vacuous for `γ = 0`"), and it is what licenses the outer
application of Lemma 6.1 in GWZ Proposition 6.6(B). -/
theorem gammaZeroSlabBound {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*} {η : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hη : 0 ≤ η) (s : Finset ι) (P : ι → Plank a b hab hb1)
    (φ : ℝ≥0) (hφR : φ ≤ Rslab) (S : Prism3D φ Rslab Rslab hφR le_rfl) :
    ((Plank.inWideSlabFamily s P S).card : ℝ≥0) ≤ a ^ (-η) * φ ^ (0 : ℝ) * (s.card : ℝ≥0) := by
  have hcard : ((Plank.inWideSlabFamily s P S).card : ℝ≥0) ≤ (s.card : ℝ≥0) := by
    exact_mod_cast Finset.card_le_card (Plank.inWideSlabFamily_subset (s := s) (V := P) (Sφ := S))
  have h_one : (1 : ℝ≥0) ≤ a ^ (-η) :=
    NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos ha ha1 (by
      linarith)
  calc
    ((Plank.inWideSlabFamily s P S).card : ℝ≥0) ≤ (s.card : ℝ≥0) := hcard
    _ = (1 : ℝ≥0) * (s.card : ℝ≥0) := by simp
    _ = (1 : ℝ≥0) * (1 : ℝ≥0) * (s.card : ℝ≥0) := by simp
    _ ≤ a ^ (-η) * (1 : ℝ≥0) * (s.card : ℝ≥0) := by
      gcongr
    _ = a ^ (-η) * φ ^ (0 : ℝ) * (s.card : ℝ≥0) := by simp

/-- `Kakeya.gammaZeroSlabBound` at the master scale: the `γ = 0` slab hypothesis of the master-scale
reading of GWZ Lemma 6.1 (`Kakeya.PlankEstimateAtMasterScale`) is vacuous for the same reason, and
for any scale `δ ∈ (0, 1]` in place of the plank scale `a`. -/
theorem gammaZeroSlabBoundAtMasterScale {a b δ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
    {η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η) (s : Finset ι) (P : ι → Plank a b hab hb1)
    (φ : ℝ≥0) (hφR : φ ≤ Rslab) (S : Prism3D φ Rslab Rslab hφR le_rfl) :
    ((Plank.inWideSlabFamily s P S).card : ℝ≥0) ≤ δ ^ (-η) * φ ^ (0 : ℝ) * (s.card : ℝ≥0) := by
  have hcard : ((Plank.inWideSlabFamily s P S).card : ℝ≥0) ≤ (s.card : ℝ≥0) := by
    exact_mod_cast Finset.card_le_card (Plank.inWideSlabFamily_subset (s := s) (V := P) (Sφ := S))
  have h_one : (1 : ℝ≥0) ≤ δ ^ (-η) :=
    NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by
      linarith)
  calc
    ((Plank.inWideSlabFamily s P S).card : ℝ≥0) ≤ (s.card : ℝ≥0) := hcard
    _ = (1 : ℝ≥0) * (s.card : ℝ≥0) := by simp
    _ = (1 : ℝ≥0) * (1 : ℝ≥0) * (s.card : ℝ≥0) := by simp
    _ ≤ δ ^ (-η) * (1 : ℝ≥0) * (s.card : ℝ≥0) := by
      gcongr
    _ = δ ^ (-η) * φ ^ (0 : ℝ) * (s.card : ℝ≥0) := by simp

/-- **Essential distinctness transfers to a family presented on given planks.**

A shaded plank family whose underlying planks are `P` inherits pairwise essential distinctness from
`P`, on any subset of the index set where `P` has it.  Essential distinctness sees only the carrier,
and a `Kakeya.ShadedPlank`'s carrier is the carrier of its `toPrism3D`.

This is how the outer family of GWZ Proposition 6.6(B) gets its essential distinctness *when it is
presented on the representatives themselves* (`Kakeya.Section6PartBData.outerPlanks`): not from an
(unavailable) extraction theorem for planks, but from the corresponding hypothesis on the
representative planks of the factorisation datum.

Since steps  it is also the **fidelity pin** for the outer clause of
`Kakeya.factoringAndMultPropGlobal`: that clause used to be the hypothesis `hW` of this lemma and is
now its conclusion, so this lemma *is* the implication old ⟹ new and no producer of the old clause
loses anything.

It does **not** apply to a family presented by a homothety, `Kakeya.collarPlank`: there `hW` is false
(`Kakeya.CollarPlankRefute.not_statement_of_universal_presentedPlank_eq_repr`), and so is the
transport it would be used for
(`Kakeya.CollarPlankRefute.not_statement_of_universal_presentedPlank_ED`). -/
theorem pairwise_isEssentiallyDistinct_of_toPrism3D_eq {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {κ' : Type*} {cells ts : Finset κ'} (hts : ts ⊆ cells)
    (P : κ' → Plank a b hab hb1) (W : κ' → ShadedPlank a b hab hb1)
    (hW : ∀ x, (W x).toPrism3D = P x)
    (hED : (cells : Set κ').Pairwise
      fun x y => _root_.IsEssentiallyDistinct (P x).carrier (P y).carrier) :
    (ts : Set κ').Pairwise
      fun x y => _root_.IsEssentiallyDistinct (W x).carrier (W y).carrier := by
  intro x hx y hy hxy
  have hx' : x ∈ (cells : Set κ') := (Finset.coe_subset.mpr hts) hx
  have hy' : y ∈ (cells : Set κ') := (Finset.coe_subset.mpr hts) hy
  rw [hW x, hW y]
  exact hED hx' hy' hxy

/-- Absorption shape for the two 6.6(B) loss constants: for `Cs, Cc ≥ 1` and `0 ≤ β`,
`Cs · Cc ^ β ≤ (Cs · Cc) ^ (1 + β)`, so a single application of `rpowConstAbsorb` to `Cs · Cc`
with power `1 + β` dominates the product loss. -/
theorem product_rpow_le {β : ℝ} (hβpos : 0 < β) (Cs Cc : ℝ≥0) (hCs : 1 ≤ Cs) (hCc : 1 ≤ Cc) :
    (Cs : ENNReal) * (Cc : ENNReal) ^ β ≤ ((Cs * Cc : ℝ≥0) : ENNReal) ^ ((1 : ℝ) + β) := by
  have hβ_nonneg : 0 ≤ β := le_of_lt hβpos
  have hCs0 : Cs ≠ 0 := (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hCs).ne'
  have hCc0 : Cc ≠ 0 := (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hCc).ne'
  have hCs_enn0 : (Cs : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hCs0
  have hCs_enn_top : (Cs : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCc_enn0 : (Cc : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hCc0
  have hCc_enn_top : (Cc : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h_mul0 : (Cs : ENNReal) * (Cc : ENNReal) ≠ 0 := mul_ne_zero hCs_enn0 hCc_enn0
  have h_mul_top : (Cs : ENNReal) * (Cc : ENNReal) ≠ ⊤ := ENNReal.mul_ne_top hCs_enn_top hCc_enn_top
  have h_base : ((Cs * Cc : ℝ≥0) : ENNReal) = (Cs : ENNReal) * (Cc : ENNReal) := by simp
  rw [h_base]
  calc
    (Cs : ENNReal) * (Cc : ENNReal) ^ β
        = ((Cs : ENNReal) * (Cc : ENNReal) ^ β) * 1 := by simp
    _ ≤ ((Cs : ENNReal) * (Cc : ENNReal) ^ β) * ((Cc : ENNReal) * (Cs : ENNReal) ^ β) := by
      have h_one_le_product : 1 ≤ (Cc : ENNReal) * (Cs : ENNReal) ^ β := by
        have h_one_le_Cc : 1 ≤ (Cc : ENNReal) := by exact_mod_cast hCc
        have h_one_le_Cs_pow : 1 ≤ (Cs : ENNReal) ^ β :=
          ENNReal.one_le_rpow (by exact_mod_cast hCs) hβpos
        calc
          (1 : ENNReal) = (1 : ENNReal) * (1 : ENNReal) := by simp
          _ ≤ (Cc : ENNReal) * (Cs : ENNReal) ^ β :=
            mul_le_mul h_one_le_Cc h_one_le_Cs_pow (by positivity) (by positivity)
      refine mul_le_mul_of_nonneg_left h_one_le_product ?_
      positivity
    _ = ((Cs : ENNReal) * (Cc : ENNReal)) * ((Cs : ENNReal) ^ β * (Cc : ENNReal) ^ β) := by ring
    _ = ((Cs : ENNReal) * (Cc : ENNReal)) * ((Cs : ENNReal) * (Cc : ENNReal)) ^ β := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hβ_nonneg]
    _ = ((Cs : ENNReal) * (Cc : ENNReal)) ^ (1 : ℝ) * ((Cs : ENNReal) * (Cc : ENNReal)) ^ β := by simp
    _ = ((Cs : ENNReal) * (Cc : ENNReal)) ^ ((1 : ℝ) + β) := by
      rw [ENNReal.rpow_add (1 : ℝ) β h_mul0 h_mul_top]
    _ = ((Cs * Cc : ℝ≥0) : ENNReal) ^ ((1 : ℝ) + β) := by simp

set_option maxHeartbeats 1000000 in
theorem combineGlobalFactor {β ε : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) (hε : 0 < ε)
    {δ a b : ℝ≥0} (hδ0 : 0 < δ) {Csplit Ccard : ℝ≥0} (hCs1 : 1 ≤ Csplit) (hCc1 : 1 ≤ Ccard)
    {Δ : ENNReal} {nq nts nj : ℕ} {μqT μW μTj : ENNReal}
    (hW : μW ≤ (δ : ENNReal) ^ (-(ε / 3)) * (nts : ENNReal) ^ β)
    (hTj : μTj ≤ (δ : ENNReal) ^ (-(ε / 3)) * Δ ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ β * (nj : ENNReal) ^ β)
    (hsplit : μqT ≤ (Csplit : ENNReal) * μW * μTj)
    (hcard : (nts : ENNReal) * (nj : ENNReal) ≤ (Ccard : ENNReal) * (nq : ENNReal))
    (hthr : (Csplit : ENNReal) * (Ccard : ENNReal) ^ β ≤ (δ : ENNReal) ^ (-(ε / 3))) :
    μqT ≤ (δ : ENNReal) ^ (-ε) * Δ ^ (1 - β)
      * ((a : ENNReal) / (b : ENNReal)) ^ β * (nq : ENNReal) ^ β := by
  -- Step 1: combine hsplit with hW and hTj
  have hβ_nonneg : 0 ≤ β := by linarith
  have hstep : μqT ≤ (Csplit : ENNReal)
      * ((δ : ENNReal) ^ (-(ε / 3)) * (nts : ENNReal) ^ β)
      * ((δ : ENNReal) ^ (-(ε / 3)) * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β * (nj : ENNReal) ^ β) := by
    calc
      μqT ≤ (Csplit : ENNReal) * μW * μTj := hsplit
      _ ≤ (Csplit : ENNReal) * ((δ : ENNReal) ^ (-(ε / 3)) * (nts : ENNReal) ^ β) * μTj := by
        gcongr
      _ ≤ (Csplit : ENNReal) * ((δ : ENNReal) ^ (-(ε / 3)) * (nts : ENNReal) ^ β)
          * ((δ : ENNReal) ^ (-(ε / 3)) * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β * (nj : ENNReal) ^ β) := by
        gcongr
  -- Step 2: cardinality bound hprod: (nts)^β * (nj)^β ≤ (Ccard)^β * (nq)^β
  have hprod : (nts : ENNReal) ^ β * (nj : ENNReal) ^ β ≤ (Ccard : ENNReal) ^ β * (nq : ENNReal) ^ β := by
    calc
      (nts : ENNReal) ^ β * (nj : ENNReal) ^ β = ((nts : ENNReal) * (nj : ENNReal)) ^ β := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hβ_nonneg]
      _ ≤ ((Ccard : ENNReal) * (nq : ENNReal)) ^ β := ENNReal.rpow_le_rpow hcard hβ_nonneg
      _ = (Ccard : ENNReal) ^ β * (nq : ENNReal) ^ β := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hβ_nonneg]
  -- Step 3: δ power split
  have hδ_nonzero : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδ_not_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsplitδ : (δ : ENNReal) ^ (-ε)
      = (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)) := by
    calc
      (δ : ENNReal) ^ (-ε) = (δ : ENNReal) ^ (-(ε / 3) + (-(ε / 3)) + (-(ε / 3))) := by ring
      _ = ((δ : ENNReal) ^ (-(ε / 3) + (-(ε / 3)))) * (δ : ENNReal) ^ (-(ε / 3)) := by
        rw [ENNReal.rpow_add (-(ε / 3) + (-(ε / 3))) (-(ε / 3)) hδ_nonzero hδ_not_top]
      _ = ((δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3))) * (δ : ENNReal) ^ (-(ε / 3)) := by
        rw [ENNReal.rpow_add (-(ε / 3)) (-(ε / 3)) hδ_nonzero hδ_not_top]
      _ = (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)) := by ring
  -- Step 4: final calc
  set X := (Csplit : ENNReal) * (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3))
    * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β with hX
  calc
    μqT ≤ (Csplit : ENNReal)
        * ((δ : ENNReal) ^ (-(ε / 3)) * (nts : ENNReal) ^ β)
        * ((δ : ENNReal) ^ (-(ε / 3)) * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β * (nj : ENNReal) ^ β) :=
      hstep
    _ = X * ((nts : ENNReal) ^ β * (nj : ENNReal) ^ β) := by
      dsimp [X]
      ring
    _ ≤ X * ((Ccard : ENNReal) ^ β * (nq : ENNReal) ^ β) :=
      mul_le_mul_left' hprod X
    _ = ((Csplit : ENNReal) * (Ccard : ENNReal) ^ β)
        * (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3))
        * (nq : ENNReal) ^ β * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β := by
      dsimp [X]
      ring
    _ ≤ (δ : ENNReal) ^ (-(ε / 3))
        * (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3))
        * (nq : ENNReal) ^ β * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β := by
      gcongr
    _ = ((δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)) * (δ : ENNReal) ^ (-(ε / 3)))
        * (nq : ENNReal) ^ β * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β := by ring
    _ = (δ : ENNReal) ^ (-ε) * (nq : ENNReal) ^ β * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β := by
      rw [hsplitδ]
    _ = (δ : ENNReal) ^ (-ε) * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β * (nq : ENNReal) ^ β := by
      ring

/-- **The 6.6(B) combination, with the inner density loss of GWZ Proposition 5.1.**

`Kakeya.combineGlobalFactor` with the max-density transfer of the Proposition 5.1 leaf weakened from
`Δ_max(inner) ≤ Δ_max(𝒯)` to `Δ_max(inner) ≤ Cinner · Δ_max(𝒯)`, which is all the affine
normalisation of an `a × b × 1` plank can give (see `Kakeya.factoringAndMultPropGlobal`).  The extra
constant is paid for out of the sub-polynomial budget: the two applications of Lemma 6.1 are run at
`ε/6` rather than `ε/3`, and the reserved factor `δ ^ (-ε/2)` absorbs `Cinner` through the threshold
hypothesis `hthrI`, exactly as `hthr` absorbs `Csplit · Ccard ^ β`. -/
theorem combineGlobalFactorWithInnerLoss {β ε : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    {δ a b : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {Csplit Ccard Cinner : ℝ≥0}
    (hCs1 : 1 ≤ Csplit) (hCc1 : 1 ≤ Ccard) (hCi1 : 1 ≤ Cinner)
    {Δ : ENNReal} {nq nts nj : ℕ} {μqT μW μTj : ENNReal}
    (hW : μW ≤ (δ : ENNReal) ^ (-(ε / 6)) * (nts : ENNReal) ^ β)
    (hTj : μTj ≤ (δ : ENNReal) ^ (-(ε / 6)) * ((Cinner : ENNReal) * Δ) ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ β * (nj : ENNReal) ^ β)
    (hsplit : μqT ≤ (Csplit : ENNReal) * μW * μTj)
    (hcard : (nts : ENNReal) * (nj : ENNReal) ≤ (Ccard : ENNReal) * (nq : ENNReal))
    (hthr : (Csplit : ENNReal) * (Ccard : ENNReal) ^ β ≤ (δ : ENNReal) ^ (-(ε / 6)))
    (hthrI : (Cinner : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 2))) :
    μqT ≤ (δ : ENNReal) ^ (-ε) * Δ ^ (1 - β)
      * ((a : ENNReal) / (b : ENNReal)) ^ β * (nq : ENNReal) ^ β := by
  -- Step 1: combine hsplit with hW and hTj
  have hβ_nonneg : 0 ≤ β := by linarith
  have hstep : μqT ≤ (Csplit : ENNReal)
      * ((δ : ENNReal) ^ (-(ε / 6)) * (nts : ENNReal) ^ β)
      * ((δ : ENNReal) ^ (-(ε / 6)) * ((Cinner : ENNReal) * Δ) ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ β * (nj : ENNReal) ^ β) := by
    calc
      μqT ≤ (Csplit : ENNReal) * μW * μTj := hsplit
      _ ≤ (Csplit : ENNReal) * ((δ : ENNReal) ^ (-(ε / 6)) * (nts : ENNReal) ^ β) * μTj := by
        gcongr
      _ ≤ (Csplit : ENNReal) * ((δ : ENNReal) ^ (-(ε / 6)) * (nts : ENNReal) ^ β)
          * ((δ : ENNReal) ^ (-(ε / 6)) * ((Cinner : ENNReal) * Δ) ^ (1 - β)
            * ((a : ENNReal) / (b : ENNReal)) ^ β * (nj : ENNReal) ^ β) := by
        gcongr
  -- Step 2: cardinality bound hprod: (nts)^β * (nj)^β ≤ (Ccard)^β * (nq)^β
  have hprod : (nts : ENNReal) ^ β * (nj : ENNReal) ^ β ≤
      (Ccard : ENNReal) ^ β * (nq : ENNReal) ^ β := by
    calc
      (nts : ENNReal) ^ β * (nj : ENNReal) ^ β = ((nts : ENNReal) * (nj : ENNReal)) ^ β := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hβ_nonneg]
      _ ≤ ((Ccard : ENNReal) * (nq : ENNReal)) ^ β :=
        ENNReal.rpow_le_rpow hcard hβ_nonneg
      _ = (Ccard : ENNReal) ^ β * (nq : ENNReal) ^ β := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hβ_nonneg]
  -- Step 3: the inner-density constant is absorbed through `Cinner ^ (1 - β) ≤ Cinner`
  have h_nonneg_1mβ : 0 ≤ 1 - β := by linarith
  have hCinner_rpow : (Cinner : ENNReal) ^ (1 - β) ≤ (Cinner : ENNReal) := by
    calc
      (Cinner : ENNReal) ^ (1 - β) ≤ (Cinner : ENNReal) ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast hCi1) (by linarith : 1 - β ≤ 1)
      _ = (Cinner : ENNReal) := ENNReal.rpow_one _
  have hCinner_mul_eq : ((Cinner : ENNReal) * Δ) ^ (1 - β)
      = (Cinner : ENNReal) ^ (1 - β) * Δ ^ (1 - β) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ h_nonneg_1mβ]
  -- Step 4: δ-power split: δ^(-ε) = δ^(-(ε/6))^3 * δ^(-(ε/2))
  have hδ_nonzero : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδ_not_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsplitδ : (δ : ENNReal) ^ (-ε)
      = (δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6))
        * (δ : ENNReal) ^ (-(ε / 2)) := by
    calc
      (δ : ENNReal) ^ (-ε) =
          (δ : ENNReal) ^ (-(ε / 6) + (-(ε / 6)) + (-(ε / 6)) + (-(ε / 2))) := by
        rw [show -ε = -(ε / 6) + -(ε / 6) + -(ε / 6) + -(ε / 2) by ring]
      _ = ((δ : ENNReal) ^ (-(ε / 6) + (-(ε / 6)) + (-(ε / 6)))) * (δ : ENNReal) ^ (-(ε / 2)) := by
        rw [ENNReal.rpow_add (-(ε / 6) + (-(ε / 6)) + (-(ε / 6))) (-(ε / 2)) hδ_nonzero
          hδ_not_top]
      _ = (((δ : ENNReal) ^ (-(ε / 6) + (-(ε / 6)))) * (δ : ENNReal) ^ (-(ε / 6)))
          * (δ : ENNReal) ^ (-(ε / 2)) := by
        rw [ENNReal.rpow_add (-(ε / 6) + (-(ε / 6))) (-(ε / 6)) hδ_nonzero hδ_not_top]
      _ = (((δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6))) * (δ : ENNReal) ^ (-(ε / 6)))
          * (δ : ENNReal) ^ (-(ε / 2)) := by
        rw [ENNReal.rpow_add (-(ε / 6)) (-(ε / 6)) hδ_nonzero hδ_not_top]
      _ = (δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6))
          * (δ : ENNReal) ^ (-(ε / 2)) := by ring
  -- Step 5: final calc
  calc
    μqT ≤ (Csplit : ENNReal)
        * ((δ : ENNReal) ^ (-(ε / 6)) * (nts : ENNReal) ^ β)
        * ((δ : ENNReal) ^ (-(ε / 6)) * ((Cinner : ENNReal) * Δ) ^ (1 - β)
          * ((a : ENNReal) / (b : ENNReal)) ^ β * (nj : ENNReal) ^ β) :=
      hstep
    _ = (Csplit : ENNReal) * (δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6))
        * ((nts : ENNReal) ^ β * (nj : ENNReal) ^ β) * ((Cinner : ENNReal) * Δ) ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ β := by
      ring
    _ ≤ (Csplit : ENNReal) * (δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6))
        * ((Ccard : ENNReal) ^ β * (nq : ENNReal) ^ β) * ((Cinner : ENNReal) * Δ) ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ β := by
      gcongr
    _ = (Csplit : ENNReal) * (δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6))
        * ((Ccard : ENNReal) ^ β * (nq : ENNReal) ^ β) * (Cinner : ENNReal) ^ (1 - β)
        * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β := by
      rw [hCinner_mul_eq]
      ring
    _ ≤ (Csplit : ENNReal) * (δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6))
        * ((Ccard : ENNReal) ^ β * (nq : ENNReal) ^ β) * (Cinner : ENNReal)
        * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β := by
      gcongr
    _ = (Csplit : ENNReal) * (Ccard : ENNReal) ^ β * (δ : ENNReal) ^ (-(ε / 6))
        * (δ : ENNReal) ^ (-(ε / 6)) * (nq : ENNReal) ^ β * (Cinner : ENNReal)
        * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β := by
      ring
    _ ≤ (δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6))
        * (nq : ENNReal) ^ β * (Cinner : ENNReal) * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β := by
      gcongr
    _ ≤ (δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6))
        * (nq : ENNReal) ^ β * (δ : ENNReal) ^ (-(ε / 2)) * Δ ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ β := by
      gcongr
    _ = (δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6)) * (δ : ENNReal) ^ (-(ε / 6))
        * (δ : ENNReal) ^ (-(ε / 2)) * (nq : ENNReal) ^ β * Δ ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ β := by
      ring
    _ = (δ : ENNReal) ^ (-ε) * (nq : ENNReal) ^ β * Δ ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ β := by
      rw [hsplitδ]
    _ = (δ : ENNReal) ^ (-ε) * Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β * (nq : ENNReal) ^ β := by
      ring

/-- **The `γ = 0` outer plank bound at the master scale, packaged for GWZ Proposition 6.6(B).**

The master-scale reading of GWZ Lemma 6.1 (`Kakeya.PlankEstimateAtMasterScale`) applied with
`γ = 0`, whose slab hypothesis is vacuous (`Kakeya.gammaZeroSlabBoundAtMasterScale`, GWZ Remark 6.2)
and whose eccentricity factor is therefore `1`.  This is the exact shape in which Proposition 6.6(B)
consumes the outer family produced by GWZ Proposition 5.1: fullness and Katz--Tao data at the master
scale `δ`, loss `δ ^ (-ε')`, no `(a/b)` factor. -/
theorem exists_outerMultiplicityBoundAtMasterScale.{u} {β : ℝ}
    (h61δ : PlankEstimateAtMasterScale.{u} β)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0),
      ∀ {κ' : Type u} (ts : Finset κ') {δ a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
        (W : κ' → ShadedPlank a b hab hb1),
        0 < δ → δ ≤ a → b ≤ b₀ →
        (∀ j ∈ ts, (W j).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
        (ts : Set κ').Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (W i).carrier (W j).carrier) →
        δ ^ η ≤ ShadedBody.fullness ts (fun j => (W j).toShadedBody) →
        IsKatzTao ts (fun j => (W j).toConvexSpaceBody) (δ ^ (-η)) →
        ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) ≤
          (δ : ENNReal) ^ (-ε') * (ts.card : ENNReal) ^ β := by
  rcases h61δ ε' hε' with ⟨η, hη, b₀, hb₀, hinstance⟩
  refine ⟨η, hη, b₀, hb₀, ?_⟩
  intro κ' ts δ a b hab hb1 W hδ hδa hbb₀ hWball hWed hWfull hWKT
  have hδ1 : δ ≤ 1 := le_trans hδa (le_trans hab hb1)
  have hslab : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
      ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
      ((Plank.inWideSlabFamily ts (fun j => (W j).toPrism3D) S).card : ℝ≥0)
        ≤ δ ^ (-η) * φ ^ (0 : ℝ) * (ts.card : ℝ≥0) :=
    fun φ hφR _ S =>
      gammaZeroSlabBoundAtMasterScale hδ hδ1 hη.le ts (fun j => (W j).toPrism3D) φ hφR S
  have hmain : ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) ≤
      (δ : ENNReal) ^ (-ε') * ((a : ENNReal) / (b : ENNReal)) ^ ((0 : ℝ) * β)
        * (ts.card : ENNReal) ^ β :=
    hinstance ts hab hb1 W
      hδ hδa hbb₀ hWball hWed hWfull hWKT 0 le_rfl zero_le_one hslab
  have hz : ((a : ENNReal) / (b : ENNReal)) ^ ((0 : ℝ) * β) = 1 := by
    rw [zero_mul, ENNReal.rpow_zero]
  rw [hz] at hmain
  rwa [mul_one] at hmain

/-- **Transfer of the inner `γ = 1` plank estimate to the outer scales.**

The rpow bookkeeping that turns the conclusion of GWZ Lemma 6.1 for the *normalised inner* family
(`Kakeya.PlankEstimateAtMasterScaleWithDensity` at `γ = 1`, stated with the inner maximal density)
into the shape the 6.6(B) combination lemmas consume: the ambient density `Δ₀` carrying the
Proposition 5.1 normalisation loss `Cinner`, and the eccentricity factor rewritten by the preserved
ratio `a'/b' = a/b`. -/
theorem innerBoundTransfer {β ε' : ℝ} (hβle : β ≤ 1)
    {δ a b a' b' Cinner : ℝ≥0} {Δ₀ Δj μTj : ENNReal} {nj : ℕ}
    (hratio : (a' : ENNReal) / (b' : ENNReal) = (a : ENNReal) / (b : ENNReal))
    (hmaxd : Δj ≤ (Cinner : ENNReal) * Δ₀)
    (hinner : μTj ≤ (δ : ENNReal) ^ (-ε') * Δj ^ (1 - β)
      * ((a' : ENNReal) / (b' : ENNReal)) ^ ((1 : ℝ) * β) * (nj : ENNReal) ^ β) :
    μTj ≤ (δ : ENNReal) ^ (-ε') * ((Cinner : ENNReal) * Δ₀) ^ (1 - β)
      * ((a : ENNReal) / (b : ENNReal)) ^ β * (nj : ENNReal) ^ β := by
  have hinner_simp : μTj ≤ (δ : ENNReal) ^ (-ε') * Δj ^ (1 - β)
      * ((a' : ENNReal) / (b' : ENNReal)) ^ β * (nj : ENNReal) ^ β := by
    simpa [one_mul] using hinner
  have hΔ : Δj ^ (1 - β) ≤ ((Cinner : ENNReal) * Δ₀) ^ (1 - β) := by
    have h_nonneg : (0 : ℝ) ≤ 1 - β := by linarith
    exact ENNReal.rpow_le_rpow hmaxd h_nonneg
  have hratio_enn : ((a' : ENNReal) / (b' : ENNReal)) ^ β =
      ((a : ENNReal) / (b : ENNReal)) ^ β := by
    rw [hratio]
  calc
    μTj ≤ (δ : ENNReal) ^ (-ε') * Δj ^ (1 - β) * ((a' : ENNReal) / (b' : ENNReal)) ^ β
        * (nj : ENNReal) ^ β := hinner_simp
    _ ≤ (δ : ENNReal) ^ (-ε') * ((Cinner : ENNReal) * Δ₀) ^ (1 - β)
        * ((a' : ENNReal) / (b' : ENNReal)) ^ β * (nj : ENNReal) ^ β := by
      gcongr
    _ = (δ : ENNReal) ^ (-ε') * ((Cinner : ENNReal) * Δ₀) ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ β * (nj : ENNReal) ^ β := by
      rw [hratio_enn]

/-! ### Additional estimates

The next declaration is **not** a proof of GWZ Proposition 6.6(B).  Two of its hypotheses,
`h61δ : PlankEstimateAtMasterScale β` and `h61δΔ : PlankEstimateAtMasterScaleWithDensity β`, are
`Prop`-valued readings of **GWZ Lemma 6.1 itself**.  Neither is established anywhere, on the source
branch or here; they are assumed.  So what is proved is the implication
"Lemma 6.1 at the master scale (both readings) ⟹ Proposition 6.6(B)", not Proposition 6.6(B).

Note also that the statement below is over
`Kakeya.Section6PartBData`, a different — and hypothesis-richer — datum than ship's
`Kakeya.GlobalPlankFactorization`. -/

/-- **GWZ Proposition 6.6(B).**
Suppose the partial estimates `K_KT(β)` and `K_F(β)` hold. For every `ε > 0` there are `η > 0`
and `δ₀ > 0` with the following property. Let `0 < δ ≤ δ₀`, and let `𝒯 = (T i)_{i ∈ q}` be a uniform
family of `δ`-tubes with shading in `B₁` satisfying `λ(𝒯, Y) ≥ δ ^ η`. Suppose that at some coarse
scale `ρ`, with `ρ`-tubes `(R k)_{k ∈ r}` above the fine tubes, a *single* indexed family
`𝒲 = (W j)_{j ∈ t}` of `a × b × 1` planks factors the family of `ρ`-tubes (`Fz`, whose outer bodies
are the planks). Then
`μ(𝒯, Y) ≤ δ ^ (-ε) · Δ_max(𝒯) ^ (1 - β) · (a/b) ^ β · |𝒯| ^ β`.

**The factorisation datum.**  The global plank factorisation is modelled through
`Kakeya.Section6PartBData`: a `Kakeya.GlobalComparableBodyFactorization`-style outer cell family of the coarse
`ρ`-tube family (each cell body containing the `ρ`-tubes it collects and contained in the cell's
representative `a × b × 1` plank, the family Katz--Tao with constant `C₀`), *together with* the three
Section-4.2 clauses that GWZ Section 6.6(B) actually uses and that the bare geometric structure does
not carry: the fine-to-coarse assignment function with two-sided comparable fibres, the
coarse-fibre Frostman datum of GWZ Remark 5.3 (the *fine* fibres are not Frostman), and the
representative plank of each cell as data rather than as an existential.  See
`Kakeya.factoringAndMultPropGlobal` and
`Kakeya/DimensionThree/Plank/Section6CoarseFactorisation.lean`.  The old weak hypothesis
`∀ i ∈ q, ∃ k ∈ r, T i ≤ R k` is a consequence of the datum
(`Kakeya.Section6PartBData.exists_parent`), so nothing is lost.

No outer body is assumed to *be* a plank.  That would demand each outer body be an exact
`Prism3D a b 1`; but an outer body is the convex hull of a union of `ρ`-tubes, and the box's vertex,
being an extreme point of the hull, would have to lie in one of the round tubes, whose inscribed
`ρ`-ball cannot fit into a corner.  Comparing two transverse coordinates gives `√2 ρ ≤ ρ`, hence
`ρ = 0` (`Kakeya.not_plankFactorization_tubes_of_pos`): with `0 < δ ≤ ρ` such hypotheses would be
unsatisfiable.  The obstruction is *not* the part-(A) one — no longitudinal comparison is involved,
and the conclusion is `ρ = 0` rather than `1/2 ≤ ρ`.

**Essential distinctness.**  Two pairwise-essential-distinctness data are hypotheses, because no
extraction theorem for planks exists in this repository and none is invented here: the fine
`δ`-tube family (the standard GWZ datum, and the honest source of essential distinctness of the
normalised inner plank family, essential distinctness being invariant under invertible affine maps)
and the representative planks of the outer cells.  Since steps  the second is consumed
*through* `Kakeya.factoringAndMultPropGlobal`, which now exports the outer family's own essential
distinctness rather than an identification of it with the representatives: that identification is
false for any homothety-presented outer family
(`Kakeya.CollarPlankRefute.not_statement_of_universal_presentedPlank_eq_repr`), and this branch must
not depend on it.

**Master-scale Lemma 6.1.**  Both applications of GWZ Lemma 6.1 are made in their master-scale
readings, passed as the hypotheses `h61δ` (`γ = 0`, outer, Katz--Tao case) and `h61δΔ` (`γ = 1`,
inner, with the `Δ_max ^ (1-β)` factor), and not in the plank-scale readings
`Kakeya.KatzTaoEstimate.plankEstimate_of_isKatzTao` and `Kakeya.KatzTaoEstimate.plankEstimate`:
after GWZ Proposition 5.1 the outer and inner fullness, Katz--Tao and slab data are available at the
master scale `δ` only.  See `Kakeya.PlankEstimateAtMasterScale` for why the plank-scale data are not
available, and `Kakeya.factoringAndMultPropGlobal` for what Proposition 5.1 does supply.

**The inner scale threshold.**  The produced `s₀ > 0` and the hypothesis `δ ≤ s₀ · a` are the inner
threshold of `Kakeya.factoringAndMultPropGlobal`, read through the inner scale `b' ≈ δ/a`: the
`γ = 1` application of Lemma 6.1 to the normalised inner family needs `b'` below a fixed threshold,
which fails exactly in the degenerate regime `ρ ≈ a ≈ δ`.  That regime is not covered here.

**Scale hypotheses.**  Unlike Proposition 6.6(A), where `ρ ≤ a` is *false* and `b ≤ 2ρ` is derived,
part (B) keeps `δ ≤ ρ ≤ a ≤ b ≤ 1`: here the `ρ`-tubes are the *inner* bodies, so the containment
runs the other way and `ρ ≤ a` is not merely consistent but forced by the datum itself
(`Kakeya.Section6PartBData.rho_le`, from `Kakeya.Tube.rho_le_of_le_prism3D`: a `ρ`-tube
contains a ball of radius `ρ` and the least width of an `a × b × 1` plank is `a`).  It is retained as
a hypothesis because it is part of the paper's hypothesis `δ ≤ ρ ≲ a ≤ b ≤ 1` and because the
degenerate case `r = ∅` carries no plank to derive it from.

**Formalisation status.**  Proved.  The `γ = 0` outer application is
`Kakeya.exists_outerMultiplicityBoundAtMasterScale`, the `γ = 1` inner one is `h61δΔ` followed by
`Kakeya.innerBoundTransfer`, the outer essential distinctness is the clause
`Kakeya.factoringAndMultPropGlobal` exports (which that leaf derives from the hypothesis on
`D.factor.repr`; the transport is `Kakeya.pairwise_isEssentiallyDistinct_of_toPrism3D_eq`), the
small-`b` combination is `Kakeya.combineGlobalFactorWithInnerLoss`, and the large-`b` branch is
`Kakeya.globalCoarsePlankFallback`.  The required Proposition 5.1 presentation is passed explicitly
to both the direct branch and the fallback. -/
theorem tubeMultiplicityOfGlobalPlankFactorisation_of_masterScaleLemma61 (Cprop : ℝ≥0) (hCprop : 1 ≤ Cprop)
    {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (h61δ : PlankEstimateAtMasterScale.{0} β)
    (h61δΔ : PlankEstimateAtMasterScaleWithDensity.{0} β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0), ∃ s₀ > (0 : ℝ≥0),
      ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (hδ0 : 0 < δ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        δ ≤ δ₀ →
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (q : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
          {κ : Type*} (r : Finset κ)
          (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF C₀ : ℝ≥0),
          C₀ ≤ δ ^ (-η) → CF ≤ δ ^ (-η) → Cfib ≤ δ ^ (-η) →
          δ ≤ ρ → ρ ≤ a → δ ≤ s₀ * a →
          ∀ (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀),
          D.Remark53Prop51 Cprop →
          (D.factor.cells : Set D.factor.Cell).Pairwise
            (fun x y => _root_.IsEssentiallyDistinct
              (D.factor.repr x).carrier (D.factor.repr y).carrier) →
          ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
            (δ : ENNReal) ^ (-ε) * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β := by
  intro ε hε
  have hε6 : (0 : ℝ) < ε / 6 := by positivity
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨ηₒ, hηₒ, b₀ₒ, hb₀ₒ, hOuter⟩ :=
    exists_outerMultiplicityBoundAtMasterScale h61δ (ε' := ε / 6) hε6
  obtain ⟨ηᵢ, hηᵢ, b₀ᵢ, hb₀ᵢ, h61⟩ := h61δΔ (ε / 6) hε6
  obtain ⟨Csplit, Ccard, Cinner, hCs1, hCc1, hCi1, hSplitFun⟩ :=
    factoringAndMultPropGlobal Cprop hCprop hβpos hβle
  obtain ⟨ηsplit, hηsplit, s₀split, hs₀split, hCfg⟩ :=
    hSplitFun ηₒ ηᵢ hηₒ hηᵢ b₀ₒ b₀ᵢ hb₀ₒ hb₀ᵢ
  obtain ⟨δ₀thr, hδ₀thr, hthrFun⟩ := rpowConstAbsorb (Csplit * Ccard) (by
    calc
      (1 : ℝ≥0) = (1 : ℝ≥0) * (1 : ℝ≥0) := by simp
      _ ≤ Csplit * Ccard := mul_le_mul hCs1 hCc1 (by positivity) (by positivity)
    ) (show (0 : ℝ) ≤ 1 + β by positivity) hε6
  obtain ⟨δ₀I, hδ₀I, hIfun⟩ :=
    rpowConstAbsorb Cinner hCi1 (show (0 : ℝ) ≤ 1 by norm_num) hε2
  obtain ⟨Ccoarse, hCcoarse, ηfall, hηfall, s₀fall, hs₀fall, hFallback⟩ :=
    globalCoarsePlankFallback Cprop hCprop hβpos hβle hKKT hKF h61δΔ hε2 b₀ₒ hb₀ₒ
  obtain ⟨δ₀co, hδ₀co, hcofun⟩ :=
    rpowConstAbsorb Ccoarse hCcoarse (show (0 : ℝ) ≤ 1 by norm_num) hε2
  set η := min (min ηsplit ηfall) (min ηₒ ηᵢ)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (lt_min hηsplit hηfall) (lt_min hηₒ hηᵢ)
  set δ₀ := min (min δ₀thr δ₀I) δ₀co
  have hδ₀ : 0 < δ₀ := by
    dsimp [δ₀]
    exact lt_min (lt_min hδ₀thr hδ₀I) hδ₀co
  set s₀ := min (min b₀ᵢ s₀fall) s₀split
  have hs₀ : 0 < s₀ := by
    dsimp [s₀]
    exact lt_min (lt_min hb₀ᵢ hs₀fall) hs₀split
  refine ⟨η, hη, δ₀, hδ₀, s₀, hs₀, ?_⟩
  intro ι q δ hδ0 T hδδ₀ hball hTdist hfull
    ρ a b hab hb1 κ r R m Cfib CF C₀ hC₀η hCFη hCfibη hδρ hρa hδsa D hRem hDED
  have hδ1 : δ ≤ 1 := hδρ.trans (hρa.trans (hab.trans hb1))
  have hδδ₀thr : δ ≤ δ₀thr := hδδ₀.trans (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδδ₀I : δ ≤ δ₀I := hδδ₀.trans (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδδ₀co : δ ≤ δ₀co := hδδ₀.trans (min_le_right _ _)
  have hη_le : η ≤ ηsplit := (min_le_left _ _).trans (min_le_left _ _)
  have hη_le_fall : η ≤ ηfall := (min_le_left _ _).trans (min_le_right _ _)
  have hfull' : (δ : ℝ≥0) ^ ηsplit ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) := by
    calc
      (δ : ℝ≥0) ^ ηsplit ≤ (δ : ℝ≥0) ^ η :=
        NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hη_le
      _ ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) := hfull
  have hC₀η' : C₀ ≤ δ ^ (-ηsplit) :=
    hC₀η.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith))
  have hCFη' : CF ≤ δ ^ (-ηsplit) :=
    hCFη.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith))
  have hCfibη' : Cfib ≤ δ ^ (-ηsplit) :=
    hCfibη.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith))
  have hfullF : (δ : ℝ≥0) ^ ηfall ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) := by
    calc
      (δ : ℝ≥0) ^ ηfall ≤ (δ : ℝ≥0) ^ η :=
        NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hη_le_fall
      _ ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) := hfull
  have hC₀ηF : C₀ ≤ δ ^ (-ηfall) :=
    hC₀η.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith))
  have hCFηF : CF ≤ δ ^ (-ηfall) :=
    hCFη.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith))
  have hCfibηF : Cfib ≤ δ ^ (-ηfall) :=
    hCfibη.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith))
  have hδb₀ᵢa : δ ≤ b₀ᵢ * a :=
    le_trans hδsa (mul_le_mul_right' ((min_le_left _ _).trans (min_le_left b₀ᵢ s₀fall)) a)
  have hδs₀falla : δ ≤ s₀fall * a :=
    le_trans hδsa (mul_le_mul_right' ((min_le_left _ _).trans (min_le_right b₀ᵢ s₀fall)) a)
  have hδs₀splita : δ ≤ s₀split * a :=
    le_trans hδsa (mul_le_mul_right' (min_le_right (min b₀ᵢ s₀fall) s₀split) a)
  by_cases hbcase : b ≤ b₀ₒ
  · have hδa : δ ≤ a := hδρ.trans hρa
    have ha_pos : 0 < a := lt_of_lt_of_le hδ0 hδa
    have hrest := hCfg q hδ0 T hball hTdist hfull' ρ a b hab hb1 ha_pos hbcase
      hδρ hρa hδb₀ᵢa hδs₀splita r R m Cfib CF C₀ hC₀η' hCFη' hCfibη' D hRem hDED
    rcases hrest with ⟨ts, W, hts_ne, hts_sub, hWed, hWball, hWfull, hWKT, hrest2⟩
    rcases hrest2 with ⟨a', b', ha'b', hb'1, ιj, qj, Pj, ha'pos, hδa', hb'thr, hratio,
      hPjball, hPjed, hjfull, hmaxd, hslab1, hcardle, hsplitineq⟩
    have hW : ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) ≤
        (δ : ENNReal) ^ (-(ε / 6)) * (ts.card : ENNReal) ^ β :=
      hOuter ts hab hb1 W hδ0 hδa hbcase hWball hWed hWfull hWKT
    have hinner := h61 qj ha'b' hb'1 Pj hδ0 hδa' hb'thr hPjball hPjed hjfull
      1 zero_le_one le_rfl hslab1
    have hTj := innerBoundTransfer hβle hratio hmaxd hinner
    have hthr : (Csplit : ENNReal) * (Ccard : ENNReal) ^ β ≤ (δ : ENNReal) ^ (-(ε / 6)) := by
      calc
        (Csplit : ENNReal) * (Ccard : ENNReal) ^ β
            ≤ ((Csplit * Ccard : ℝ≥0) : ENNReal) ^ ((1 : ℝ) + β) :=
          product_rpow_le hβpos Csplit Ccard hCs1 hCc1
        _ ≤ (δ : ENNReal) ^ (-(ε / 6)) := hthrFun δ hδ0 hδδ₀thr
    have hthrI : (Cinner : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 2)) := by
      simpa using hIfun δ hδ0 hδδ₀I
    exact combineGlobalFactorWithInnerLoss hβpos hβle hδ0 hδ1 hCs1 hCc1 hCi1
      hW hTj hsplitineq hcardle hthr hthrI
  · have hco : ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
      (Ccoarse : ENNReal) *
        ((δ : ENNReal) ^ (-(ε / 2)) * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
          * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β) :=
      hFallback q hδ0 T hball hTdist hfullF ρ a b hab hb1 r R m Cfib CF C₀
        hC₀ηF hCFηF hCfibηF hδρ hρa hδs₀falla D hRem hDED (not_le.mp hbcase)
    have hcoAbs : (Ccoarse : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 2)) := by
      simpa using hcofun δ hδ0 hδδ₀co
    have hδ_nonzero : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
    have hδ_not_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hsplitδ : (δ : ENNReal) ^ (-ε) = (δ : ENNReal) ^ (-(ε / 2)) * (δ : ENNReal) ^ (-(ε / 2)) := by
      calc
        (δ : ENNReal) ^ (-ε) = (δ : ENNReal) ^ (-(ε / 2) + (-(ε / 2))) := by
          rw [show (-ε : ℝ) = (-(ε / 2)) + (-(ε / 2)) by ring]
        _ = (δ : ENNReal) ^ (-(ε / 2)) * (δ : ENNReal) ^ (-(ε / 2)) :=
          ENNReal.rpow_add (-(ε / 2)) (-(ε / 2)) hδ_nonzero hδ_not_top
    calc
      ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
        (Ccoarse : ENNReal) *
          ((δ : ENNReal) ^ (-(ε / 2)) * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
            * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β) := hco
      _ = ((Ccoarse : ENNReal) * (δ : ENNReal) ^ (-(ε / 2)))
          * ((maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
            * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β) := by ring
      _ ≤ ((δ : ENNReal) ^ (-(ε / 2)) * (δ : ENNReal) ^ (-(ε / 2)))
          * ((maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
            * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β) := by
        gcongr
      _ = (δ : ENNReal) ^ (-ε)
          * ((maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
            * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β) := by
        rw [hsplitδ]
      _ = (δ : ENNReal) ^ (-ε) * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
          * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β := by ring

end Kakeya

end
