/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Kakeya.DimensionThree.MainLemma2.Section6CompatDyadic
public import Kakeya.DimensionThree.Plank.SlabCoverAbsolute
public import Kakeya.DimensionThree.Plank.FibreClassPigeonhole
public import Kakeya.DimensionThree.Plank.SlabwiseDensity

/-!
# The slab layer, wired to the leaf's data

This file discharges **every hypothesis** of `Plank.slabwiseDensity_of_preassembly` from the data
`ShadedPlank.reduction_to_slab_atTypicalAngle` carries, inside one dyadic block of
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_dyadicBlocks`.

Two things make it possible, and neither existed before this run.

* **The absolute plank-angle binder** `Kakeya.HasMaxPlankAngleBound s Y'' (planks Y) θ 1`, threaded
  into the leaf.  It lets the slab cover run at `θ` *itself*
  (`Plank.exists_slabCover_of_absoluteAngle` asks for the bound at the literal constant `2`), so no
  radius transport is needed; and it supplies
  `Plank.localAngleConcentration_of_preassemblyData`'s `hmax`, whose angle constant is bound
  **before** the configuration.
* **The dyadic block's `a`-scale bound** `C ≤ a ^ (-(2 * 2 ^ j * ε))`.  It supplies the same
  producer's two-sided typicality at `Cstab0 * a ^ (-εs)` with `εs = 2 ^ (j+1) ε` fixed before the
  configuration, and it makes `ShadedBody.HasCConstantMultiplicity s Y'' (1 * a ^ (-εint))`
  immediate at `εint = εs` — so the multiplicity pigeonhole is **not needed at all** and its
  `1 / (log₂ |s| + 1)` loss never arises.

## The exponents

`εwork = 6 · 2 ^ j · ε`, `ηL = (4η + εwork)/3`, `εs = εint = 2 · 2 ^ j · ε`.  They satisfy
`Plank.slabwiseDensity_of_preassembly`'s `3 * ηL ≤ 4 * η + εwork` with equality and
`Plank.localAngleConcentration_of_preassemblyData`'s `εs < ηL` with margin `4η/3`, uniformly in the
block index `j` — `ShadedPlank.blockLedger_margin` made operational.

## What is not here

The output side: converting the returned Item-1 constant and refinement coefficient into the leaf's
`c1 = δ ^ ε'` and composing back to `ShadedPlank.bodies Y`.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal Real ENNReal

noncomputable section

namespace ShadedPlank

universe u

/-- **Every hypothesis of `Plank.slabwiseDensity_of_preassembly`, discharged from the leaf's data
inside dyadic block `j`.**

The conclusion is that theorem's output: a measurable `Gtot`, the quantitative refinement of `Y''`
restricted to it at coefficient `cRefC * a ^ (2 · 2 ^ j · ε)`, and Item 1 at radius `θ b` with
dilation `Kakeya.plankReduction.ballDilation`, at the constant

`cBall * cLamBox ^ 2 * a ^ (4η + 6 · 2 ^ j · ε)`,  `cLamBox = K₀ · a ^ (εint − ηL) · λ(s, Y'')`.

`cRefC`, `K₀` and `cBall` are bound **before** the configuration; the only configuration-dependent
factor is the fullness `λ(s, Y'')`, which is a quantity of the data and not of the slab layer. -/
theorem exists_slabDensityOutputs_of_blockData {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (j : ℕ) :
    ∃ cRefC K₀ cBall : ℝ≥0, 0 < cRefC ∧ 0 < K₀ ∧ 0 < cBall ∧
    ∀ {ι : Type u} (s : Finset ι) {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < a → a < 1 → 0 < b → a / b ≤ θ → 1 ≤ C →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
      (2 : ℝ≥0) ≤ Real.toNNReal (Kakeya.plankAngleScaleA a) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      C ≤ a ^ (-(2 * (2 : ℝ) ^ j * ε)) →
      ∃ (Gtot : Set (EuclideanSpace ℝ (Fin 3))) (hGtot : MeasurableSet Gtot),
        ShadedBody.IsCRefinement s
            (fun i => ShadedBody.restrictShade (Y'' i) Gtot hGtot) s Y''
            (cRefC * a ^ (2 * (2 : ℝ) ^ j * ε)) ∧
        ∀ x : EuclideanSpace ℝ (Fin 3),
          ((⋃ i ∈ s, (ShadedBody.restrictShade (Y'' i) Gtot hGtot).shade) ∩
            Metric.closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty →
            ((cBall
                * (K₀ * a ^ (2 * (2 : ℝ) ^ j * ε - (4 * η + 6 * (2 : ℝ) ^ j * ε) / 3)
                    * ShadedBody.fullness s Y'')
                * (K₀ * a ^ (2 * (2 : ℝ) ^ j * ε - (4 * η + 6 * (2 : ℝ) ^ j * ε) / 3)
                    * ShadedBody.fullness s Y'')
                * a ^ (4 * η + 6 * (2 : ℝ) ^ j * ε) : ℝ≥0) : ENNReal) *
                volume (Metric.closedBall x ((θ * b : ℝ≥0) : ℝ))
              ≤ volume ((⋃ i ∈ s, (ShadedBody.restrictShade (Y'' i) Gtot hGtot).shade) ∩
                Metric.closedBall x
                  ((Kakeya.plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ))) := by
  classical
  -- the block's exponents depend only on `η`, `ε`, `j`
  set εwork : ℝ := 6 * (2 : ℝ) ^ j * ε with hεworkdef
  set ηL : ℝ := (4 * η + εwork) / 3 with hηLdef
  set εs : ℝ := 2 * (2 : ℝ) ^ j * ε with hεsdef
  have hεspos : 0 < εs := by rw [hεsdef]; positivity
  have hlt : εs < ηL := by
    rw [hεsdef, hηLdef, hεworkdef]
    nlinarith [hη, hε, pow_pos (by norm_num : (0:ℝ) < 2) j]
  -- the constants, all bound before the index type
  obtain ⟨Cset, Cang, Cset', Cang', Nov, hCset, hCang, hNov, hCsetLe, hCangLe,
    hCset'ge, hCang'ge, hcover⟩ := Plank.exists_slabCover_of_absoluteAngle
  obtain ⟨cTan, hcTan, htanlem⟩ := Plank.tangentiality_of_trimmedSlabFamilies Cang'
    (le_trans hCang hCangLe)
  obtain ⟨Ceta, hCeta, hLAClem⟩ :=
    Plank.localAngleConcentration_of_preassemblyData 2 1 (by norm_num) le_rfl hεspos hlt
  obtain ⟨cBall, hcBall, hslab⟩ := Plank.slabwiseDensity_of_preassembly cTan Ceta hCeta
  have hNov0 : (Nov : ℝ≥0) ≠ 0 := by
    simpa using (Nat.pos_of_ne_zero (by omega : Nov ≠ 0)).ne'
  have hcTan0 : cTan ≠ 0 := (lt_of_lt_of_le zero_lt_one hcTan).ne'
  refine ⟨(256 * (Nov : ℝ≥0) * 1)⁻¹, (2 * (512 * (Nov : ℝ≥0) * cTan))⁻¹, cBall,
    ?_, ?_, hcBall, ?_⟩
  · simp only [mul_one]
    exact pos_iff_ne_zero.mpr (inv_ne_zero (by positivity))
  · exact pos_iff_ne_zero.mpr (inv_ne_zero (by positivity))
  intro ι s a b hab hb1 Y θ hθ1 C Y'' ha ha1 hb hθlb hC1 hYref hconstY htyp hmaxA hA2 hfullY hCa
  have hθ : (0 : ℝ≥0) < θ := lt_of_lt_of_le (by positivity) hθlb
  set Y₁ : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := Y'' with hY₁
  have hshV : ∀ i ∈ s, (Y₁ i).shade ⊆ ((ShadedPlank.planks Y i).carrier :
      Set (EuclideanSpace ℝ (Fin 3))) := by
    intro i hi x hx
    have h1 : x ∈ (Y'' i).shade := hx
    have h2 := (hYref.1.2 i hi).2 h1
    exact (ShadedPlank.bodies Y i).shade_subset h2
  have hcarEq : ∀ i ∈ s, ((Y₁ i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((ShadedPlank.planks Y i).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro i hi
    have := (hYref.1.2 i hi).1
    simp only [hY₁]
    rw [this]
  have hmax2 : Kakeya.HasMaxPlankAngleBound s Y₁ (ShadedPlank.planks Y) θ 2 :=
    Kakeya.HasMaxPlankAngleBound.mono_const (by norm_num)
      (Kakeya.HasMaxPlankAngleBound.mono (Finset.Subset.refl s) (fun i _ => le_rfl) hmaxA)
  obtain ⟨𝒮, hcov, hovIdx, hovPt⟩ :=
    hcover s (ShadedPlank.planks Y) Y₁ hθ1 ha hθlb hmax2 hshV
  set T : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → Finset ι :=
    fun S sh q => (Plank.inSlabFamilyC Cset' Cang' s (ShadedPlank.planks Y) S).filter
      (fun i => ((Plank.trimmedSlabShading Cset Cang s (ShadedPlank.planks Y) Y₁ S i).shade ∩
        Plank.halfSlabBox S b sh q).Nonempty) with hTdef
  set Z : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → ι →
      ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    fun S sh q i => ShadedBody.restrictShade
      (Plank.trimmedSlabShading Cset Cang s (ShadedPlank.planks Y) Y₁ S i)
      (Plank.halfSlabBox S b sh q) (Plank.measurableSet_halfSlabBox S b sh q) with hZdef
  have haθb : a ≤ θ * b := by
    have h := mul_le_mul_right' hθlb b
    rwa [div_mul_cancel₀ _ hb.ne'] at h
  have htan := htanlem Cset Cang Cset' s (ShadedPlank.planks Y) Y₁ T ha hb haθb hshV
    (fun S sh q => rfl)
  have htyp₁ : Kakeya.IsTypicalPlankAngle s Y₁ (ShadedPlank.planks Y) θ (1 * a ^ (-εs))
      (Real.toNNReal (Kakeya.plankAngleScaleA a)) :=
    Kakeya.IsTypicalPlankAngle.mono_const (by rw [one_mul]; exact hCa) htyp
  have hLAC := hLAClem Cset Cang Cset' Cang' (Real.toNNReal (Kakeya.plankAngleScaleA a))
    s (ShadedPlank.planks Y) Y₁ T Z ha ha1 hb hθ haθb hA2 hCset'ge hCang'ge hshV hmax2 htyp₁
    (fun S sh q => rfl) (fun S sh q i _ => rfl)
  set εint : ℝ := εs with hεintdef
  have hεintpos : 0 < εint := by rw [hεintdef]; exact hεspos
  have hCmult : ShadedBody.HasCConstantMultiplicity s Y₁ (1 * a ^ (-εint)) := by
    refine ShadedBody.HasCConstantMultiplicity.mono s Y₁ ?_ hconstY
    rw [one_mul]
    exact hCa
  set lamLower : ℝ≥0 := ShadedBody.fullness s Y₁ with hlamLowerdef
  set lamScale : ℝ≥0 :=
    (2 * (1 : ℝ≥0))⁻¹ * a ^ εint * lamLower / (512 * (Nov : ℝ≥0) * cTan) with hlamScaledef
  set cLamBox : ℝ≥0 := lamScale * a ^ (-ηL) with hcLamBoxdef
  have hηLpos : 0 < ηL := by rw [hηLdef, hεworkdef]; positivity
  have hcLamBoxle : cLamBox * a ^ ηL ≤ lamScale := by
    rw [hcLamBoxdef, mul_assoc, ← NNReal.rpow_add ha.ne']
    simp
  have h3ηL : 3 * ηL ≤ 4 * η + εwork := by rw [hηLdef]; ring_nf; linarith
  have hCset'1 : (1 : ℝ≥0) ≤ Cset' := le_trans hCset hCsetLe
  have hlamY : 0 < ShadedBody.fullness s (ShadedPlank.bodies Y) :=
    lt_of_lt_of_le (NNReal.rpow_pos ha) hfullY
  have hcarne : (∑ i ∈ s, volume ((ShadedPlank.bodies Y i).carrier :
      Set (EuclideanSpace ℝ (Fin 3)))) ≠ ⊤ := by
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun i _ => ?_))
    rw [show ((ShadedPlank.bodies Y i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = (Y i).carrier from rfl, ShadedPlank.volume_carrier (Y i)]
    finiteness
  have hsumY : (∑ i ∈ s, volume (ShadedPlank.bodies Y i).shade) ≠ 0 :=
    ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos s (ShadedPlank.bodies Y) hlamY
  have hsumY'' : (∑ i ∈ s, volume (Y'' i).shade) ≠ 0 := by
    intro h0
    have hle := hYref.2
    rw [h0, le_zero_iff, mul_eq_zero] at hle
    rcases hle with h | h
    · have hz : (C⁻¹ : ℝ≥0) = 0 := by exact_mod_cast h
      exact absurd hz (inv_ne_zero (lt_of_lt_of_le zero_lt_one hC1).ne')
    · exact hsumY h
  have hcarne₁ : (∑ i ∈ s, volume ((Y₁ i).carrier :
      Set (EuclideanSpace ℝ (Fin 3)))) ≠ ⊤ := by
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun i hi => ?_))
    rw [show ((Y₁ i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = ((ShadedPlank.planks Y i).carrier : Set (EuclideanSpace ℝ (Fin 3))) from hcarEq i hi,
      show ((ShadedPlank.planks Y i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = (Y i).carrier from rfl, ShadedPlank.volume_carrier (Y i)]
    finiteness
  have hlamL : 0 < lamLower := by
    rw [hlamLowerdef, pos_iff_ne_zero]
    intro h
    have hdef := ShadedBody.fullness_def s Y₁
    rw [h, ENNReal.coe_zero] at hdef
    rcases ENNReal.div_eq_zero_iff.mp hdef.symm with h1 | h1
    · exact hsumY'' h1
    · exact hcarne₁ h1
  have hcLamBoxpos : 0 < cLamBox := by
    rw [hcLamBoxdef]
    have hs : 0 < lamScale := by
      rw [hlamScaledef]
      have hpow : (0 : ℝ≥0) < a ^ εint := NNReal.rpow_pos ha
      positivity
    have : (0 : ℝ≥0) < a ^ (-ηL) := NNReal.rpow_pos ha
    positivity
  obtain ⟨Gtot, hGtot, href, hitem⟩ := hslab Cset Cang Cset' Cang' 1 cLamBox lamLower lamScale
    η εwork εint ηL Nov s (ShadedPlank.planks Y) Y₁ 𝒮 T Z hcTan hCset'1 (by norm_num) hNov
    ha ha1.le hb hθ hb1 hθlb hηLpos hcLamBoxpos h3ηL hcLamBoxle rfl hCsetLe hCangLe
    hcov hovIdx hovPt hshV hcarEq (fun S sh q => rfl) (fun S sh q i _ => rfl)
    (by
      intro S sh q i hi
      simp only [hTdef, Finset.mem_filter] at hi
      have his : i ∈ s := Plank.inSlabFamilyC_subset hi.1
      simpa [hZdef, Plank.trimmedSlabShading] using hcarEq i his)
    htan
    (by
      intro S sh q i hi
      simp only [hTdef, Finset.mem_filter] at hi
      have his : i ∈ s := Plank.inSlabFamilyC_subset hi.1
      simpa [hZdef, Plank.trimmedSlabShading] using hcarEq i his)
    (fun S Dg => hLAC S Dg) le_rfl hCmult
  refine ⟨Gtot, hGtot, ?_, ?_⟩
  · simpa [hεintdef, hεsdef] using href
  · intro x hx
    have hsplit : (a : ℝ≥0) ^ (εint - ηL) = a ^ εint * a ^ (-ηL) := by
      rw [← NNReal.rpow_add ha.ne']
      congr 1
    have hkey : cLamBox
        = (2 * (512 * (Nov : ℝ≥0) * cTan))⁻¹ * a ^ (εint - ηL) * lamLower := by
      rw [hcLamBoxdef, hlamScaledef, hsplit, div_eq_mul_inv, mul_inv]
      simp only [inv_one, mul_one]
      ring
    have := hitem x hx
    rw [hkey] at this
    simpa [hεintdef, hεsdef, hηLdef, hεworkdef, hlamLowerdef, hY₁] using this

/-! ## Closing the leaf -/

/-- `2 ≤ Kakeya.plankAngleScaleA a` once `a ≤ 3⁻¹`: then `log a⁻¹ ≥ 1`, so the square root is at
least `1` and the exponential at least `e > 2`.  This is the one smallness fact
`Plank.localAngleConcentration_of_preassemblyData`'s stability-scale hypothesis `2 ≤ A` needs, and
the dyadic reduction supplies it through its `a ≤ athr` export. -/
theorem two_le_plankAngleScaleA_toNNReal {a : ℝ≥0} (ha : 0 < a) (ha3 : a ≤ 3⁻¹) :
    (2 : ℝ≥0) ≤ Real.toNNReal (Kakeya.plankAngleScaleA a) := by
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hinv : (3 : ℝ) ≤ (a : ℝ)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hapos]
    calc (a : ℝ) ≤ ((3⁻¹ : ℝ≥0) : ℝ) := by exact_mod_cast ha3
      _ = 3⁻¹ := by norm_num
  have hlog : (1 : ℝ) ≤ Real.log (a : ℝ)⁻¹ := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 3) hinv
    have he : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      nlinarith [Real.exp_one_lt_d9]
    linarith
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (Real.log (a : ℝ)⁻¹) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hlog
  have hexp : (2 : ℝ) ≤ Kakeya.plankAngleScaleA a := by
    rw [Kakeya.plankAngleScaleA]
    calc (2 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
      _ ≤ Real.exp (Real.sqrt (Real.log (a : ℝ)⁻¹)) := Real.exp_le_exp.mpr hsqrt
  have hco : ((2 : ℝ≥0) : ℝ) ≤ Kakeya.plankAngleScaleA a := by exact_mod_cast hexp
  exact (Real.le_toNNReal_iff_coe_le (by linarith : (0:ℝ) ≤ Kakeya.plankAngleScaleA a)).mpr hco

/-- **GWZ 6.13 on one dyadic block.**

The target statement with the block hypotheses of
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_dyadicBlocks` inserted, and proved.  The output is
`s' = s`, `Y' = Y''` restricted to the slab layer's `Gtot`, and `c1 = δ ^ ε'`.

* the fullness clause, `δ ^ ε' · a ^ ε ≤ cRefC · a ^ (4 · 2 ^ j · ε)`, using `δ ≤ a ^ (2 ^ j)` and
  `C ≤ a ^ (-(2 · 2 ^ j · ε))` twice — once for `λ(s, Y'') ≥ C⁻¹ λ(s, bodies Y)` and once for the
  refinement coefficient;
* Item 1, `δ ^ ε' · a ^ (4η + ε) ≤ cBall · K₀ ^ 2 · a ^ (10 · 2 ^ j · ε + (10/3) η)`, i.e.
  `(10/3) η ≤ 4η + ε + 118 · 2 ^ j · ε`, true uniformly in `j`;
* the absolute constants `cRefC`, `cBall · K₀ ^ 2` are absorbed into `a ^ ε` and
  `a ^ ((2/3) η + ε)` by the `a ≤ athr` the dyadic reduction exports, which is itself
  `a ^ (2 ^ J) ≤ δ ≤ δthr`.

No smallness threshold on `δ` is needed here at all: `δthr = 1`. -/
theorem reduction_to_slab_atTypicalAngle_block :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (j : ℕ) (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr athr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧ 0 < athr ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
      (a ^ ((2 : ℝ) ^ (j + 1)) ≤ δ) →
      (δ ≤ a ^ ((2 : ℝ) ^ j)) →
      (C ≤ a ^ (-((2 : ℝ) ^ (j + 1) * ε))) →
      (a ≤ athr) →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * a ^ (4 * η) * a ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε') := by
  intro η ε ε' hη hε hε' hgap j Ccard D
  classical
  obtain ⟨cRefC, K₀, cBall, hcRefC, hK₀, hcBall, hwire⟩ :=
    exists_slabDensityOutputs_of_blockData (η := η) (ε := ε) hη hε j
  have hCK : (0 : ℝ≥0) < cBall * K₀ * K₀ := by positivity
  set athr : ℝ≥0 :=
    min (min (cRefC ^ ε⁻¹) ((cBall * K₀ * K₀) ^ ((2 / 3 * η + ε)⁻¹))) 3⁻¹ with hathrdef
  have hathrpos : (0 : ℝ≥0) < athr := by
    refine lt_min (lt_min (NNReal.rpow_pos hcRefC) (NNReal.rpow_pos hCK)) (by norm_num)
  refine ⟨1, athr, one_pos, le_rfl, hathrpos, ?_⟩
  intro ι s δ a b hab hb1 Y θ hθ1 C Y'' hδ hδa ha1 _hδthr hwin hfull hma hmd h2 hcard
    hθlb hC1 hCδ hYref hYmult htyp hmaxA hjlo hjhi hCa haathr
  have ha : (0 : ℝ≥0) < a := lt_of_lt_of_le hδ hδa
  have hb : (0 : ℝ≥0) < b := lt_of_lt_of_le ha hab
  have ha1' : (a : ℝ≥0) ≤ 1 := ha1.le
  have ha3 : a ≤ 3⁻¹ := le_trans haathr (min_le_right _ _)
  have hA2 := two_le_plankAngleScaleA_toNNReal ha ha3
  have hCa' : C ≤ a ^ (-(2 * (2 : ℝ) ^ j * ε)) := by
    refine le_trans hCa (le_of_eq ?_)
    congr 1
    ring
  obtain ⟨Gtot, hGtot, href, hitem⟩ :=
    hwire s Y θ hθ1 C Y'' ha ha1 hb hθlb hC1 hYref hYmult htyp hmaxA hA2 hfull hCa'
  -- the two absorbed constants
  have habs1 : (a : ℝ≥0) ^ ε ≤ cRefC := by
    have h := NNReal.rpow_le_rpow (le_trans haathr (le_trans (min_le_left _ _) (min_le_left _ _)))
      hε.le
    refine le_trans h (le_of_eq ?_)
    rw [← NNReal.rpow_mul, inv_mul_cancel₀ hε.ne', NNReal.rpow_one]
  have hposexp : (0 : ℝ) < 2 / 3 * η + ε := by positivity
  have habs2 : (a : ℝ≥0) ^ (2 / 3 * η + ε) ≤ cBall * K₀ * K₀ := by
    have h := NNReal.rpow_le_rpow (le_trans haathr (le_trans (min_le_left _ _) (min_le_right _ _)))
      hposexp.le
    refine le_trans h (le_of_eq ?_)
    rw [← NNReal.rpow_mul, inv_mul_cancel₀ hposexp.ne', NNReal.rpow_one]
  -- carriers are positive in total
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with hs | hs
    · exfalso
      have hz : ShadedBody.fullness s (ShadedPlank.bodies Y) = 0 := by simp [hs]
      rw [hz] at hfull
      exact absurd (le_antisymm hfull bot_le) (NNReal.rpow_pos ha).ne'
    · exact hs
  have hcarpos : 0 < ∑ i ∈ s, volume ((ShadedPlank.bodies Y i).carrier :
      Set (EuclideanSpace ℝ (Fin 3))) := by
    obtain ⟨i0, hi0⟩ := hsne
    have hpos : 0 < volume ((ShadedPlank.bodies Y i0).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) := by
      rw [show ((ShadedPlank.bodies Y i0).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = (Y i0).carrier from rfl, ShadedPlank.volume_carrier (Y i0)]
      exact ENNReal.mul_pos (ENNReal.mul_pos (by norm_num) (ENNReal.coe_pos.mpr ha).ne').ne'
        (ENNReal.coe_pos.mpr hb).ne'
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun i =>
      volume ((ShadedPlank.bodies Y i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
      (fun i _ => bot_le) hi0)
  have hcarEq'' : ∀ i ∈ s, volume ((Y'' i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = volume ((ShadedPlank.bodies Y i).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    fun i hi => by rw [(hYref.1.2 i hi).1]
  have hcarpos'' : 0 < ∑ i ∈ s, volume ((Y'' i).carrier :
      Set (EuclideanSpace ℝ (Fin 3))) := by
    rwa [Finset.sum_congr rfl hcarEq'']
  have hmpos0 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have h1 : C⁻¹ * ShadedBody.fullness s (ShadedPlank.bodies Y)
      ≤ ShadedBody.fullness s Y'' :=
    ShadedBody.IsCRefinement.mul_fullness_le s Y'' s (ShadedPlank.bodies Y) hcarpos hYref
  have hCinv : (a : ℝ≥0) ^ (2 * (2 : ℝ) ^ j * ε) ≤ C⁻¹ := by
    have hax : (0 : ℝ≥0) < a ^ (2 * (2 : ℝ) ^ j * ε) := NNReal.rpow_pos ha
    have h : C ≤ ((a : ℝ≥0) ^ (2 * (2 : ℝ) ^ j * ε))⁻¹ := by
      rw [← NNReal.rpow_neg]; exact hCa'
    rw [NNReal.le_inv_iff_mul_le hax.ne'] at h
    rw [NNReal.le_inv_iff_mul_le (lt_of_lt_of_le zero_lt_one hC1).ne']
    calc (a : ℝ≥0) ^ (2 * (2 : ℝ) ^ j * ε) * C = C * a ^ (2 * (2 : ℝ) ^ j * ε) := by ring
      _ ≤ 1 := h
  refine ⟨s, fun i => ShadedBody.restrictShade (Y'' i) Gtot hGtot, δ ^ ε',
    NNReal.rpow_pos hδ, ?_, href.1, ?_, ?_, ?_⟩
  · -- refinement of the plank bodies
    refine ⟨Finset.Subset.refl s, fun i hi => ⟨?_, ?_⟩⟩
    · exact (href.1.2 i hi).1.trans (hYref.1.2 i hi).1
    · exact Set.Subset.trans (href.1.2 i hi).2 ((hYref.1.2 i hi).2)
  · -- the fullness clause
    have h2' : (cRefC * a ^ (2 * (2 : ℝ) ^ j * ε)) * ShadedBody.fullness s Y''
        ≤ ShadedBody.fullness s (fun i => ShadedBody.restrictShade (Y'' i) Gtot hGtot) :=
      ShadedBody.IsCRefinement.mul_fullness_le s
        (fun i => ShadedBody.restrictShade (Y'' i) Gtot hGtot) s Y'' hcarpos'' href
    have hmpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hstep : (δ : ℝ≥0) ^ ε' * a ^ ε ≤ cRefC * a ^ (4 * (2 : ℝ) ^ j * ε) := by
      have hd : (δ : ℝ≥0) ^ ε' ≤ a ^ ((2 : ℝ) ^ j * ε') := by
        calc (δ : ℝ≥0) ^ ε' ≤ (a ^ ((2 : ℝ) ^ j)) ^ ε' := NNReal.rpow_le_rpow hjhi hε'.le
          _ = a ^ ((2 : ℝ) ^ j * ε') := by rw [← NNReal.rpow_mul]
      have hd2 : (a : ℝ≥0) ^ ((2 : ℝ) ^ j * ε') ≤ a ^ (128 * (2 : ℝ) ^ j * ε) :=
        NNReal.rpow_le_rpow_of_exponent_ge ha ha1' (by nlinarith)
      have hcomb : (δ : ℝ≥0) ^ ε' * a ^ ε ≤ a ^ (128 * (2 : ℝ) ^ j * ε + ε) := by
        calc (δ : ℝ≥0) ^ ε' * a ^ ε ≤ a ^ (128 * (2 : ℝ) ^ j * ε) * a ^ ε := by
              gcongr; exact le_trans hd hd2
          _ = a ^ (128 * (2 : ℝ) ^ j * ε + ε) := by rw [← NNReal.rpow_add ha.ne']
      refine le_trans hcomb ?_
      have hsplit : (a : ℝ≥0) ^ (128 * (2 : ℝ) ^ j * ε + ε)
          = a ^ (124 * (2 : ℝ) ^ j * ε + ε) * a ^ (4 * (2 : ℝ) ^ j * ε) := by
        rw [← NNReal.rpow_add ha.ne']; congr 1; ring
      rw [hsplit]
      gcongr
      calc (a : ℝ≥0) ^ (124 * (2 : ℝ) ^ j * ε + ε) ≤ a ^ ε :=
            NNReal.rpow_le_rpow_of_exponent_ge ha ha1' (by nlinarith)
        _ ≤ cRefC := habs1
    have hfin : cRefC * a ^ (4 * (2 : ℝ) ^ j * ε) * ShadedBody.fullness s (ShadedPlank.bodies Y)
        ≤ ShadedBody.fullness s (fun i => ShadedBody.restrictShade (Y'' i) Gtot hGtot) := by
      calc cRefC * a ^ (4 * (2 : ℝ) ^ j * ε) * ShadedBody.fullness s (ShadedPlank.bodies Y)
          = (cRefC * a ^ (2 * (2 : ℝ) ^ j * ε))
            * (a ^ (2 * (2 : ℝ) ^ j * ε) * ShadedBody.fullness s (ShadedPlank.bodies Y)) := by
            rw [show (4 : ℝ) * (2 : ℝ) ^ j * ε = 2 * (2 : ℝ) ^ j * ε + 2 * (2 : ℝ) ^ j * ε by ring,
              NNReal.rpow_add ha.ne']
            ring
        _ ≤ (cRefC * a ^ (2 * (2 : ℝ) ^ j * ε)) * ShadedBody.fullness s Y'' := by
            gcongr
            exact le_trans (by gcongr) h1
        _ ≤ ShadedBody.fullness s (fun i => ShadedBody.restrictShade (Y'' i) Gtot hGtot) := h2'
    exact le_trans (by gcongr) hfin
  · -- Item 1
    have hmpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    set E : ℝ := 2 * (2 : ℝ) ^ j * ε - (4 * η + 6 * (2 : ℝ) ^ j * ε) / 3 with hEdef
    have hlam2 : (a : ℝ≥0) ^ (2 * (2 : ℝ) ^ j * ε) * a ^ η ≤ ShadedBody.fullness s Y'' := by
      refine le_trans ?_ h1
      gcongr
    -- the produced constant, bounded below by a single `a`-power
    have hpow : (a : ℝ≥0) ^ E * a ^ E * (a ^ (2 * (2 : ℝ) ^ j * ε) * a ^ η)
          * (a ^ (2 * (2 : ℝ) ^ j * ε) * a ^ η) * a ^ (4 * η + 6 * (2 : ℝ) ^ j * ε)
        = a ^ (10 * (2 : ℝ) ^ j * ε + 10 / 3 * η) := by
      simp only [← NNReal.rpow_add ha.ne']
      congr 1
      rw [hEdef]; ring
    have hBIG : cBall * K₀ * K₀ * a ^ (10 * (2 : ℝ) ^ j * ε + 10 / 3 * η)
        ≤ cBall * (K₀ * a ^ E * ShadedBody.fullness s Y'')
            * (K₀ * a ^ E * ShadedBody.fullness s Y'')
            * a ^ (4 * η + 6 * (2 : ℝ) ^ j * ε) := by
      rw [← hpow]
      calc cBall * K₀ * K₀ * ((a : ℝ≥0) ^ E * a ^ E
              * (a ^ (2 * (2 : ℝ) ^ j * ε) * a ^ η) * (a ^ (2 * (2 : ℝ) ^ j * ε) * a ^ η)
              * a ^ (4 * η + 6 * (2 : ℝ) ^ j * ε))
          = cBall * (K₀ * a ^ E * (a ^ (2 * (2 : ℝ) ^ j * ε) * a ^ η))
              * (K₀ * a ^ E * (a ^ (2 * (2 : ℝ) ^ j * ε) * a ^ η))
              * a ^ (4 * η + 6 * (2 : ℝ) ^ j * ε) := by ring
        _ ≤ cBall * (K₀ * a ^ E * ShadedBody.fullness s Y'')
              * (K₀ * a ^ E * ShadedBody.fullness s Y'')
              * a ^ (4 * η + 6 * (2 : ℝ) ^ j * ε) := by gcongr
    -- the demanded constant, bounded above by a single `a`-power
    have hLHS : (δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε
        ≤ a ^ (128 * (2 : ℝ) ^ j * ε + 4 * η + ε) := by
      have hd : (δ : ℝ≥0) ^ ε' ≤ a ^ (128 * (2 : ℝ) ^ j * ε) := by
        calc (δ : ℝ≥0) ^ ε' ≤ (a ^ ((2 : ℝ) ^ j)) ^ ε' := NNReal.rpow_le_rpow hjhi hε'.le
          _ = a ^ ((2 : ℝ) ^ j * ε') := by rw [← NNReal.rpow_mul]
          _ ≤ a ^ (128 * (2 : ℝ) ^ j * ε) :=
              NNReal.rpow_le_rpow_of_exponent_ge ha ha1' (by nlinarith)
      calc (δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε
          ≤ a ^ (128 * (2 : ℝ) ^ j * ε) * a ^ (4 * η) * a ^ ε := by gcongr
        _ = a ^ (128 * (2 : ℝ) ^ j * ε + 4 * η + ε) := by
            simp only [← NNReal.rpow_add ha.ne']
    have hmid : (a : ℝ≥0) ^ (128 * (2 : ℝ) ^ j * ε + 4 * η + ε)
        ≤ cBall * K₀ * K₀ * a ^ (10 * (2 : ℝ) ^ j * ε + 10 / 3 * η) := by
      have hsplit : (a : ℝ≥0) ^ (128 * (2 : ℝ) ^ j * ε + 4 * η + ε)
          = a ^ (118 * (2 : ℝ) ^ j * ε + 2 / 3 * η + ε)
            * a ^ (10 * (2 : ℝ) ^ j * ε + 10 / 3 * η) := by
        simp only [← NNReal.rpow_add ha.ne']
        congr 1
        ring
      rw [hsplit]
      gcongr
      calc (a : ℝ≥0) ^ (118 * (2 : ℝ) ^ j * ε + 2 / 3 * η + ε)
          ≤ a ^ (2 / 3 * η + ε) :=
            NNReal.rpow_le_rpow_of_exponent_ge ha ha1' (by nlinarith)
        _ ≤ cBall * K₀ * K₀ := habs2
    have hconst : (δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε
        ≤ cBall * (K₀ * a ^ E * ShadedBody.fullness s Y'')
            * (K₀ * a ^ E * ShadedBody.fullness s Y'')
            * a ^ (4 * η + 6 * (2 : ℝ) ^ j * ε) :=
      le_trans hLHS (le_trans hmid hBIG)
    -- radii
    intro x hx
    have hrad1 : ((θ * b : ℝ≥0) : ℝ) = ((θ : ℝ) * (b : ℝ)) := by push_cast; ring
    have hrad2 : ((Kakeya.plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ))
        = ((redPlankTube.ballDilation : ℝ) * (θ : ℝ) * (b : ℝ)) := by
      simp [Kakeya.plankReduction.ballDilation, redPlankTube.ballDilation]
      ring
    have hx' : ((⋃ i ∈ s, (ShadedBody.restrictShade (Y'' i) Gtot hGtot).shade) ∩
        Metric.closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty := by rwa [hrad1]
    have hgoal := hitem x hx'
    rw [hrad2, hrad1] at hgoal
    refine le_trans ?_ hgoal
    have hco : ((δ : ℝ≥0) ^ ε' : ℝ≥0) * (a : ℝ≥0) ^ (4 * η) * (a : ℝ≥0) ^ ε
        ≤ (cBall * (K₀ * a ^ E * ShadedBody.fullness s Y'')
            * (K₀ * a ^ E * ShadedBody.fullness s Y'')
            * a ^ (4 * η + 6 * (2 : ℝ) ^ j * ε) : ℝ≥0) := hconst
    have hEN : (((δ : ℝ≥0) ^ ε' : ℝ≥0) : ENNReal) * (a : ENNReal) ^ (4 * η)
          * (a : ENNReal) ^ ε
        ≤ ((cBall * (K₀ * a ^ E * ShadedBody.fullness s Y'')
            * (K₀ * a ^ E * ShadedBody.fullness s Y'')
            * a ^ (4 * η + 6 * (2 : ℝ) ^ j * ε) : ℝ≥0) : ENNReal) := by
      rw [show ((a : ENNReal) ^ (4 * η)) = (((a : ℝ≥0) ^ (4 * η) : ℝ≥0) : ENNReal) from
          (ENNReal.coe_rpow_of_nonneg _ (by positivity)).symm,
        show ((a : ENNReal) ^ ε) = (((a : ℝ≥0) ^ ε : ℝ≥0) : ENNReal) from
          (ENNReal.coe_rpow_of_nonneg _ hε.le).symm,
        ← ENNReal.coe_mul, ← ENNReal.coe_mul]
      exact ENNReal.coe_le_coe.mpr hco
    exact mul_le_mul_right' hEN _
  · rw [NNReal.rpow_neg]

end ShadedPlank

end
