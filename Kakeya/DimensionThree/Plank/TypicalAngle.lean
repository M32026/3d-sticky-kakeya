/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.AngleDef
public import Kakeya.Mathlib.Data.Nat.Log

/-!
# Selection refinement and the constant typical angle

This module, in namespace `Kakeya`, contains
the pointwise selection refinement, the dyadic angle-band helpers, and the constant-typical-angle /
constant-multiplicity refinement `constantTypicalAngle` together with the refinement-constant bound
`refineConst_bound`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real

noncomputable section

namespace Kakeya

variable {ι : Type*}

/-- **Pointwise selected fibres define a refinement (extra6, `lem:pointwiseSelectionRefinement`).**
Let `(𝒫, Y₁)` be a shaded family of planks indexed by a finite set `s`, and let
`G : Finset ι → Finset ι` be a *fibre-determined selection* with `G F ⊆ F`. The selected shading
`Y_sel(P i) = {x ∈ Y₁(P i) | i ∈ G(𝒫_{Y₁}(x))}` yields a `Y_sel` such that:
(i) `(𝒫, Y_sel)` is a refinement of `(𝒫, Y₁)`;
(ii) the new fibre is exactly the selection: `𝒫_{Y_sel}(x) = G(𝒫_{Y₁}(x))` for every `x`;
(iii) if `|G F| ≥ λ |F|` for every `F`, then `(𝒫, Y_sel)` is a `λ`-refinement of `(𝒫, Y₁)`. -/
theorem pointwiseSelectionRefinement
    (s : Finset ι) (Y₁ : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (G : Finset ι → Finset ι) (hG : ∀ F : Finset ι, G F ⊆ F) :
    ∃ Ysel : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)),
      (∀ i, (Ysel i).shade = {x ∈ (Y₁ i).shade | i ∈ G (shadeFibre s Y₁ x)}) ∧
      ShadedBody.IsRefinement s Ysel s Y₁ ∧
      (∀ x, shadeFibre s Ysel x = G (shadeFibre s Y₁ x)) ∧
      (∀ lam : ℝ≥0, (∀ F : Finset ι, (lam : ℝ) * (F.card : ℝ) ≤ ((G F).card : ℝ)) →
        ShadedBody.IsCRefinement s Ysel s Y₁ lam) := by
  classical
  -- Level sets of the fibre map, indexed by `F ⊆ s`.
  have hfib_subset : ∀ x, shadeFibre s Y₁ x ⊆ s := fun x => Finset.filter_subset _ _
  have hfib_mem : ∀ {x} {i}, i ∈ shadeFibre s Y₁ x ↔ i ∈ s ∧ x ∈ (Y₁ i).shade :=
    fun {x i} => mem_shadeFibre s Y₁ x i
  -- Measurability of each level set `{x | 𝒫_{Y₁}(x) = F}` (the standalone lemma).
  have hLset_meas : ∀ F : Finset ι,
      MeasurableSet {x : EuclideanSpace ℝ (Fin 3) | shadeFibre s Y₁ x = F} :=
    fun F => measurableSet_shadeFibre_eq s Y₁ F
  -- Measurability of each selected shading.
  have hsel_meas : ∀ i : ι,
      MeasurableSet {x ∈ (Y₁ i).shade | i ∈ G (shadeFibre s Y₁ x)} := by
    intro i
    have hmeas : Measurable (fun x => decide (i ∈ G (shadeFibre s Y₁ x))) :=
      measurable_fibreComp s Y₁ (fun F => decide (i ∈ G F))
    have heq : {x ∈ (Y₁ i).shade | i ∈ G (shadeFibre s Y₁ x)}
        = (Y₁ i).shade ∩ (fun x => decide (i ∈ G (shadeFibre s Y₁ x))) ⁻¹' {true} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        decide_eq_true_eq]
    rw [heq]
    exact (Y₁ i).measurableSet_shade.inter (hmeas (MeasurableSet.singleton true))
  -- The selected family.
  set Ysel : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i =>
    { (Y₁ i) with
      shade := {x ∈ (Y₁ i).shade | i ∈ G (shadeFibre s Y₁ x)}
      measurableSet_shade := hsel_meas i
      shade_subset := (Set.sep_subset _ _).trans (Y₁ i).shade_subset } with hYsel_def
  have hYsel_shade : ∀ i, (Ysel i).shade = {x ∈ (Y₁ i).shade | i ∈ G (shadeFibre s Y₁ x)} :=
    fun _ => rfl
  refine ⟨Ysel, fun _ => rfl,
    ⟨subset_rfl, fun i _ => ⟨rfl, by rw [hYsel_shade]; exact Set.sep_subset _ _⟩⟩, ?_, ?_⟩
  · -- Fibre identity.
    intro x
    ext i
    rw [mem_shadeFibre]
    constructor
    · rintro ⟨_, hx⟩; exact hx.2
    · intro hiG
      have hmem := hfib_mem.mp (hG _ hiG)
      exact ⟨hmem.1, hmem.2, hiG⟩
  · -- Mass bound.
    intro lam hlam
    refine ⟨⟨subset_rfl, fun i _ => ⟨rfl, Set.sep_subset _ _⟩⟩, ?_⟩
    -- Level-set volumes.
    set Lvol : Finset ι → ENNReal := fun F => volume {x : EuclideanSpace ℝ (Fin 3) |
      shadeFibre s Y₁ x = F} with hLvol
    have hLdisj : (↑(s.powerset) : Set (Finset ι)).PairwiseDisjoint
        (fun F => {x : EuclideanSpace ℝ (Fin 3) | shadeFibre s Y₁ x = F}) := by
      intro F _ F' _ hFF'
      refine Set.disjoint_left.2 fun x hxF hxF' => hFF' ?_
      simp only [Set.mem_setOf_eq] at hxF hxF'
      rw [← hxF, ← hxF']
    -- Each shading splits over the level sets it meets.
    have hsplit : ∀ (U : Set (EuclideanSpace ℝ (Fin 3))) (T : Finset ι → Prop) [DecidablePred T],
        U = ⋃ F ∈ s.powerset.filter T, {x : EuclideanSpace ℝ (Fin 3) | shadeFibre s Y₁ x = F} →
        volume U = ∑ F ∈ s.powerset.filter T, Lvol F := by
      intro U T _ hcov
      rw [hcov, measure_biUnion_finset
        (hLdisj.subset (by intro F hF; exact Finset.mem_coe.mpr (Finset.mem_of_mem_filter F hF)))
        (fun F _ => hLset_meas F)]
    -- The two mass expansions.
    have hY₁vol : ∀ i ∈ s, volume (Y₁ i).shade
        = ∑ F ∈ s.powerset.filter (fun F => i ∈ F), Lvol F := by
      intro i hi
      refine hsplit _ (fun F => i ∈ F) ?_
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · intro hx
        exact ⟨shadeFibre s Y₁ x, ⟨hfib_subset x, hfib_mem.mpr ⟨hi, hx⟩⟩, rfl⟩
      · rintro ⟨F, ⟨_, hiF⟩, hxF⟩
        exact (hfib_mem.mp (hxF ▸ hiF)).2
    have hYselvol : ∀ i ∈ s, volume (Ysel i).shade
        = ∑ F ∈ s.powerset.filter (fun F => i ∈ G F), Lvol F := by
      intro i hi
      rw [hYsel_shade i]
      refine hsplit _ (fun F => i ∈ G F) ?_
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨_, hiG⟩
        exact ⟨shadeFibre s Y₁ x, ⟨hfib_subset x, hiG⟩, rfl⟩
      · rintro ⟨F, ⟨_, hiGF⟩, hxF⟩
        exact ⟨(hfib_mem.mp (hxF ▸ Finset.mem_of_subset (hG F) hiGF)).2, hxF ▸ hiGF⟩
    -- Swap the order of summation and count.
    have hswap : ∀ (sel : Finset ι → Finset ι), (∀ F ∈ s.powerset, sel F ⊆ s) →
        ∑ i ∈ s, ∑ F ∈ s.powerset.filter (fun F => i ∈ sel F), Lvol F
          = ∑ F ∈ s.powerset, ((sel F).card : ENNReal) * Lvol F := by
      intro sel hsel
      calc ∑ i ∈ s, ∑ F ∈ s.powerset.filter (fun F => i ∈ sel F), Lvol F
          = ∑ i ∈ s, ∑ F ∈ s.powerset, if i ∈ sel F then Lvol F else 0 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_filter]
        _ = ∑ F ∈ s.powerset, ∑ i ∈ s, if i ∈ sel F then Lvol F else 0 := Finset.sum_comm
        _ = ∑ F ∈ s.powerset, ((sel F).card : ENNReal) * Lvol F := by
            refine Finset.sum_congr rfl fun F hF => ?_
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            congr 1
            rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hsel F hF)]
    -- Assemble.
    have e1 : ∑ i ∈ s, volume (Ysel i).shade
        = ∑ F ∈ s.powerset, ((G F).card : ENNReal) * Lvol F := by
      rw [← hswap (fun F => G F) (fun F hF => (hG F).trans (Finset.mem_powerset.mp hF))]
      exact Finset.sum_congr rfl hYselvol
    have e2 : ∑ i ∈ s, volume (Y₁ i).shade
        = ∑ F ∈ s.powerset, ((F.card : ℕ) : ENNReal) * Lvol F := by
      rw [← hswap (fun F => F) (fun F hF => Finset.mem_powerset.mp hF)]
      exact Finset.sum_congr rfl hY₁vol
    rw [e1, e2, Finset.mul_sum]
    refine Finset.sum_le_sum fun F _ => ?_
    rw [← mul_assoc]
    refine mul_le_mul_left ?_ (Lvol F)
    have hnn : (lam * F.card : ℝ≥0) ≤ ((G F).card : ℝ≥0) := by
      have := hlam F
      rw [← NNReal.coe_le_coe]; push_cast; linarith
    exact_mod_cast hnn

/-- Mass bound for a pointwise fibre selection.  This compatibility theorem exposes the
quantitative conclusion of `pointwiseSelectionRefinement` for an already constructed shading. -/
lemma sum_volume_shade_selection_ge (s : Finset ι)
    (Y₁ Ysel : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (G : Finset ι → Finset ι)
    (hG : ∀ F : Finset ι, G F ⊆ F)
    (hYsel : ∀ i, (Ysel i).shade = {x ∈ (Y₁ i).shade | i ∈ G (shadeFibre s Y₁ x)})
    (lam : ℝ≥0) (hlam : ∀ F : Finset ι, (lam : ℝ) * (F.card : ℝ) ≤ ((G F).card : ℝ)) :
    (lam : ENNReal) * ∑ i ∈ s, volume (Y₁ i).shade ≤
      ∑ i ∈ s, volume (Ysel i).shade := by
  obtain ⟨Z, hZ, _href, _hfibre, hmass⟩ := pointwiseSelectionRefinement s Y₁ G hG
  calc
    (lam : ENNReal) * ∑ i ∈ s, volume (Y₁ i).shade
        ≤ ∑ i ∈ s, volume (Z i).shade := (hmass lam hlam).2
    _ = ∑ i ∈ s, volume (Ysel i).shade := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hZ i, hYsel i]

/-- Dyadic angle band: for `0 < θ ≤ 1`, the dyadic level `j = ⌊log₂ ⌊θ⁻¹⌋⌋` satisfies
`θ ≤ (2 ^ j)⁻¹ ≤ 2 θ`, i.e. `(2 ^ j)⁻¹` is a factor-`2` approximation of `θ`. -/
private lemma dyadic_angle_band {θ : ℝ≥0} (hpos : 0 < θ) (hθ1 : θ ≤ 1) :
    θ ≤ ((2 : ℝ≥0) ^ Nat.log 2 ⌊(θ⁻¹ : ℝ≥0)⌋₊)⁻¹ ∧
      ((2 : ℝ≥0) ^ Nat.log 2 ⌊(θ⁻¹ : ℝ≥0)⌋₊)⁻¹ ≤ 2 * θ := by -- (extracted by Fuse golfer)
  set n : ℕ := ⌊(θ⁻¹ : ℝ≥0)⌋₊ with hn
  have hppos : (0:ℝ≥0) < (2:ℝ≥0) ^ Nat.log 2 n := by positivity
  have hone_le : (1 : ℝ≥0) ≤ θ⁻¹ := by
    simpa using (inv_le_inv₀ one_pos hpos).mpr hθ1
  have hnne : n ≠ 0 := by
    rw [hn]; exact Nat.one_le_iff_ne_zero.1 (Nat.le_floor (by exact_mod_cast hone_le))
  have hge : ((2 : ℝ≥0) ^ Nat.log 2 n) ≤ θ⁻¹ := by
    have h1 : ((2 : ℝ≥0) ^ Nat.log 2 n) ≤ (n : ℝ≥0) := by
      exact_mod_cast Nat.pow_log_le_self 2 hnne
    exact le_trans h1 (by rw [hn]; exact Nat.floor_le (by positivity))
  have hlt : θ⁻¹ < 2 * (2 : ℝ≥0) ^ Nat.log 2 n := by
    have hlt0 : n < (2 : ℕ) ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    calc θ⁻¹ < (n : ℝ≥0) + 1 := by rw [hn]; exact Nat.lt_floor_add_one _
      _ ≤ (2 : ℝ≥0) ^ (Nat.log 2 n + 1) := by
          rw [← Nat.cast_ofNat, ← Nat.cast_pow]; exact_mod_cast hlt0
      _ = 2 * (2 : ℝ≥0) ^ Nat.log 2 n := by rw [pow_succ]; ring
  refine ⟨?_, ?_⟩
  · rw [← inv_inv θ, inv_le_inv₀ (inv_pos.mpr hpos) hppos]; exact hge
  · rw [show ((2:ℝ≥0) ^ Nat.log 2 n)⁻¹ = 1 / (2:ℝ≥0) ^ Nat.log 2 n by rw [one_div],
      div_le_iff₀ hppos]
    have hmul := mul_lt_mul_of_pos_right hlt hpos
    rw [inv_mul_cancel₀ hpos.ne'] at hmul
    calc (1:ℝ≥0) ≤ 2 * (2:ℝ≥0) ^ Nat.log 2 n * θ := le_of_lt hmul
      _ = 2 * θ * (2:ℝ≥0) ^ Nat.log 2 n := by ring

/-- The joint dyadic-cell count `(⌊log₂⌊b/a⌋⌋ + 1)(⌊log₂ N⌋ + 1)` is bounded by the real
`(log(b/a)/log 2 + 2)(log N / log 2 + 1)`, so the reciprocal of the latter bounds `c` below. -/
private lemma le_bands_card_inv {a b : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (N : ℕ) :
    ((Real.log ((b : ℝ) / a) / Real.log 2 + 2) * (Real.log (N : ℝ) / Real.log 2 + 1))⁻¹
      ≤ (((Nat.log 2 ⌊(b / a : ℝ≥0)⌋₊ : ℝ) + 1) * ((Nat.log 2 N : ℝ) + 1))⁻¹ := by
        -- (extracted by Fuse golfer)
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hNatLog : ∀ n : ℕ, (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0; simp
    · rw [le_div_iff₀ hlog2]
      have h1 : (2:ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have h2 := Real.log_le_log (by positivity) h1
      rwa [Real.log_pow] at h2
  have hLbound : ((Nat.log 2 N : ℝ) + 1) ≤ Real.log (N : ℝ) / Real.log 2 + 1 := by
    linarith [hNatLog N]
  have hfloor1 : 1 ≤ ⌊(b / a : ℝ≥0)⌋₊ := by
    apply Nat.le_floor; rw [Nat.cast_one, le_div_iff₀ ha, one_mul]; exact hab
  have hJbound : ((Nat.log 2 ⌊(b / a : ℝ≥0)⌋₊ : ℝ) + 1)
      ≤ Real.log ((b : ℝ) / a) / Real.log 2 + 2 := by
    have hfloorle : (⌊(b / a : ℝ≥0)⌋₊ : ℝ) ≤ (b : ℝ) / a := by
      rw [← NNReal.coe_div]
      exact_mod_cast Nat.floor_le (show (0:ℝ≥0) ≤ b / a by positivity)
    have hdiv : (Nat.log 2 ⌊(b / a : ℝ≥0)⌋₊ : ℝ) ≤ Real.log ((b : ℝ) / a) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      calc (Nat.log 2 ⌊(b / a : ℝ≥0)⌋₊ : ℝ) * Real.log 2
          ≤ Real.log (⌊(b / a : ℝ≥0)⌋₊ : ℝ) := by
            rw [← le_div_iff₀ hlog2]; exact hNatLog _
        _ ≤ Real.log ((b : ℝ) / a) := Real.log_le_log (by exact_mod_cast hfloor1) hfloorle
    linarith
  have hf2pos : (0:ℝ) < Real.log (N : ℝ) / Real.log 2 + 1 :=
    lt_of_lt_of_le (by positivity) hLbound
  have hf1pos : (0:ℝ) < Real.log ((b : ℝ) / a) / Real.log 2 + 2 :=
    lt_of_lt_of_le (by positivity) hJbound
  exact (inv_le_inv₀ (mul_pos hf1pos hf2pos) (by positivity)).mpr
    (mul_le_mul hJbound hLbound (by positivity) hf1pos.le)

/-- **Constant typical angle and multiplicity after refinement**
(extra6, `lem:constantTypicalAngle`).
Let `(𝒫, Yₐ)` be a shaded family of planks indexed by a finite set `s`, and suppose the typical
angle is *fibre-determined* by `Θ : Finset ι → ℝ≥0` with `Θ(𝒫_{Yₐ}(x)) ∈ [a/b, 1]` on
`U(𝒫, Yₐ)`. Then there is a `⪆ 1` refinement `(𝒫, Y')` (the loss `c` is at least the reciprocal of
the joint dyadic-cell count, i.e. sub-polynomial in `a` and `|s|`) and a single `θ ∈ [a/b, 1]` with
(i) `θ(x) ∼ θ` (within the absolute factor `2`) on `U(𝒫, Y')`, and
(ii) `(𝒫, Y')` has constant multiplicity with the absolute factor `2`.
The fibre is unchanged on `U(𝒫, Y')`, so `Θ(𝒫_{Y'}(x)) = Θ(𝒫_{Yₐ}(x))`. -/
theorem constantTypicalAngle
    (s : Finset ι) (Ya : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {a b : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (_hb1 : b ≤ 1)
    (Θ : Finset ι → ℝ≥0)
    (hΘlb : ∀ x ∈ ⋃ i ∈ s, (Ya i).shade, a / b ≤ Θ (shadeFibre s Ya x))
    (hΘub : ∀ x ∈ ⋃ i ∈ s, (Ya i).shade, Θ (shadeFibre s Ya x) ≤ 1) :
    ∃ (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (θ : ℝ≥0) (c : ℝ≥0),
      0 < c ∧
      ((Real.log ((b : ℝ) / a) / Real.log 2 + 2)
          * (Real.log (s.card : ℝ) / Real.log 2 + 1))⁻¹ ≤ (c : ℝ) ∧
      ShadedBody.IsCRefinement s Y' s Ya c ∧
      a / b ≤ θ ∧ θ ≤ 1 ∧
      ShadedBody.HasCConstantMultiplicity s Y' 2 ∧
      (∀ x ∈ ⋃ i ∈ s, (Y' i).shade, shadeFibre s Y' x = shadeFibre s Ya x) ∧
      (∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
        Θ (shadeFibre s Y' x) ≤ θ ∧ θ ≤ 2 * Θ (shadeFibre s Y' x)) := by
  classical
  have hbpos : (0:ℝ≥0) < b := lt_of_lt_of_le ha hab
  have hab_pos : (0:ℝ≥0) < a / b := div_pos ha hbpos
  -- Joint (angle, cardinality) band, fibre-determined.
  set band : EuclideanSpace ℝ (Fin 3) → ℕ × ℕ :=
    fun x => (Nat.log 2 ⌊((Θ (shadeFibre s Ya x))⁻¹ : ℝ≥0)⌋₊, Nat.log 2 (shadeFibre s Ya x).card)
    with hband
  have hband_meas : Measurable band :=
    measurable_fibreComp s Ya (fun F => (Nat.log 2 ⌊((Θ F)⁻¹ : ℝ≥0)⌋₊, Nat.log 2 F.card))
  set J : ℕ := Nat.log 2 ⌊((b / a : ℝ≥0))⌋₊ with hJ
  set L : ℕ := Nat.log 2 s.card with hL
  set Bands : Finset (ℕ × ℕ) := Finset.range (J + 1) ×ˢ Finset.range (L + 1) with hBands
  set X : ℕ × ℕ → Set (EuclideanSpace ℝ (Fin 3)) := fun p => band ⁻¹' {p} with hX
  have hX_meas : ∀ p, MeasurableSet (X p) := fun p => hband_meas (MeasurableSet.singleton p)
  have hBands_ne : Bands.Nonempty :=
    Finset.Nonempty.product ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
      ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
  have hX_disj : (↑Bands : Set (ℕ × ℕ)).PairwiseDisjoint X := by
    intro p _ q _ hpq
    refine Set.disjoint_left.2 fun x hxp hxq => hpq ?_
    have h1 : band x = p := hxp
    have h2 : band x = q := hxq
    rw [← h1, ← h2]
  -- Each point's band lies in `Bands`.
  have hsfsub : ∀ x, shadeFibre s Ya x ⊆ s := fun x => Finset.filter_subset _ _
  have hbandB : ∀ x ∈ (⋃ i ∈ s, (Ya i).shade), band x ∈ Bands := by
    intro x hx
    rw [hBands, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    have hΘl : a / b ≤ Θ (shadeFibre s Ya x) := hΘlb x hx
    refine ⟨?_, ?_⟩
    · rw [hband]
      simp only [Nat.lt_succ_iff, hJ]
      refine Nat.log_mono_right (Nat.floor_le_floor ?_)
      rw [show (b / a : ℝ≥0) = (a / b)⁻¹ by rw [inv_div]]
      exact (inv_le_inv₀ (lt_of_lt_of_le hab_pos hΘl) hab_pos).mpr hΘl
    · rw [hband]
      simp only [Nat.lt_succ_iff, hL]
      exact Nat.log_mono_right (Finset.card_le_card (hsfsub x))
  -- Mass splits over the bands.
  have hsplit : ∀ i ∈ s,
      volume (Ya i).shade = ∑ p ∈ Bands, volume ((Ya i).shade ∩ X p) := by
    intro i hi
    have hd : (↑Bands : Set (ℕ × ℕ)).PairwiseDisjoint (fun p => (Ya i).shade ∩ X p) :=
      fun p hp q hq hpq =>
        (hX_disj hp hq hpq).mono Set.inter_subset_right Set.inter_subset_right
    have hm : ∀ p ∈ Bands, MeasurableSet ((Ya i).shade ∩ X p) :=
      fun p _ => (Ya i).measurableSet_shade.inter (hX_meas p)
    have hunion : (⋃ p ∈ Bands, ((Ya i).shade ∩ X p)) = (Ya i).shade := by
      apply Set.Subset.antisymm
      · exact Set.iUnion₂_subset fun p _ => Set.inter_subset_left
      · intro x hx
        exact Set.mem_iUnion₂.2 ⟨band x, hbandB x (Set.mem_iUnion₂.2 ⟨i, hi, hx⟩), hx, rfl⟩
    conv_lhs => rw [← hunion]
    rw [measure_biUnion_finset hd hm]
  have hT : (∑ i ∈ s, volume (Ya i).shade)
      = ∑ p ∈ Bands, ∑ i ∈ s, volume ((Ya i).shade ∩ X p) := by
    calc ∑ i ∈ s, volume (Ya i).shade
        = ∑ i ∈ s, ∑ p ∈ Bands, volume ((Ya i).shade ∩ X p) := Finset.sum_congr rfl hsplit
      _ = ∑ p ∈ Bands, ∑ i ∈ s, volume ((Ya i).shade ∩ X p) := Finset.sum_comm
  obtain ⟨p0, hp0B, hp0max⟩ :=
    Finset.exists_max_image Bands (fun p => ∑ i ∈ s, volume ((Ya i).shade ∩ X p)) hBands_ne
  have hsum_le : (∑ i ∈ s, volume (Ya i).shade)
      ≤ Bands.card • ∑ i ∈ s, volume ((Ya i).shade ∩ X p0) := by
    rw [hT]
    exact Finset.sum_le_card_nsmul Bands _ _ fun p hp => hp0max p hp
  -- The refinement: restrict to the chosen cell.
  set V' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i =>
    { Ya i with
      shade := (Ya i).shade ∩ X p0
      measurableSet_shade := (Ya i).measurableSet_shade.inter (hX_meas p0)
      shade_subset := Set.inter_subset_left.trans (Ya i).shade_subset } with hV'
  have hV'shade : ∀ i, (V' i).shade = (Ya i).shade ∩ X p0 := fun _ => rfl
  -- On `U(V')` the band is `p0` and the fibre is unchanged.
  have hbandeq : ∀ x ∈ (⋃ i ∈ s, (V' i).shade), band x = p0 := by
    intro x hx
    obtain ⟨i, _, hix⟩ := Set.mem_iUnion₂.1 hx
    rw [hV'shade] at hix
    exact hix.2
  have hxU : ∀ x ∈ (⋃ i ∈ s, (V' i).shade), x ∈ ⋃ i ∈ s, (Ya i).shade := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.1 hx
    rw [hV'shade] at hix
    exact Set.mem_iUnion₂.2 ⟨i, hi, hix.1⟩
  have hfibre_eq : ∀ x ∈ (⋃ i ∈ s, (V' i).shade), shadeFibre s V' x = shadeFibre s Ya x := by
    intro x hx
    obtain ⟨i, _, hix⟩ := Set.mem_iUnion₂.1 hx
    rw [hV'shade] at hix
    ext k
    rw [mem_shadeFibre, mem_shadeFibre]
    refine ⟨fun ⟨hks, hk⟩ => ⟨hks, ?_⟩, fun ⟨hks, hk⟩ => ⟨hks, ?_⟩⟩
    · rw [hV'shade] at hk; exact hk.1
    · rw [hV'shade]; exact ⟨hk, hix.2⟩
  -- The typical angle.
  set θ : ℝ≥0 := (a / b) ⊔ ((2 : ℝ≥0) ^ p0.1)⁻¹ with hθ
  -- Angle-band bounds at points of `U(V')`.
  have hΘbound : ∀ x ∈ (⋃ i ∈ s, (V' i).shade),
      Θ (shadeFibre s Ya x) ≤ ((2 : ℝ≥0) ^ p0.1)⁻¹ ∧
        ((2 : ℝ≥0) ^ p0.1)⁻¹ ≤ 2 * Θ (shadeFibre s Ya x) := by
    intro x hx
    have hxinU := hxU x hx
    have habx : Nat.log 2 ⌊((Θ (shadeFibre s Ya x))⁻¹ : ℝ≥0)⌋₊ = p0.1 := by
      have := congrArg Prod.fst (hbandeq x hx); rwa [hband] at this
    rw [← habx]
    exact dyadic_angle_band (lt_of_lt_of_le hab_pos (hΘlb x hxinU)) (hΘub x hxinU)
  -- The retained fraction.
  set c : ℝ≥0 := ((Bands.card : ℝ≥0))⁻¹ with hc
  have hNne : (Bands.card : ℝ≥0) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hBands_ne
  have hNpos : (0:ℝ≥0) < (Bands.card : ℝ≥0) := pos_iff_ne_zero.mpr hNne
  refine ⟨V', θ, c, ?_, ?_,
    ⟨⟨subset_rfl, fun i _ => ⟨rfl, by rw [hV'shade]; exact Set.inter_subset_left⟩⟩, ?_⟩,
    le_sup_left, ?_, ?_, hfibre_eq, ?_⟩
  · -- `0 < c`.
    rw [hc]; exact inv_pos.mpr hNpos
  · -- The quantitative lower bound on `c`, via `le_bands_card_inv`.
    rw [show (c : ℝ) = ((Bands.card : ℝ))⁻¹ by rw [hc, NNReal.coe_inv]; norm_cast,
      show (Bands.card : ℝ)
          = ((Nat.log 2 ⌊(b / a : ℝ≥0)⌋₊ : ℝ) + 1) * ((Nat.log 2 s.card : ℝ) + 1) by
        rw [hBands, Finset.card_product, Finset.card_range, Finset.card_range, hJ, hL]
        push_cast; ring]
    exact le_bands_card_inv ha hab s.card
  · -- Mass bound for the refinement, via `ennreal_natinv_mul_le`.
    rw [show (c : ENNReal) = ((Bands.card : ENNReal))⁻¹ by
      rw [hc, ENNReal.coe_inv hNne, ENNReal.coe_natCast]]
    refine ennreal_natinv_mul_le (Finset.card_ne_zero.mpr hBands_ne) ?_
    have heq : ∑ i ∈ s, volume (V' i).shade = ∑ i ∈ s, volume ((Ya i).shade ∩ X p0) :=
      Finset.sum_congr rfl fun i _ => by rw [hV'shade]
    rw [heq, ← nsmul_eq_mul]; exact hsum_le
  · -- `θ ≤ 1`.
    rw [hθ]
    refine sup_le (div_le_one_of_le hab) ?_
    rw [inv_le_one₀ (by positivity)]
    exact one_le_pow₀ (by norm_num)
  · -- Constant multiplicity (factor `2`).
    intro x hx y hy
    set Fx : Finset ι := shadeFibre s Ya x with hFx
    set Fy : Finset ι := shadeFibre s Ya y with hFy
    have hcardx : Nat.log 2 Fx.card = p0.2 := by
      rw [hFx]; have := congrArg Prod.snd (hbandeq x hx); rwa [hband] at this
    have hcardy : Nat.log 2 Fy.card = p0.2 := by
      rw [hFy]; have := congrArg Prod.snd (hbandeq y hy); rwa [hband] at this
    have hpmx : ShadedBody.pointwiseMultiplicity s V' x = Fx.card := by
      rw [hFx, ← hfibre_eq x hx]; rfl
    have hpmy : ShadedBody.pointwiseMultiplicity s V' y = Fy.card := by
      rw [hFy, ← hfibre_eq y hy]; rfl
    have hxne : Fx.card ≠ 0 := by
      rw [hFx]
      obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.1 hx
      rw [hV'shade] at hix
      exact Finset.card_ne_zero.2 ⟨i, (mem_shadeFibre s Ya x i).2 ⟨hi, hix.1⟩⟩
    have hyne : Fy.card ≠ 0 := by
      rw [hFy]
      obtain ⟨i, hi, hiy⟩ := Set.mem_iUnion₂.1 hy
      rw [hV'shade] at hiy
      exact Finset.card_ne_zero.2 ⟨i, (mem_shadeFibre s Ya y i).2 ⟨hi, hiy.1⟩⟩
    have hle : Fx.card ≤ 2 * Fy.card :=
      Kakeya.le_two_mul_of_log_two_eq hyne (hcardx.trans hcardy.symm)
    rw [hpmx, hpmy]; exact_mod_cast hle
  · -- `Θ` comparability with `θ`.
    intro x hx
    rw [hfibre_eq x hx]
    have hb := hΘbound x hx
    refine ⟨le_trans hb.1 le_sup_right, ?_⟩
    rw [hθ]
    refine sup_le ?_ hb.2
    have hΘl : a / b ≤ Θ (shadeFibre s Ya x) := hΘlb x (hxU x hx)
    calc a / b ≤ Θ (shadeFibre s Ya x) := hΘl
      _ ≤ 2 * Θ (shadeFibre s Ya x) := by
          rw [two_mul]; exact le_add_self

/-- The refinement-constant bound for GWZ Lemma 6.11, isolated so it elaborates in a small
context. Using the polynomial plank-count bound `hcard` (and the cell-count bound `hc2` from
`constantTypicalAngle`), the quantity `a^ε · c2⁻¹ · B · (⌊log₂ sc⌋+1)` is bounded by a single
`a`-independent constant: `B`, the two `log`-cell factors and the dyadic count are each
sub-polynomial (`≤ Kᵢ · a^(-ε/4)`), so their product times `a^ε` is a constant. This is where
`hcard` is genuinely used to control the `≈ 1` refinement constant.

(No longer `private`: it is consumed by `findingTypicalAngleOfIntersection` in the downstream file
`Kakeya.DimensionThree.Plank.TypicalAngleIncidence`.) -/
lemma refineConst_bound {a b : ℝ≥0} (ha : 0 < a) (ha1 : a < 1) (hab : a ≤ b)
    (hb1 : b ≤ 1) {ε : ℝ} (hε : 0 < ε) {C₀ : ℝ≥0} {N : ℝ} (sc : ℕ)
    (hcard : (sc : ℝ) ≤ (C₀ : ℝ) * (a : ℝ) ^ (-N)) {c2 : ℝ} (hc2pos : 0 < c2)
    (hc2 : ((Real.log ((b : ℝ) / a) / Real.log 2 + 2) * (Real.log (sc : ℝ) / Real.log 2 + 1))⁻¹
        ≤ c2) :
    ∃ K : ℝ, 0 ≤ K ∧
      (a : ℝ) ^ ε * (c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ)) ≤ K := by
  have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have ha1R : (a:ℝ) < 1 := by exact_mod_cast ha1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDβpos : (0:ℝ) < (a:ℝ) ^ (-(ε/4)) := Real.rpow_pos_of_pos haR _
  obtain ⟨Cβ, hCβpos, hCβ⟩ :=
    subpolyExp (show (0:ℝ) ≤ 3/4 by norm_num) (show (3/4:ℝ) < 1 by norm_num)
      (show (0:ℝ) < ε / 4 by linarith)
  obtain ⟨K1, hK1⟩ := logarg_subpoly (show (0:ℝ) ≤ 2 by norm_num) (show (0:ℝ) < ε/4 by linarith)
  obtain ⟨K2, hK2⟩ := logarg_subpoly (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) < ε/4 by linarith)
  set f1 : ℝ := Real.log ((b:ℝ)/a)/Real.log 2 + 2 with hf1def
  set f2 : ℝ := Real.log (sc:ℝ)/Real.log 2 + 1 with hf2def
  have hba1 : (1:ℝ) ≤ (b:ℝ)/a := by rw [le_div_iff₀ haR, one_mul]; exact_mod_cast hab
  have hf1pos : 0 < f1 := by
    have h0 := div_nonneg (Real.log_nonneg hba1) hlog2.le; rw [hf1def]; linarith
  have hf2pos : 0 < f2 := by
    rcases Nat.eq_zero_or_pos sc with h0 | hpos
    · simp [hf2def, h0]
    · have h0 := div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hpos)) hlog2.le
      rw [hf2def]; linarith
  have hc2inv : c2⁻¹ ≤ f1 * f2 := by
    rw [← inv_inv (f1 * f2)]
    exact (inv_le_inv₀ hc2pos (inv_pos.mpr (mul_pos hf1pos hf2pos))).mpr hc2
  have hBβ : plankAngleScaleB a ≤ Cβ * (a:ℝ) ^ (-(ε/4)) := hCβ (a:ℝ) haR ha1R
  have hf1β : f1 ≤ K1 * (a:ℝ) ^ (-(ε/4)) := by
    refine hK1 (a:ℝ) ((b:ℝ)/a) haR ha1R.le (le_trans zero_le_one hba1) ?_
    rw [one_mul, Real.rpow_neg_one, div_le_iff₀ haR, inv_mul_eq_div, le_div_iff₀ haR]
    calc (b:ℝ) * a ≤ 1 * a := mul_le_mul (by exact_mod_cast hb1) le_rfl haR.le zero_le_one
      _ = (a:ℝ) := one_mul _
  have hf2β : f2 ≤ K2 * (a:ℝ) ^ (-(ε/4)) :=
    hK2 (a:ℝ) (sc:ℝ) haR ha1R.le (by positivity) hcard
  have hk1β : ((Nat.log 2 sc + 1 : ℕ) : ℝ) ≤ K2 * (a:ℝ) ^ (-(ε/4)) := by
    refine le_trans ?_ hf2β
    push_cast
    rcases Nat.eq_zero_or_pos sc with h0 | hpos
    · simp [hf2def, h0]
    · rw [hf2def]
      have hNlog : (Nat.log 2 sc : ℝ) ≤ Real.log (sc:ℝ) / Real.log 2 := by
        rw [le_div_iff₀ hlog2]
        have h1 : (2:ℝ) ^ (Nat.log 2 sc) ≤ (sc:ℝ) := by
          exact_mod_cast Nat.pow_log_le_self 2 hpos.ne'
        have := Real.log_le_log (by positivity) h1
        rwa [Real.log_pow] at this
      linarith
  have hK1pos : 0 < K1 := by nlinarith [lt_of_lt_of_le hf1pos hf1β, hDβpos]
  have hK2pos : 0 < K2 := by nlinarith [lt_of_lt_of_le hf2pos hf2β, hDβpos]
  have hcombine : (a:ℝ) ^ ε * ((a:ℝ) ^ (-(ε/4)) * (a:ℝ) ^ (-(ε/4)) * (a:ℝ) ^ (-(ε/4))
      * (a:ℝ) ^ (-(ε/4))) = 1 := by
    rw [← Real.rpow_add haR, ← Real.rpow_add haR, ← Real.rpow_add haR,
      ← Real.rpow_add haR]
    rw [show ε + (-(ε / 4) + -(ε / 4) + -(ε / 4) + -(ε / 4)) = 0 by ring, Real.rpow_zero]
  have hBpos0 : (0:ℝ) < plankAngleScaleB a := by rw [plankAngleScaleB]; exact Real.exp_pos _
  have hc2inv' : c2⁻¹ ≤ (K1 * (a:ℝ) ^ (-(ε/4))) * (K2 * (a:ℝ) ^ (-(ε/4))) :=
    le_trans hc2inv (mul_le_mul hf1β hf2β hf2pos.le (by positivity))
  have hX : c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ)
      ≤ (K1 * (a:ℝ) ^ (-(ε/4))) * (K2 * (a:ℝ) ^ (-(ε/4))) * (Cβ * (a:ℝ) ^ (-(ε/4)))
        * (K2 * (a:ℝ) ^ (-(ε/4))) :=
    mul_le_mul (mul_le_mul hc2inv' hBβ hBpos0.le (by positivity)) hk1β (by positivity)
      (by positivity)
  refine ⟨K1 * K2 * Cβ * K2, le_of_lt (by positivity), ?_⟩
  calc (a:ℝ) ^ ε * (c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ))
      ≤ (a:ℝ) ^ ε * ((K1 * (a:ℝ) ^ (-(ε/4))) * (K2 * (a:ℝ) ^ (-(ε/4))) * (Cβ * (a:ℝ) ^ (-(ε/4)))
          * (K2 * (a:ℝ) ^ (-(ε/4)))) :=
        mul_le_mul_of_nonneg_left hX (le_of_lt (Real.rpow_pos_of_pos haR ε))
    _ = (K1 * K2 * Cβ * K2)
          * ((a:ℝ) ^ ε * ((a:ℝ) ^ (-(ε/4)) * (a:ℝ) ^ (-(ε/4)) * (a:ℝ) ^ (-(ε/4))
            * (a:ℝ) ^ (-(ε/4)))) := by ring
    _ = K1 * K2 * Cβ * K2 := by rw [hcombine, mul_one]

/-- **The refinement-constant bound with the constant bound *before* the configuration.**

This is `refineConst_bound` with the quantifiers in the honest order.  The constant produced there
is `K = K₁ · K₂ · C_β · K₂`, where `C_β` and `K₁` depend only on `ε` (they come from
`Kakeya.subpolyExp` at `α = 3/4` and from `Kakeya.logarg_subpoly` at `M = N = 1`, `r = 2`), and
`K₂` comes from `Kakeya.logarg_subpoly` at `M = C₀`, `N = Nexp`, `r = 1`.  So `K` depends only on
`(ε, C₀, Nexp)` and not on `a`, `b`, `sc` or `c2`; stating it that way is what lets GWZ Lemma 6.11
bind its refinement constant before the finite
configuration, and hence lets the refinement loss of GWZ Lemma 6.11 be a genuine explicit
`C⁻¹ · a ^ ε` rather than an unconstrained positive existential. -/
lemma refineConst_bound_uniform {ε : ℝ} (hε : 0 < ε) (C₀ : ℝ≥0) (Nexp : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {a b : ℝ≥0}, 0 < a → a < 1 → a ≤ b → b ≤ 1 →
        ∀ sc : ℕ, (sc : ℝ) ≤ (C₀ : ℝ) * (a : ℝ) ^ (-Nexp) →
          ∀ {c2 : ℝ}, 0 < c2 →
            ((Real.log ((b : ℝ) / a) / Real.log 2 + 2)
                * (Real.log (sc : ℝ) / Real.log 2 + 1))⁻¹ ≤ c2 →
            (a : ℝ) ^ ε * (c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ)) ≤ K := by
  obtain ⟨Cβ, hCβpos, hCβ⟩ :=
    subpolyExp (show (0:ℝ) ≤ 3/4 by norm_num) (show (3/4:ℝ) < 1 by norm_num)
      (show (0:ℝ) < ε/4 by linarith)
  obtain ⟨K1, hK1⟩ := logarg_subpoly (M := 1) (N := 1) (r := 2) (show (0:ℝ) ≤ 2 by norm_num)
    (show (0:ℝ) < ε/4 by linarith)
  obtain ⟨K2, hK2⟩ := logarg_subpoly (M := (C₀ : ℝ)) (N := Nexp) (r := 1) (show (0:ℝ) ≤ 1 by
      norm_num)
    (show (0:ℝ) < ε/4 by linarith)
  have hK1pos : 0 < K1 := by
    have h := hK1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h1rpow : (1 : ℝ) ^ (-(ε/4)) = 1 := Real.one_rpow _
    have hlog1 : Real.log (1 : ℝ) = 0 := Real.log_one
    rw [hlog1, h1rpow] at h
    norm_num at h
    linarith
  have hK2pos : 0 < K2 := by
    have hC0_nonneg : 0 ≤ (C₀ : ℝ) := NNReal.coe_nonneg _
    have h_mul : 0 ≤ (C₀ : ℝ) * (1 : ℝ) ^ (-Nexp) := by
      have h1rpow' : (1 : ℝ) ^ (-Nexp) = 1 := Real.one_rpow _
      rw [h1rpow']
      nlinarith
    have h := hK2 1 0 (by norm_num) (by norm_num) (by norm_num) h_mul
    have h1rpow : (1 : ℝ) ^ (-(ε/4)) = 1 := Real.one_rpow _
    have hlog0 : Real.log (0 : ℝ) = 0 := Real.log_zero
    rw [hlog0, h1rpow] at h
    norm_num at h
    linarith
  refine ⟨K1 * K2 * Cβ * K2, le_of_lt (by positivity), ?_⟩
  intro a b ha ha1 hab hb1 sc hcard c2 hc2pos hc2
  -- The rest is verbatim from `refineConst_bound` after its own `obtain` statements.
  have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have ha1R : (a:ℝ) < 1 := by exact_mod_cast ha1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDβpos : (0:ℝ) < (a:ℝ) ^ (-(ε/4)) := Real.rpow_pos_of_pos haR _
  set f1 : ℝ := Real.log ((b:ℝ)/a)/Real.log 2 + 2 with hf1def
  set f2 : ℝ := Real.log (sc:ℝ)/Real.log 2 + 1 with hf2def
  have hba1 : (1:ℝ) ≤ (b:ℝ)/a := by rw [le_div_iff₀ haR, one_mul]; exact_mod_cast hab
  have hf1pos : 0 < f1 := by
    have h0 := div_nonneg (Real.log_nonneg hba1) hlog2.le; rw [hf1def]; linarith
  have hf2pos : 0 < f2 := by
    rcases Nat.eq_zero_or_pos sc with h0 | hpos
    · simp [hf2def, h0]
    · have h0 := div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hpos)) hlog2.le
      rw [hf2def]; linarith
  have hc2inv : c2⁻¹ ≤ f1 * f2 := by
    rw [← inv_inv (f1 * f2)]
    exact (inv_le_inv₀ hc2pos (inv_pos.mpr (mul_pos hf1pos hf2pos))).mpr hc2
  have hBβ : plankAngleScaleB a ≤ Cβ * (a:ℝ) ^ (-(ε/4)) := hCβ (a:ℝ) haR ha1R
  have hf1β : f1 ≤ K1 * (a:ℝ) ^ (-(ε/4)) := by
    refine hK1 (a:ℝ) ((b:ℝ)/a) haR ha1R.le (le_trans zero_le_one hba1) ?_
    rw [one_mul, Real.rpow_neg_one, div_le_iff₀ haR, inv_mul_eq_div, le_div_iff₀ haR]
    calc (b:ℝ) * a ≤ 1 * a := mul_le_mul (by exact_mod_cast hb1) le_rfl haR.le zero_le_one
      _ = (a:ℝ) := one_mul _
  have hf2β : f2 ≤ K2 * (a:ℝ) ^ (-(ε/4)) :=
    hK2 (a:ℝ) (sc:ℝ) haR ha1R.le (by positivity) hcard
  have hk1β : ((Nat.log 2 sc + 1 : ℕ) : ℝ) ≤ K2 * (a:ℝ) ^ (-(ε/4)) := by
    refine le_trans ?_ hf2β
    push_cast
    rcases Nat.eq_zero_or_pos sc with h0 | hpos
    · simp [hf2def, h0]
    · rw [hf2def]
      have hNlog : (Nat.log 2 sc : ℝ) ≤ Real.log (sc:ℝ) / Real.log 2 := by
        rw [le_div_iff₀ hlog2]
        have h1 : (2:ℝ) ^ (Nat.log 2 sc) ≤ (sc:ℝ) := by
          exact_mod_cast Nat.pow_log_le_self 2 hpos.ne'
        have := Real.log_le_log (by positivity) h1
        rwa [Real.log_pow] at this
      linarith
  have hK1pos' : 0 < K1 := hK1pos
  have hK2pos' : 0 < K2 := hK2pos
  have hcombine : (a:ℝ) ^ ε * ((a:ℝ) ^ (-(ε/4)) * (a:ℝ) ^ (-(ε/4)) * (a:ℝ) ^ (-(ε/4))
      * (a:ℝ) ^ (-(ε/4))) = 1 := by
    rw [← Real.rpow_add haR, ← Real.rpow_add haR, ← Real.rpow_add haR,
      ← Real.rpow_add haR]
    rw [show ε + (-(ε / 4) + -(ε / 4) + -(ε / 4) + -(ε / 4)) = 0 by ring, Real.rpow_zero]
  have hBpos0 : (0:ℝ) < plankAngleScaleB a := by rw [plankAngleScaleB]; exact Real.exp_pos _
  have hc2inv' : c2⁻¹ ≤ (K1 * (a:ℝ) ^ (-(ε/4))) * (K2 * (a:ℝ) ^ (-(ε/4))) :=
    le_trans hc2inv (mul_le_mul hf1β hf2β hf2pos.le (by positivity))
  have hX : c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ)
      ≤ (K1 * (a:ℝ) ^ (-(ε/4))) * (K2 * (a:ℝ) ^ (-(ε/4))) * (Cβ * (a:ℝ) ^ (-(ε/4)))
        * (K2 * (a:ℝ) ^ (-(ε/4))) :=
    mul_le_mul (mul_le_mul hc2inv' hBβ hBpos0.le (by positivity)) hk1β (by positivity)
      (by positivity)
  calc (a:ℝ) ^ ε * (c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ))
      ≤ (a:ℝ) ^ ε * ((K1 * (a:ℝ) ^ (-(ε/4))) * (K2 * (a:ℝ) ^ (-(ε/4))) * (Cβ * (a:ℝ) ^ (-(ε/4)))
          * (K2 * (a:ℝ) ^ (-(ε/4)))) :=
        mul_le_mul_of_nonneg_left hX (le_of_lt (Real.rpow_pos_of_pos haR ε))
    _ = (K1 * K2 * Cβ * K2)
          * ((a:ℝ) ^ ε * ((a:ℝ) ^ (-(ε/4)) * (a:ℝ) ^ (-(ε/4)) * (a:ℝ) ^ (-(ε/4))
            * (a:ℝ) ^ (-(ε/4)))) := by ring
    _ = K1 * K2 * Cβ * K2 := by rw [hcombine, mul_one]

/-- **The refinement-constant bound with the reserve retention loss** (extra69,
`rem:refineConstBoundUniformReserve`).

Exactly `Kakeya.refineConst_bound_uniform` with the single factor `plankAngleScaleB a` replaced by
`plankAngleScaleB a * plankReserveLoss kappa a`, and with the constant still fixed before the
configuration and still depending only on `(kappa, ε, C₀, Nexp)`.

This is the refinement bookkeeping of
`Kakeya.findingTypicalAngleOfIntersection_stable_reserve`.  Running the per-fibre stopping-time
selection at the reserve scale `Kakeya.plankReserveScale kappa a`
(`Kakeya.typicalAngleFibre_reserve`) costs the extra factor `Kakeya.plankReserveLoss kappa a`
in the retained fraction of the selected sub-fibre, and nothing else; that factor is still
sub-polynomial, so the loss is absorbed by a larger
uniform constant.  The proof splits `a ^ ε = a ^ (ε/2) · a ^ (ε/2)` and spends one half on
`Kakeya.refineConst_bound_uniform` at `ε / 2` and the other on
`Kakeya.plankReserveLoss_le_rpow` at `ε / 2`; only one split is needed, because
`plankReserveLoss` already packages both the `kappa`-dependent constant and the extra
`plankAngleScaleA a * plankAngleScaleB a`.

No hypothesis on `kappa` is needed: only the sub-polynomiality and positivity of
`plankReserveLoss kappa a` are used, both of which hold for every real `kappa`.  The reserve route
instantiates this at `kappa ≥ 1`. -/
lemma refineConst_bound_uniform_reserve (kappa : ℝ) {ε : ℝ} (hε : 0 < ε)
    (C₀ : ℝ≥0) (Nexp : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {a b : ℝ≥0}, 0 < a → a < 1 → a ≤ b → b ≤ 1 →
        ∀ sc : ℕ, (sc : ℝ) ≤ (C₀ : ℝ) * (a : ℝ) ^ (-Nexp) →
          ∀ {c2 : ℝ}, 0 < c2 →
            ((Real.log ((b : ℝ) / a) / Real.log 2 + 2)
                * (Real.log (sc : ℝ) / Real.log 2 + 1))⁻¹ ≤ c2 →
            (a : ℝ) ^ ε * (c2⁻¹ * (plankAngleScaleB a * plankReserveLoss kappa a)
                * ((Nat.log 2 sc + 1 : ℕ) : ℝ)) ≤ K := by
  have hε2 : 0 < ε/2 := by linarith
  have h_ε2_nonpos : -(ε/2 : ℝ) ≤ 0 := by nlinarith
  obtain ⟨K_small, hK_small_nonneg, hK_small⟩ :=
    refineConst_bound_uniform (show (0:ℝ) < ε/2 from hε2) C₀ Nexp
  obtain ⟨Cres, hCres_pos, hCres⟩ :=
    plankReserveLoss_le_rpow kappa (show (0:ℝ) < ε/2 by linarith)
  refine ⟨K_small * Cres, mul_nonneg hK_small_nonneg hCres_pos.le, ?_⟩
  intro a b ha ha1 hab hb1 sc hcard c2 hc2pos hc2
  have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have ha1R : (a:ℝ) < 1 := by exact_mod_cast ha1
  have hBpos : (0:ℝ) < plankAngleScaleB a := by
    rw [plankAngleScaleB]; exact Real.exp_pos _
  have hLoss_pos : (0:ℝ) < plankReserveLoss kappa a :=
    plankReserveLoss_pos kappa a
  have hap_pos : (0:ℝ) < (a:ℝ) ^ (ε/2) := Real.rpow_pos_of_pos haR _
  -- Factor 1: from `refineConst_bound_uniform` at `ε/2`
  have hfac1 : (a:ℝ) ^ (ε/2) * (c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ)) ≤
      K_small :=
    hK_small ha ha1 hab hb1 sc hcard hc2pos hc2
  -- Factor 2: from `plankReserveLoss_le_rpow` at `ε/2`
  have hLoss_mul : (a:ℝ) ^ (ε/2) * (a:ℝ) ^ (-(ε/2)) = 1 := by
    calc
      (a:ℝ) ^ (ε/2) * (a:ℝ) ^ (-(ε/2)) = (a:ℝ) ^ ((ε/2) + (-(ε/2 : ℝ))) := by
        rw [← Real.rpow_add haR]
      _ = (a:ℝ) ^ (0 : ℝ) := by ring_nf
      _ = 1 := Real.rpow_zero _
  have hLoss_le : plankReserveLoss kappa a ≤ Cres * (a:ℝ) ^ (-(ε/2)) :=
    hCres a ha ha1
  have hfac2 : (a:ℝ) ^ (ε/2) * plankReserveLoss kappa a ≤ Cres := by
    calc
      (a:ℝ) ^ (ε/2) * plankReserveLoss kappa a ≤ (a:ℝ) ^ (ε/2) * (Cres * (a:ℝ) ^ (-(ε/2))) :=
        mul_le_mul_of_nonneg_left hLoss_le (by positivity)
      _ = Cres * ((a:ℝ) ^ (ε/2) * (a:ℝ) ^ (-(ε/2))) := by ring
      _ = Cres * 1 := by rw [hLoss_mul]
      _ = Cres := by ring
  -- Identity: a^ε * (c2⁻¹ * (B * Loss) * L) = (a^(ε/2) * (c2⁻¹ * B * L)) * (a^(ε/2) * Loss)
  have hLHS_eq : (a:ℝ) ^ ε * (c2⁻¹ * (plankAngleScaleB a * plankReserveLoss kappa a) * ((Nat.log
      2 sc + 1 : ℕ) : ℝ))
      = ((a:ℝ) ^ (ε/2) * (c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ)))
        * ((a:ℝ) ^ (ε/2) * plankReserveLoss kappa a) := by
    calc
      (a:ℝ) ^ ε * (c2⁻¹ * (plankAngleScaleB a * plankReserveLoss kappa a) * ((Nat.log 2 sc + 1 :
          ℕ) : ℝ))
          = ((a:ℝ) ^ (ε/2) * (a:ℝ) ^ (ε/2)) * (c2⁻¹ * (plankAngleScaleB a * plankReserveLoss
              kappa a) * ((Nat.log 2 sc + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_add haR, show (ε/2 : ℝ) + (ε/2 : ℝ) = ε by ring]
      _ = ((a:ℝ) ^ (ε/2) * (c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ)))
          * ((a:ℝ) ^ (ε/2) * plankReserveLoss kappa a) := by ring
  rw [hLHS_eq]
  exact mul_le_mul hfac1 hfac2 (by positivity) (by positivity)


/-- **The refinement-constant bound at an auxiliary scale `δ ≤ a`.**

This is `Kakeya.refineConst_bound_uniform` with the plank-count bound read at an auxiliary scale
`δ ≤ a` and the compensating factor read at the same scale: from `sc ≤ C₀ · δ ^ (-Nexp)` it bounds
`δ ^ ε · (c₂⁻¹ · B(a) · (⌊log₂ sc⌋ + 1))` by a constant depending only on `(ε, C₀, Nexp)`.

The constant is literally the same one, `K = K₁ · K₂ · C_β · K₂`.  Each of the three `a`-scale
factors is sub-polynomial in `a` and hence, since `δ ≤ a < 1` makes `a ^ (-ε/4) ≤ δ ^ (-ε/4)`, also
sub-polynomial in `δ`; the one genuinely `δ`-scaled factor, the dyadic count of the plank family,
is handled by `Kakeya.logarg_subpoly` read at `δ`.  So the four `δ ^ (-ε/4)` again cancel against
`δ ^ ε`.

This is what makes an auxiliary-scale form of GWZ Lemma 6.11 possible at all: the plank-count
hypothesis `|𝒫| ≤ C₀ · δ ^ (-Nexp)` is genuinely weaker than the `a`-scale one, and the losses
`δ ^ (±ε)` are correspondingly weaker, and it is exactly this lemma that says the two weakenings
match. -/
lemma refineConst_bound_perScale_of_data {ε : ℝ} (hε : 0 < ε) (C₀ : ℝ≥0) (Nexp : ℝ)
    {K1 Cβ : ℝ} (hK1pos : 0 < K1)
    (hK1 : ∀ (δ x : ℝ), 0 < δ → δ ≤ 1 → 0 ≤ x → x ≤ (1 : ℝ) * δ ^ (-(1 : ℝ)) →
      Real.log x / Real.log 2 + 2 ≤ K1 * δ ^ (-(ε / 4)))
    (hCβpos : 0 < Cβ)
    (hCβ : ∀ a : ℝ, 0 < a → a < 1 →
      Real.exp ((Real.log a⁻¹) ^ (3 / 4 : ℝ)) ≤ Cβ * a ^ (-(ε / 4))) :
      ∀ {a b δ : ℝ≥0}, 0 < a → a < 1 → a ≤ b → b ≤ 1 → 0 < δ → δ ≤ a →
        ∀ sc : ℕ, (sc : ℝ) ≤ (C₀ : ℝ) * (δ : ℝ) ^ (-Nexp) →
          ∀ {c2 : ℝ}, 0 < c2 →
            ((Real.log ((b : ℝ) / a) / Real.log 2 + 2)
                * (Real.log (sc : ℝ) / Real.log 2 + 1))⁻¹ ≤ c2 →
            (δ : ℝ) ^ ε * (c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ)) ≤
              K1 * logargConst (C₀ : ℝ) Nexp 1 (ε / 4) * Cβ *
                logargConst (C₀ : ℝ) Nexp 1 (ε / 4) := by
  set K2 : ℝ := logargConst (C₀ : ℝ) Nexp 1 (ε / 4) with hK2def
  have hK2 : ∀ (δ x : ℝ), 0 < δ → δ ≤ 1 → 0 ≤ x → x ≤ (C₀ : ℝ) * δ ^ (-Nexp) →
      Real.log x / Real.log 2 + 1 ≤ K2 * δ ^ (-(ε / 4)) :=
    logarg_subpoly_le (M := (C₀ : ℝ)) (N := Nexp) (r := 1) (show (0:ℝ) ≤ 1 by norm_num)
      (show (0:ℝ) < ε/4 by linarith)
  have hK2pos : 0 < K2 :=
    lt_of_lt_of_le zero_lt_one (le_logargConst (show (0:ℝ) < ε/4 by linarith))
  intro a b δ ha ha1 hab hb1 hδ hδa sc hcard c2 hc2pos hc2
  have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have ha1R : (a:ℝ) < 1 := by exact_mod_cast ha1
  have hδR : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδ
  have hδaR : (δ:ℝ) ≤ (a:ℝ) := by exact_mod_cast hδa
  have hδ1R : (δ:ℝ) ≤ 1 := le_trans hδaR ha1R.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDβpos : (0:ℝ) < (δ:ℝ) ^ (-(ε/4)) := Real.rpow_pos_of_pos hδR _
  -- transport of the `a`-scale sub-polynomial factors to the smaller scale `δ`
  have hmono : (a:ℝ) ^ (-(ε/4)) ≤ (δ:ℝ) ^ (-(ε/4)) :=
    Real.rpow_le_rpow_of_nonpos hδR hδaR (by linarith)
  set f1 : ℝ := Real.log ((b:ℝ)/a)/Real.log 2 + 2 with hf1def
  set f2 : ℝ := Real.log (sc:ℝ)/Real.log 2 + 1 with hf2def
  have hba1 : (1:ℝ) ≤ (b:ℝ)/a := by rw [le_div_iff₀ haR, one_mul]; exact_mod_cast hab
  have hf1pos : 0 < f1 := by
    have h0 := div_nonneg (Real.log_nonneg hba1) hlog2.le; rw [hf1def]; linarith
  have hf2pos : 0 < f2 := by
    rcases Nat.eq_zero_or_pos sc with h0 | hpos
    · simp [hf2def, h0]
    · have h0 := div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hpos)) hlog2.le
      rw [hf2def]; linarith
  have hc2inv : c2⁻¹ ≤ f1 * f2 := by
    rw [← inv_inv (f1 * f2)]
    exact (inv_le_inv₀ hc2pos (inv_pos.mpr (mul_pos hf1pos hf2pos))).mpr hc2
  have hBβ : plankAngleScaleB a ≤ Cβ * (δ:ℝ) ^ (-(ε/4)) :=
    (hCβ (a:ℝ) haR ha1R).trans (mul_le_mul_of_nonneg_left hmono hCβpos.le)
  have hf1β : f1 ≤ K1 * (δ:ℝ) ^ (-(ε/4)) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hmono hK1pos.le)
    refine hK1 (a:ℝ) ((b:ℝ)/a) haR ha1R.le (le_trans zero_le_one hba1) ?_
    rw [one_mul, Real.rpow_neg_one, div_le_iff₀ haR, inv_mul_eq_div, le_div_iff₀ haR]
    calc (b:ℝ) * a ≤ 1 * a := mul_le_mul (by exact_mod_cast hb1) le_rfl haR.le zero_le_one
      _ = (a:ℝ) := one_mul _
  have hf2β : f2 ≤ K2 * (δ:ℝ) ^ (-(ε/4)) :=
    hK2 (δ:ℝ) (sc:ℝ) hδR hδ1R (by positivity) hcard
  have hk1β : ((Nat.log 2 sc + 1 : ℕ) : ℝ) ≤ K2 * (δ:ℝ) ^ (-(ε/4)) := by
    refine le_trans ?_ hf2β
    push_cast
    rcases Nat.eq_zero_or_pos sc with h0 | hpos
    · simp [hf2def, h0]
    · rw [hf2def]
      have hNlog : (Nat.log 2 sc : ℝ) ≤ Real.log (sc:ℝ) / Real.log 2 := by
        rw [le_div_iff₀ hlog2]
        have h1 : (2:ℝ) ^ (Nat.log 2 sc) ≤ (sc:ℝ) := by
          exact_mod_cast Nat.pow_log_le_self 2 hpos.ne'
        have := Real.log_le_log (by positivity) h1
        rwa [Real.log_pow] at this
      linarith
  have hcombine : (δ:ℝ) ^ ε * ((δ:ℝ) ^ (-(ε/4)) * (δ:ℝ) ^ (-(ε/4)) * (δ:ℝ) ^ (-(ε/4))
      * (δ:ℝ) ^ (-(ε/4))) = 1 := by
    rw [← Real.rpow_add hδR, ← Real.rpow_add hδR, ← Real.rpow_add hδR,
      ← Real.rpow_add hδR]
    rw [show ε + (-(ε / 4) + -(ε / 4) + -(ε / 4) + -(ε / 4)) = 0 by ring, Real.rpow_zero]
  have hBpos0 : (0:ℝ) < plankAngleScaleB a := by rw [plankAngleScaleB]; exact Real.exp_pos _
  have hc2inv' : c2⁻¹ ≤ (K1 * (δ:ℝ) ^ (-(ε/4))) * (K2 * (δ:ℝ) ^ (-(ε/4))) :=
    le_trans hc2inv (mul_le_mul hf1β hf2β hf2pos.le (by positivity))
  have hX : c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ)
      ≤ (K1 * (δ:ℝ) ^ (-(ε/4))) * (K2 * (δ:ℝ) ^ (-(ε/4))) * (Cβ * (δ:ℝ) ^ (-(ε/4)))
        * (K2 * (δ:ℝ) ^ (-(ε/4))) :=
    mul_le_mul (mul_le_mul hc2inv' hBβ hBpos0.le (by positivity)) hk1β (by positivity)
      (by positivity)
  calc (δ:ℝ) ^ ε * (c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ))
      ≤ (δ:ℝ) ^ ε * ((K1 * (δ:ℝ) ^ (-(ε/4))) * (K2 * (δ:ℝ) ^ (-(ε/4))) * (Cβ * (δ:ℝ) ^ (-(ε/4)))
          * (K2 * (δ:ℝ) ^ (-(ε/4)))) :=
        mul_le_mul_of_nonneg_left hX (le_of_lt (Real.rpow_pos_of_pos hδR ε))
    _ = (K1 * K2 * Cβ * K2)
          * ((δ:ℝ) ^ ε * ((δ:ℝ) ^ (-(ε/4)) * (δ:ℝ) ^ (-(ε/4)) * (δ:ℝ) ^ (-(ε/4))
            * (δ:ℝ) ^ (-(ε/4)))) := by ring
    _ = K1 * K2 * Cβ * K2 := by rw [hcombine, mul_one]

/-- The two `C₀`-free ingredients of `Kakeya.refineConst_bound_perScale_of_data`: the
logarithmic bound `K1` on the dyadic count of the plank *aspect ratio*, and the sub-polynomial
bound `Cβ` on `plankAngleScaleB`.  Both are functions of `ε` alone, which is what lets
`Kakeya.exists_refineConst_bound_perScale_uniform` bind its constant before `C₀`. -/
private lemma exists_perScale_data {ε : ℝ} (hε : 0 < ε) :
    ∃ K1 Cβ : ℝ, 0 < K1 ∧ 0 < Cβ ∧
      (∀ (δ x : ℝ), 0 < δ → δ ≤ 1 → 0 ≤ x → x ≤ (1 : ℝ) * δ ^ (-(1 : ℝ)) →
        Real.log x / Real.log 2 + 2 ≤ K1 * δ ^ (-(ε / 4))) ∧
      (∀ a : ℝ, 0 < a → a < 1 →
        Real.exp ((Real.log a⁻¹) ^ (3 / 4 : ℝ)) ≤ Cβ * a ^ (-(ε / 4))) := by
  obtain ⟨Cβ, hCβpos, hCβ⟩ :=
    subpolyExp (show (0:ℝ) ≤ 3/4 by norm_num) (show (3/4:ℝ) < 1 by norm_num)
      (show (0:ℝ) < ε/4 by linarith)
  refine ⟨logargConst 1 1 2 (ε / 4), Cβ, ?_, hCβpos, ?_, hCβ⟩
  · exact lt_of_lt_of_le two_pos (le_logargConst (show (0:ℝ) < ε/4 by linarith))
  · exact logarg_subpoly_le (M := 1) (N := 1) (r := 2) (show (0:ℝ) ≤ 2 by norm_num)
      (show (0:ℝ) < ε/4 by linarith)

/-- **The refinement-constant bound at an auxiliary scale `δ ≤ a`** (blueprint
`lem:refineConstUniformPerScale`), in the existential form the callers use.

The witness is `K1 · K2 · Cβ · K2` with `K2 = Kakeya.logargConst C₀ Nexp 1 (ε/4)`; see
`Kakeya.refineConst_bound_perScale_of_data` for the version that names it and
`Kakeya.exists_refineConst_bound_perScale_uniform` for the version whose constant is bound
*before* `C₀`. -/
lemma refineConst_bound_uniform_perScale {ε : ℝ} (hε : 0 < ε) (C₀ : ℝ≥0) (Nexp : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {a b δ : ℝ≥0}, 0 < a → a < 1 → a ≤ b → b ≤ 1 → 0 < δ → δ ≤ a →
        ∀ sc : ℕ, (sc : ℝ) ≤ (C₀ : ℝ) * (δ : ℝ) ^ (-Nexp) →
          ∀ {c2 : ℝ}, 0 < c2 →
            ((Real.log ((b : ℝ) / a) / Real.log 2 + 2)
                * (Real.log (sc : ℝ) / Real.log 2 + 1))⁻¹ ≤ c2 →
            (δ : ℝ) ^ ε * (c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ)) ≤ K := by
  obtain ⟨K1, Cβ, hK1pos, hCβpos, hK1, hCβ⟩ := exists_perScale_data hε
  have hK2pos : (0:ℝ) < logargConst (C₀ : ℝ) Nexp 1 (ε / 4) :=
    lt_of_lt_of_le zero_lt_one (le_logargConst (show (0:ℝ) < ε/4 by linarith))
  exact ⟨_, le_of_lt (by positivity),
    refineConst_bound_perScale_of_data hε C₀ Nexp hK1pos hK1 hCβpos hCβ⟩

/-- **The refinement-constant bound with its constant bound *before* the plank-count constant
`C₀`.**

This is the exposure that `Kakeya.refineConst_bound_uniform_perScale` hides.  There, the
constant `K` is quantified *after* `C₀`, so nothing says how it grows with `C₀`; here a single
`A`, a function of `ε` and `Nexp` alone, serves every `C₀`, at the cost of the factor
`(log⁺C₀ + 1)²`.

That the growth is **logarithmic in `C₀`** and not a power of it is the whole content, and it
is what the Section-9 clause `Kakeya.VeryNotSticky.CaseScale.typicalAngle_const` needs: that
clause feeds a `C₀` of size `δ^{-2ϱ}` and asks the resulting constant to be at most
`(δ')^{-η/16}`, which a power of `C₀` could never satisfy (`CaseParams.densityBias` forces
`ϱ > 2^20 η`) but `(log⁺C₀+1)² = O(log(1/δ)²)` satisfies for all small `δ`. -/
lemma exists_refineConst_bound_perScale_uniform {ε : ℝ} (hε : 0 < ε) (Nexp : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ C₀ : ℝ≥0,
      ∀ {a b δ : ℝ≥0}, 0 < a → a < 1 → a ≤ b → b ≤ 1 → 0 < δ → δ ≤ a →
        ∀ sc : ℕ, (sc : ℝ) ≤ (C₀ : ℝ) * (δ : ℝ) ^ (-Nexp) →
          ∀ {c2 : ℝ}, 0 < c2 →
            ((Real.log ((b : ℝ) / a) / Real.log 2 + 2)
                * (Real.log (sc : ℝ) / Real.log 2 + 1))⁻¹ ≤ c2 →
            (δ : ℝ) ^ ε * (c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ)) ≤
              A * (max (Real.log (C₀ : ℝ)) 0 + 1) ^ 2 := by
  obtain ⟨K1, Cβ, hK1pos, hCβpos, hK1, hCβ⟩ := exists_perScale_data hε
  have hε4 : (0:ℝ) < ε / 4 := by linarith
  set B : ℝ := logargBase Nexp 1 (ε / 4) with hBdef
  have hB0 : 0 ≤ B := logargBase_nonneg (by norm_num) hε4
  refine ⟨K1 * Cβ * B ^ 2, by positivity, ?_⟩
  intro C₀ a b δ ha ha1 hab hb1 hδ hδa sc hcard c2 hc2pos hc2
  set L : ℝ := max (Real.log (C₀ : ℝ)) 0 with hLdef
  have hL0 : 0 ≤ L := le_max_right _ _
  have hK2le : logargConst (C₀ : ℝ) Nexp 1 (ε / 4) ≤ B * (L + 1) :=
    logargConst_le_logargBase_mul (by norm_num) hε4
  have hK2pos : (0:ℝ) < logargConst (C₀ : ℝ) Nexp 1 (ε / 4) :=
    lt_of_lt_of_le zero_lt_one (le_logargConst hε4)
  refine le_trans
    (refineConst_bound_perScale_of_data hε C₀ Nexp hK1pos hK1 hCβpos hCβ ha ha1 hab hb1 hδ hδa
      sc hcard hc2pos hc2) ?_
  have hsq : logargConst (C₀ : ℝ) Nexp 1 (ε / 4) * logargConst (C₀ : ℝ) Nexp 1 (ε / 4)
      ≤ (B * (L + 1)) * (B * (L + 1)) :=
    mul_le_mul hK2le hK2le hK2pos.le (by positivity)
  calc K1 * logargConst (C₀ : ℝ) Nexp 1 (ε / 4) * Cβ * logargConst (C₀ : ℝ) Nexp 1 (ε / 4)
      = (K1 * Cβ) *
          (logargConst (C₀ : ℝ) Nexp 1 (ε / 4) * logargConst (C₀ : ℝ) Nexp 1 (ε / 4)) := by
        ring
    _ ≤ (K1 * Cβ) * ((B * (L + 1)) * (B * (L + 1))) := by
        exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = K1 * Cβ * B ^ 2 * (L + 1) ^ 2 := by ring

/-- **The reserve refinement-constant bound at an auxiliary scale `δ ≤ a`.**

`Kakeya.refineConst_bound_uniform_reserve` and `Kakeya.refineConst_bound_uniform_perScale`
combined: the extra reserve factor `plankReserveLoss kappa a` is absorbed exactly as there, using
`δ ^ (ε/2) ≤ a ^ (ε/2)` to read the `a`-scale sub-polynomial bound at the smaller scale. -/
lemma refineConst_bound_uniform_reserve_perScale (kappa : ℝ) {ε : ℝ} (hε : 0 < ε)
    (C₀ : ℝ≥0) (Nexp : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {a b δ : ℝ≥0}, 0 < a → a < 1 → a ≤ b → b ≤ 1 → 0 < δ → δ ≤ a →
        ∀ sc : ℕ, (sc : ℝ) ≤ (C₀ : ℝ) * (δ : ℝ) ^ (-Nexp) →
          ∀ {c2 : ℝ}, 0 < c2 →
            ((Real.log ((b : ℝ) / a) / Real.log 2 + 2)
                * (Real.log (sc : ℝ) / Real.log 2 + 1))⁻¹ ≤ c2 →
            (δ : ℝ) ^ ε * (c2⁻¹ * (plankAngleScaleB a * plankReserveLoss kappa a)
                * ((Nat.log 2 sc + 1 : ℕ) : ℝ)) ≤ K := by
  have hε2 : 0 < ε/2 := by linarith
  obtain ⟨K_small, hK_small_nonneg, hK_small⟩ :=
    refineConst_bound_uniform_perScale (show (0:ℝ) < ε/2 from hε2) C₀ Nexp
  obtain ⟨Cres, hCres_pos, hCres⟩ :=
    plankReserveLoss_le_rpow kappa (show (0:ℝ) < ε/2 by linarith)
  refine ⟨K_small * Cres, mul_nonneg hK_small_nonneg hCres_pos.le, ?_⟩
  intro a b δ ha ha1 hab hb1 hδ hδa sc hcard c2 hc2pos hc2
  have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have ha1R : (a:ℝ) < 1 := by exact_mod_cast ha1
  have hδR : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδ
  have hδaR : (δ:ℝ) ≤ (a:ℝ) := by exact_mod_cast hδa
  have hBpos : (0:ℝ) < plankAngleScaleB a := by
    rw [plankAngleScaleB]; exact Real.exp_pos _
  have hLoss_pos : (0:ℝ) < plankReserveLoss kappa a := plankReserveLoss_pos kappa a
  have hfac1 : (δ:ℝ) ^ (ε/2) * (c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ)) ≤
      K_small := hK_small ha ha1 hab hb1 hδ hδa sc hcard hc2pos hc2
  have hδle : (δ:ℝ) ^ (ε/2) ≤ (a:ℝ) ^ (ε/2) := Real.rpow_le_rpow hδR.le hδaR hε2.le
  have hLoss_mul : (a:ℝ) ^ (ε/2) * (a:ℝ) ^ (-(ε/2)) = 1 := by
    rw [← Real.rpow_add haR, show (ε/2 : ℝ) + -(ε/2 : ℝ) = 0 by ring, Real.rpow_zero]
  have hfac2 : (δ:ℝ) ^ (ε/2) * plankReserveLoss kappa a ≤ Cres := by
    calc (δ:ℝ) ^ (ε/2) * plankReserveLoss kappa a
        ≤ (a:ℝ) ^ (ε/2) * plankReserveLoss kappa a :=
          mul_le_mul_of_nonneg_right hδle hLoss_pos.le
      _ ≤ (a:ℝ) ^ (ε/2) * (Cres * (a:ℝ) ^ (-(ε/2))) :=
          mul_le_mul_of_nonneg_left (hCres a ha ha1) (by positivity)
      _ = Cres * ((a:ℝ) ^ (ε/2) * (a:ℝ) ^ (-(ε/2))) := by ring
      _ = Cres := by rw [hLoss_mul, mul_one]
  have hLHS_eq : (δ:ℝ) ^ ε * (c2⁻¹ * (plankAngleScaleB a * plankReserveLoss kappa a)
      * ((Nat.log 2 sc + 1 : ℕ) : ℝ))
      = ((δ:ℝ) ^ (ε/2) * (c2⁻¹ * plankAngleScaleB a * ((Nat.log 2 sc + 1 : ℕ) : ℝ)))
        * ((δ:ℝ) ^ (ε/2) * plankReserveLoss kappa a) := by
    rw [show (δ:ℝ) ^ ε = (δ:ℝ) ^ (ε/2) * (δ:ℝ) ^ (ε/2) by
      rw [← Real.rpow_add hδR, show (ε/2 : ℝ) + (ε/2 : ℝ) = ε by ring]]
    ring
  rw [hLHS_eq]
  exact mul_le_mul hfac1 hfac2 (by positivity) (by positivity)

end Kakeya

end
