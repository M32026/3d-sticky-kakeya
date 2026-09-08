/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.Frostman
public import Kakeya.GridScale
public import Kakeya.MultiScaleFac.Loss
public import Kakeya.MultiScaleFac.ScaleGapTransport
public import Kakeya.Sticky
public import Kakeya.Tube.Basic
public import Kakeya.Uniform

/-!
# Assembling the third bullet of the amended dichotomy, half (B)

The transport of a node maximal density at a comparable radius, the choice of a grid index inside
the stopping margin, and the move of the exponent to the rounded scale.  This is the half-(B) API
the dichotomy actually consumes.

Sliced out of the former `DividingScalesKT`.
-/

@[expose] public section

open MeasureTheory Real Metric
open scoped Topology

universe u
open Tube

namespace Kakeya

open StickyKakeya
open MultiScaleFac

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

section Bullet3Assembly

variable {ι : Type*}

/-! #### Transport of a node maximal density at a comparable radius -/

/-- The dimensional constant of the comparable-radius transport, at thickening multiple `k`: the
ratio of the two tube-volume constants times the cost of thickening a test body by `k` times a
scale it accommodates. -/
noncomputable abbrev KT.gapDensityConstN (k : ℕ) : NNReal :=
  thickenVolConstN (E := E) k * Tube.volume_le.C (Module.finrank ℝ E)
    / Tube.le_volume.c (Module.finrank ℝ E)

/-- The `δ`-free dimensional constant of the comparable-radius transport: the constant at
thickening multiple `5`, which dominates the multiple `⌈G⌉` for every `G ≥ 1` once a factor `G ^ n`
is extracted. -/
noncomputable abbrev KT.gapDensityConstCmp : NNReal := KT.gapDensityConstN (E := E) 5

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Thickening by `⌈G⌉` times an accommodated scale costs `G ^ n` times thickening by `5` times
it**, since `2(⌈G⌉ + 1) ≤ 12 G` for `G ≥ 1`.  This is what keeps the `δ`-dependence of the
comparable-radius transport confined to `G`. -/
private theorem thickenVolConstN_ceil_le {G : ℝ} (hG : 1 ≤ G) :
    (thickenVolConstN (E := E) ⌈G⌉₊ : ℝ)
      ≤ G ^ Module.finrank ℝ E * (thickenVolConstN (E := E) 5 : ℝ) := by
  have hnum : (2 * ((⌈G⌉₊ : ℝ) + 1)) ^ Module.finrank ℝ E
      ≤ G ^ Module.finrank ℝ E * (2 * ((5 : ℝ) + 1)) ^ Module.finrank ℝ E := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    linarith [Nat.ceil_lt_add_one (zero_le_one.trans hG)]
  unfold thickenVolConstN
  push_cast
  rw [mul_div_assoc']
  gcongr

/-- **The comparable-radius transport, tested against one container.**  The per-test-body form of
the transport, in which the fattening radius `ρ` is only at most `k σ_c` rather than at most the
grid scale `σ_c`; the selected children then lie in the `k σ_c`-thickening of the test body, which
`Kakeya.MultiScaleFac.volume_thickenBody_le_nsmul` makes affordable. -/
private theorem densityIn_nodesIn_le_mul_maxDensity_nodesIn_rescale_nsmul {δ : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu)
    (hs : s.Nonempty) {c b : ℕ} (hcb : c ≤ b) (hbN : b ≤ N) (hσ1 : gridScale δ N c ≤ 1)
    {ρ : NNReal} (hρ0 : 0 < ρ) {k : ℕ} (hρk : ρ ≤ (k : NNReal) * gridScale δ N c)
    (K K' : ConvexSpaceBody E) :
    Kakeya.densityIn (𝒰.nodesIn c K) (fun j => (𝒰.cover.tube c j).toConvexSpaceBody) K'
      ≤ ((KT.gapDensityConstN (E := E) k
            * (gridScale δ N c / ρ) ^ (Module.finrank ℝ E - 1) : NNReal) : ENNReal)
          * Kakeya.maxDensity (𝒰.nodesIn b K)
              (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody) := by
  classical
  let n := Module.finrank ℝ E
  let m := n - 1
  let σ := gridScale δ N c
  let W : ι → ConvexSpaceBody E := fun j => (𝒰.cover.tube c j).toConvexSpaceBody
  let W' : ι → ConvexSpaceBody E := fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody
  let t : Finset ι := (𝒰.nodesIn c K).filter (fun j => W j ≤ K')
  let vlo : ENNReal := ((Tube.le_volume.c n * ρ ^ m : NNReal) : ENNReal)
  let vhi : ENNReal := ((Tube.volume_le.C n * σ ^ m : NNReal) : ENNReal)
  let q : ENNReal := (thickenVolConstN (E := E) k : ENNReal)
  let Denn : ENNReal := ((KT.gapDensityConstN (E := E) k * (σ / ρ) ^ m : NNReal) : ENNReal)
  rw [Kakeya.densityIn_eq_densityIn_filter]
  rcases Finset.eq_empty_or_nonempty t with ht | htne
  · simp [t, W, ht, Kakeya.densityIn_empty]
  · obtain ⟨j₀, hj₀t⟩ := htne
    obtain ⟨f, hfinj, hfmem⟩ :=
      exists_child_selection 𝒰 hs hcb hbN t (by
        intro j hjt
        exact ((𝒰.mem_nodesIn_iff c K j).mp (Finset.mem_filter.mp hjt).1).1)
    let t' : Finset ι := t.image f
    have hcard : t.card ≤ t'.card := (Finset.card_image_of_injOn hfinj).ge
    have hchild : ∀ j ∈ t, f j ∈ 𝒰.nodesIn b (𝒰.cover.tube c j).toConvexSpaceBody := by
      intro j hjt
      have h := hfmem j hjt
      rwa [UniformTubeSet.nodesUnder_eq_nodesIn] at h
    have htb : ∀ j ∈ t, (𝒰.cover.tube b (f j)).toConvexSpaceBody
        ≤ (𝒰.cover.tube c j).toConvexSpaceBody := fun j hjt =>
      ((𝒰.mem_nodesIn_iff b (𝒰.cover.tube c j).toConvexSpaceBody (f j)).mp (hchild j hjt)).2
    have ht's' : t' ⊆ 𝒰.nodesIn b K := by
      intro j' hj'
      obtain ⟨j, hjt, rfl⟩ := Finset.mem_image.mp hj'
      exact (𝒰.mem_nodesIn_iff b K (f j)).mpr
        ⟨((𝒰.mem_nodesIn_iff b (𝒰.cover.tube c j).toConvexSpaceBody (f j)).mp (hchild j hjt)).1,
          (htb j hjt).trans ((𝒰.mem_nodesIn_iff c K j).mp (Finset.mem_filter.mp hjt).1).2⟩
    have hmem' : ∀ j' ∈ t', W' j' ≤ K'.cthickening (((k : NNReal) * σ : NNReal) : ℝ) := by
      intro j' hj'
      obtain ⟨j, hjt, rfl⟩ := Finset.mem_image.mp hj'
      have hρkℝ : (ρ : ℝ) ≤ (((k : NNReal) * σ : NNReal) : ℝ) := by exact_mod_cast hρk
      simpa [W'] using tube_rescale_le_cthickening (𝒰.cover.tube b (f j)) hρkℝ
        ((htb j hjt).trans (Finset.mem_filter.mp hjt).2)
    have hhi : ∀ j ∈ t, MeasureTheory.volume (W j).carrier ≤ vhi := by
      intro j hj
      have hv := Tube.volume_le hσ1 (𝒰.cover.tube c j)
      simpa [W, vhi, n, m, σ, ENNReal.coe_mul, ENNReal.coe_pow] using hv
    have hlo : ∀ j' ∈ t', vlo ≤ MeasureTheory.volume (W' j').carrier := by
      intro j' hj'
      have hv := Tube.le_volume ((𝒰.cover.tube b j').rescale ρ)
      simpa [W', vlo, n, m, ENNReal.coe_mul, ENNReal.coe_pow] using hv
    have hKq : MeasureTheory.volume (K'.cthickening (((k : NNReal) * σ : NNReal) : ℝ)).carrier ≤
        q * MeasureTheory.volume K'.carrier := by
      have hj₀K' : W j₀ ≤ K' := (Finset.mem_filter.mp hj₀t).2
      have hc := volume_thickenBody_le_nsmul (𝒰.cover.tube c j₀) (by simpa [W] using hj₀K')
        (le_refl ((k : NNReal) * σ))
      simpa [q, σ] using hc
    have hvlo0 : vlo ≠ 0 := ENNReal.coe_ne_zero.mpr
      (mul_ne_zero (Tube.le_volume.c_pos n).ne' (pow_ne_zero m hρ0.ne'))
    have hvloTop : vlo ≠ ⊤ := ENNReal.coe_ne_top
    have hD : vhi * q ≤ Denn * vlo := by
      have hD_NN : Tube.volume_le.C n * σ ^ m * thickenVolConstN (E := E) k ≤
          KT.gapDensityConstN (E := E) k * (σ / ρ) ^ m * (Tube.le_volume.c n * ρ ^ m) :=
        le_of_eq (by
          unfold KT.gapDensityConstN
          rw [show Module.finrank ℝ E = n by rfl]
          field_simp [(Tube.le_volume.c_pos n).ne', hρ0.ne']
          rw [mul_assoc, ← mul_pow, div_mul_cancel₀ _ hρ0.ne']
          ring)
      change ((Tube.volume_le.C n * σ ^ m : NNReal) : ENNReal)
            * (thickenVolConstN (E := E) k : ENNReal) ≤
          ((KT.gapDensityConstN (E := E) k * (σ / ρ) ^ m : NNReal) : ENNReal)
            * ((Tube.le_volume.c n * ρ ^ m : NNReal) : ENNReal)
      exact_mod_cast hD_NN
    exact
      (densityIn_le_mul_maxDensity_of_selection (ι' := ι) (t := t) (t' := t')
        (s' := 𝒰.nodesIn b K) (W := W) (W' := W') (K' := K')
        (K'' := K'.cthickening (((k : NNReal) * σ : NNReal) : ℝ)) (vlo := vlo) (vhi := vhi) (q := q)
        (D := Denn) hvlo0 hvloTop hhi hlo hcard ht's' hmem' hKq hD)

/-- **The comparable-radius transport, in ratio form.**  The maximum over test bodies of
`densityIn_nodesIn_le_mul_maxDensity_nodesIn_rescale_nsmul`. -/
private theorem maxDensity_nodesIn_le_mul_maxDensity_nodesIn_rescale_nsmul {δ : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu)
    (hs : s.Nonempty) {c b : ℕ} (hcb : c ≤ b) (hbN : b ≤ N) (hσ1 : gridScale δ N c ≤ 1)
    {ρ : NNReal} (hρ0 : 0 < ρ) {k : ℕ} (hρk : ρ ≤ (k : NNReal) * gridScale δ N c)
    (K : ConvexSpaceBody E) :
    Kakeya.maxDensity (𝒰.nodesIn c K) (fun j => (𝒰.cover.tube c j).toConvexSpaceBody)
      ≤ ((KT.gapDensityConstN (E := E) k
            * (gridScale δ N c / ρ) ^ (Module.finrank ℝ E - 1) : NNReal) : ENNReal)
          * Kakeya.maxDensity (𝒰.nodesIn b K)
              (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody) := by
  rw [Kakeya.maxDensity_le_iff]
  intro K'
  exact densityIn_nodesIn_le_mul_maxDensity_nodesIn_rescale_nsmul 𝒰 hs hcb hbN hσ1 hρ0 hρk K K'

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The constant of the comparable-radius transport, with its `δ`-dependence isolated.**

Both the ratio `(σ_c/ρ)^{n-1}` and the thickening multiple `⌈G⌉` are bounded by powers of `G`, so
the whole constant is a `δ`-free dimensional factor times `G ^ {2n}`. -/
private theorem KT.gapDensityConstN_mul_div_pow_le {G : ℝ} (hG : 1 ≤ G) {σ ρ : NNReal}
    (hρ0 : 0 < ρ) (hσG : (σ : ℝ) ≤ G * (ρ : ℝ)) :
    ((KT.gapDensityConstN (E := E) ⌈G⌉₊ * (σ / ρ) ^ (Module.finrank ℝ E - 1) : NNReal) : ENNReal)
      ≤ (KT.gapDensityConstCmp (E := E) : ENNReal)
          * ENNReal.ofReal (G ^ (2 * Module.finrank ℝ E)) := by
  set n : ℕ := Module.finrank ℝ E
  have hG0 : (0 : ℝ) ≤ G := zero_le_one.trans hG
  have hcmpC_nonneg : (0 : ℝ) ≤ (KT.gapDensityConstCmp (E := E) : ℝ) := NNReal.coe_nonneg _
  have hσr : ((σ / ρ : NNReal) : ℝ) ≤ G := by
    rw [NNReal.coe_div]
    exact (div_le_iff₀ (by exact_mod_cast hρ0)).mpr hσG
  have hcnst : (KT.gapDensityConstN (E := E) ⌈G⌉₊ : ℝ)
      ≤ G ^ n * (KT.gapDensityConstCmp (E := E) : ℝ) := by
    unfold KT.gapDensityConstN KT.gapDensityConstCmp
    push_cast
    rw [mul_div_assoc', ← mul_assoc]
    gcongr
    exact thickenVolConstN_ceil_le hG
  have hmain : ((KT.gapDensityConstN (E := E) ⌈G⌉₊ * (σ / ρ) ^ (n - 1) : NNReal) : ℝ)
      ≤ (KT.gapDensityConstCmp (E := E) : ℝ) * G ^ (2 * n) :=
    calc
      (KT.gapDensityConstN (E := E) ⌈G⌉₊ : ℝ) * ((σ / ρ : NNReal) : ℝ) ^ (n - 1)
          ≤ G ^ n * (KT.gapDensityConstCmp (E := E) : ℝ) * G ^ (n - 1) :=
        mul_le_mul hcnst (pow_le_pow_left₀ (NNReal.coe_nonneg _) hσr _)
          (pow_nonneg (NNReal.coe_nonneg _) _) (mul_nonneg (pow_nonneg hG0 n) hcmpC_nonneg)
      _ = (KT.gapDensityConstCmp (E := E) : ℝ) * G ^ (n + (n - 1)) := by rw [pow_add]; ring
      _ ≤ (KT.gapDensityConstCmp (E := E) : ℝ) * G ^ (2 * n) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hG (by omega)) hcmpC_nonneg
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul hcmpC_nonneg]
  exact ENNReal.ofReal_le_ofReal hmain

/-- **Comparable-radius transport of a node maximal density**, the form consumed by the third
bullet of `Kakeya.MultiScaleFac.dividingScalesKatzTao` once the window has been rounded to the
stopping margin.  The bracket `σ_{c+1} ≤ ρ ≤ σ_c` is replaced by two-sided comparability with an
explicit factor `G`, at the price of `G ^ {2n}` rather than `G ^ {n-1}` in the constant. -/
theorem maxDensity_nodesIn_le_mul_maxDensity_nodesIn_rescale_comparable {δ : NNReal} (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu)
    (hs : s.Nonempty) {c b : ℕ} (hcb : c ≤ b) (hbN : b ≤ N) {ρ : NNReal} (hρ0 : 0 < ρ) {G : ℝ}
    (hG : 1 ≤ G) (hlo : (gridScale δ N c : ℝ) ≤ G * (ρ : ℝ))
    (hhi : (ρ : ℝ) ≤ G * (gridScale δ N c : ℝ)) (K : ConvexSpaceBody E) :
    Kakeya.maxDensity (𝒰.nodesIn c K) (fun j => (𝒰.cover.tube c j).toConvexSpaceBody)
      ≤ (KT.gapDensityConstCmp (E := E) : ENNReal)
          * ENNReal.ofReal (G ^ (2 * Module.finrank ℝ E))
          * Kakeya.maxDensity (𝒰.nodesIn b K)
              (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody) := by
  have hρk : ρ ≤ ((⌈G⌉₊ : ℕ) : NNReal) * gridScale δ N c := by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact hhi.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil G) (NNReal.coe_nonneg _))
  refine (maxDensity_nodesIn_le_mul_maxDensity_nodesIn_rescale_nsmul 𝒰 hs hcb hbN
    (gridScale_le_one hδ1 N c) hρ0 hρk K).trans ?_
  gcongr
  exact KT.gapDensityConstN_mul_div_pow_le hG hρ0 hlo

/-! #### Choosing a grid index inside the stopping margin -/

/-- **Clamping a radius into an interval costs the slack it was already comparable with.**

`ρ` is comparable to both endpoints with factor `g`, so its clamp into `[u, v]` is comparable to
`ρ` itself with the same factor: either the clamp is `ρ`, or it is the endpoint that `ρ`
overshot. -/
private theorem exists_clamped_of_le_mul {u v ρ : NNReal} {g : ℝ} (hg : 1 ≤ g) (huv : u ≤ v)
    (hlo : (u : ℝ) ≤ g * (ρ : ℝ)) (hhi : (ρ : ℝ) ≤ g * (v : ℝ)) :
    ∃ ρ' : NNReal, u ≤ ρ' ∧ ρ' ≤ v ∧ (ρ' : ℝ) ≤ g * (ρ : ℝ) ∧ (ρ : ℝ) ≤ g * (ρ' : ℝ) := by
  refine ⟨max u (min v ρ), le_max_left _ _, max_le huv (min_le_left v ρ), ?_, ?_⟩
  · rw [NNReal.coe_max]
    refine max_le hlo (le_trans ?_ (le_mul_of_one_le_left (by positivity) hg))
    exact_mod_cast min_le_right v ρ
  · rcases le_total ρ v with hρv | hvρ
    · refine le_trans ?_ (le_mul_of_one_le_left (by positivity) hg)
      exact_mod_cast le_max_of_le_right (le_min hρv le_rfl)
    · rw [min_eq_left hvρ, max_eq_right huv]
      exact hhi

/-- **A radius comparable to the two endpoints of a range of grid indices is comparable to a grid
scale inside that range.**  One grid gap is paid for the clamp of
`Kakeya.MultiScaleFac.exists_clamped_of_le_mul` and one for the rounding of
`Kakeya.MultiScaleFac.exists_gridIndex_of_mem_Icc`, hence the slack `scaleGapLoss 2 δ`. -/
private theorem exists_gridIndex_comparable {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {A B : ℕ}
    (hAB : A ≤ B) {ρ : NNReal}
    (hlo : (gridScale δ (ssfGridLen δ) B : ℝ) ≤ scaleGapLoss 1 δ * (ρ : ℝ))
    (hhi : (ρ : ℝ) ≤ scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) A : ℝ)) :
    ∃ c : ℕ, A ≤ c ∧ c ≤ B ∧
      (gridScale δ (ssfGridLen δ) c : ℝ) ≤ scaleGapLoss 2 δ * (ρ : ℝ) ∧
      (ρ : ℝ) ≤ scaleGapLoss 2 δ * (gridScale δ (ssfGridLen δ) c : ℝ) := by
  have hg1 : (1 : ℝ) ≤ scaleGapLoss 1 δ := one_le_scaleGapLoss 1 hδ hδ1
  have hg0 : (0 : ℝ) < scaleGapLoss 1 δ := zero_lt_one.trans_le hg1
  have hsq : scaleGapLoss 2 δ = scaleGapLoss 1 δ * scaleGapLoss 1 δ := by
    simpa using (Kakeya.MultiScaleFac.A.scaleGapLoss_add hδ 1 1).symm
  have huv : gridScale δ (ssfGridLen δ) B ≤ gridScale δ (ssfGridLen δ) A :=
    gridScale_antitone hδ hδ1 (ssfGridLen δ) hAB
  obtain ⟨ρ', hu, hv, h1, h2⟩ := exists_clamped_of_le_mul hg1 huv hlo hhi
  obtain ⟨c, hAc, hcB, hc1, hc2⟩ :=
    exists_gridIndex_of_mem_Icc hδ hδ1 hAB (by exact_mod_cast hu) (by exact_mod_cast hv)
  refine ⟨c, hAc, hcB, ?_, ?_⟩
  · rw [hsq, mul_assoc]
    exact (gridScale_le_scaleGapLoss_mul hδ hc1).trans (mul_le_mul_of_nonneg_left h1 hg0.le)
  · rw [hsq, mul_assoc]
    exact (h2.trans (mul_le_mul_of_nonneg_left hc2 hg0.le)).trans
      (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (NNReal.coe_nonneg _) hg1) hg0.le)

/-- **A radius below `δ^{x/M}` is within one gap of every grid scale of index at most `x + 1`.** -/
private theorem le_scaleGapLoss_mul_gridScale_of_le_rpow {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {x : ℝ} {k : ℕ} (hk : (k : ℝ) ≤ x + 1) {ρ : NNReal}
    (hρ : (ρ : ℝ) ≤ (δ : ℝ) ^ (x / (ssfGridLen δ : ℝ))) :
    (ρ : ℝ) ≤ scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) k : ℝ) := by
  have hδ0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hident : (δ : ℝ) ^ (((k : ℝ) - 1) / (ssfGridLen δ : ℝ)) =
      scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) k : ℝ) := by
    rw [scaleGapLoss, gridScale, NNReal.coe_rpow, ← Real.rpow_add hδ0]
    congr 1
    ring
  rw [← hident]
  exact hρ.trans (Real.rpow_le_rpow_of_exponent_ge hδ0 (by exact_mod_cast hδ1)
    (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)))

/-- **A radius above `δ^{x/M}` dominates, up to one gap, every grid scale of index at least
`x - 1`.** -/
private theorem gridScale_le_scaleGapLoss_mul_of_rpow_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {x : ℝ} {k : ℕ} (hk : x - 1 ≤ (k : ℝ)) {ρ : NNReal}
    (hρ : (δ : ℝ) ^ (x / (ssfGridLen δ : ℝ)) ≤ (ρ : ℝ)) :
    (gridScale δ (ssfGridLen δ) k : ℝ) ≤ scaleGapLoss 1 δ * (ρ : ℝ) := by
  have hδ0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  calc
    (gridScale δ (ssfGridLen δ) k : ℝ) = (δ : ℝ) ^ ((k : ℝ) / (ssfGridLen δ : ℝ)) := by
      rw [gridScale, NNReal.coe_rpow]
    _ ≤ (δ : ℝ) ^ ((x - 1) / (ssfGridLen δ : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hδ0 (by exact_mod_cast hδ1)
        (div_le_div_of_nonneg_right hk (Nat.cast_nonneg _))
    _ = scaleGapLoss 1 δ * (δ : ℝ) ^ (x / (ssfGridLen δ : ℝ)) := by
      rw [scaleGapLoss, ← Real.rpow_add hδ0]
      congr 1
      ring
    _ ≤ scaleGapLoss 1 δ * (ρ : ℝ) :=
      mul_le_mul_of_nonneg_left hρ (by rw [scaleGapLoss]; positivity)

/-- **A real scale in the `ε`-window is comparable to a grid scale inside the stopping margin.**
Written as exponents, the window is `x ∈ [a + ε(b-a), b - ε(b-a)]` and the margin is
`[a + m, b - m]` with `m = ⌈ε(b-a)⌉`, so the two differ by at most one grid index: rounding `x` to
an index and clamping that index into the margin cost one grid gap each. -/
theorem exists_marginIndex_of_window {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ}
    {a b m : ℕ} (_hmlo : ε * ((b : ℝ) - (a : ℝ)) ≤ (m : ℝ))
    (hmhi : (m : ℝ) ≤ ε * ((b : ℝ) - (a : ℝ)) + 1) (hroom : a + 2 * m ≤ b) {ρ : NNReal}
    (hlo : (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε
        ≤ (ρ : ℝ))
    (hhi : (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
        * ((gridScale δ (ssfGridLen δ) b : ℝ) / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ε) :
    ∃ c : ℕ, a + m ≤ c ∧ c + m ≤ b ∧
      (gridScale δ (ssfGridLen δ) c : ℝ) ≤ scaleGapLoss 2 δ * (ρ : ℝ) ∧
      (ρ : ℝ) ≤ scaleGapLoss 2 δ * (gridScale δ (ssfGridLen δ) c : ℝ) := by
  have hd0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hcoe : ∀ k : ℕ, ((gridScale δ (ssfGridLen δ) k : NNReal) : ℝ)
      = (δ : ℝ) ^ ((k : ℝ) / (ssfGridLen δ : ℝ)) := fun k => by
    rw [gridScale, NNReal.coe_rpow]
  have key : ∀ p q : ℕ, ∀ y : ℝ, (p : ℝ) + ε * ((q : ℝ) - (p : ℝ)) = y →
      (gridScale δ (ssfGridLen δ) p : ℝ)
        * ((gridScale δ (ssfGridLen δ) q : ℝ) / (gridScale δ (ssfGridLen δ) p : ℝ)) ^ ε
      = (δ : ℝ) ^ (y / (ssfGridLen δ : ℝ)) := by
    intro p q y hy
    rw [hcoe, hcoe, ← Real.rpow_sub hd0, ← Real.rpow_mul hd0.le, ← Real.rpow_add hd0, ← hy]
    congr 1
    ring
  have hlow := key b a ((b : ℝ) - ε * ((b : ℝ) - (a : ℝ))) (by ring)
  have hup := key a b ((a : ℝ) + ε * ((b : ℝ) - (a : ℝ))) (by ring)
  have hmb : m ≤ b := by omega
  have hAB : a + m ≤ b - m := by omega
  have hlo' : (gridScale δ (ssfGridLen δ) (b - m) : ℝ) ≤ scaleGapLoss 1 δ * (ρ : ℝ) :=
    gridScale_le_scaleGapLoss_mul_of_rpow_le hδ hδ1
      (x := (b : ℝ) - ε * ((b : ℝ) - (a : ℝ))) (by rw [Nat.cast_sub hmb]; linarith)
      (hlow.symm.trans_le hlo)
  have hhi' : (ρ : ℝ) ≤ scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) (a + m) : ℝ) :=
    le_scaleGapLoss_mul_gridScale_of_le_rpow hδ hδ1
      (x := (a : ℝ) + ε * ((b : ℝ) - (a : ℝ))) (by push_cast; linarith) (hhi.trans_eq hup)
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_gridIndex_comparable hδ hδ1 hAB hlo' hhi'
  exact ⟨c, hc1, by omega, hc3, hc4⟩

/-! #### Moving the exponent to the rounded scale -/

/-- **Moving the exponent of the lower bound from a real scale to a comparable grid scale costs one
gap loss.**  The exponent is at most `1`, so the gap loss is not amplified by it. -/
theorem ofReal_rpow_div_le_mul_ofReal_rpow_div {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {θ ρ σ : ℝ} (hθ : 0 ≤ θ) (hρ : 0 < ρ) (hσ : 0 < σ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hcmp : σ ≤ scaleGapLoss 2 δ * ρ) :
    ENNReal.ofReal ((θ / ρ) ^ t)
      ≤ ENNReal.ofReal (scaleGapLoss 2 δ) * ENNReal.ofReal ((θ / σ) ^ t) := by
  set L : ℝ := scaleGapLoss 2 δ
  have hL1 : (1 : ℝ) ≤ L := one_le_scaleGapLoss 2 hδ hδ1
  have hL0 : (0 : ℝ) < L := zero_lt_one.trans_le hL1
  have hreal : (θ / ρ) ^ t ≤ L * (θ / σ) ^ t := by
    have hbase : θ / ρ ≤ L * (θ / σ) := by
      rw [mul_div_assoc', div_le_div_iff₀ hρ hσ]
      calc θ * σ ≤ θ * (L * ρ) := mul_le_mul_of_nonneg_left hcmp hθ
        _ = L * θ * ρ := by ring
    calc (θ / ρ) ^ t ≤ (L * (θ / σ)) ^ t := Real.rpow_le_rpow (by positivity) hbase ht0
      _ = L ^ t * (θ / σ) ^ t := Real.mul_rpow hL0.le (by positivity)
      _ ≤ L * (θ / σ) ^ t := mul_le_mul_of_nonneg_right
          (by simpa using Real.rpow_le_rpow_of_exponent_le hL1 ht1)
          (Real.rpow_nonneg (by positivity) t)
  rw [← ENNReal.ofReal_mul hL0.le]
  exact ENNReal.ofReal_le_ofReal hreal

end Bullet3Assembly

end MultiScaleFac

end Kakeya

end
