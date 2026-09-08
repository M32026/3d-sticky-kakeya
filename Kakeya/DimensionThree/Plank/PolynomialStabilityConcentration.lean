/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.LocalAngleConcentration
public import Kakeya.DimensionThree.Plank.SlabTypicalAngle

/-!
# Angular concentration at a free, then at a *polynomial*, stability constant

`Plank.localAngleConcentration_trimmed_of_slabLocal` consumes the angular-stability clause in the
stop-scale form `θ / Kakeya.plankAngleScaleB a ≤ M(V, t)`.  What
`Kakeya.plankReduction_preassembly` actually delivers is the two-sided
`Kakeya.IsTypicalPlankAngle` at the constant `Cθ · a ^ (-ε_int)`, whose lower half is
`θ / (Cθ · a ^ (-ε_int)) ≤ M(V, t)`.  That is *weaker*: `a ^ (-ε_int)` is polynomial while
`Kakeya.plankAngleScaleB a = exp((log a⁻¹) ^ (3/4))` is sub-polynomial, so the stop-scale form does
not follow.

The whole dependence of the concentration chain on the stop scale is the *absorption* step
(`Plank.exists_combined_absorption`), which is already isolated as a hypothesis by
`Plank.localAngleConcentration_of_saturated_free`.  This file discharges that hypothesis at a
polynomial stability constant instead:

`Cstar · Mtyp = 8 Cθ a^{-ε_s} · 2(N+1)` with `N ≤ log₂(16 C Cθ a^{-ε_s}) + 1`, so the product is
`≲ a^{-ε_s} · log a⁻¹`, and one logarithm is absorbed by any strictly larger power.  Hence the
concentration is available at every exponent `η > ε_s`, at a constant `Ceta` fixed before every
geometric datum.

This is the honest route for the assembly of GWZ Lemma 6.13: it spends no new power of `a` — the
exponent `η` at which the concentration is used is `η_L = η + 5ε_work/4`, which already exceeds
`ε_int = ε_work/4`.

Note the contrast with `Plank.exists_delta_absorption_fails`: that obstruction is about a stability
constant `Cθ · δ ^ (-ε)` at a *second* shading scale `δ` allowed to be arbitrarily smaller than `a`,
where no power of `a` alone can dominate.  The development carries no such second scale — the
paper's `δ` is `a` throughout, which was a typo in the source — so the obstruction does not apply
and the absorption is available.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

/-! ## Hypothesis (5) and Item 2 at a *free* angular stability constant

`Plank.localAngleConcentration_of_saturated` hard-codes its angular stability constant as
`Kakeya.plankAngleScaleB a`, and `Plank.localAngleConcentration_of_saturated_scaled` relaxes it only
to `K · Kakeya.plankAngleScaleB a` for a fixed `K ≥ 1`.  Neither form is usable by the assembly of
GWZ Lemma 6.13: what `Kakeya.representativeWitness_strong_uniform` supplies is
`Kakeya.IsTypicalPlankAngle … (Cθ · a ^ (-ε)) …`, i.e. stability at `Cstab = Cθ · a ^ (-ε)`, and

`Cθ · a ^ (-ε) ≤ K · Kakeya.plankAngleScaleB a`

is **false**: the left side is polynomial in `a⁻¹` and the right side sub-polynomial in `a⁻¹`.

This section removes the hard-coding, and records exactly what it costs.

* `Plank.exists_localTypicalIntersectionAngle_of_localStability_free` takes `Cstab : ℝ` with
  `1 ≤ Cstab` completely free and takes the **absorption budget as a hypothesis** rather than
  deriving it from `Kakeya.plankAngleScaleB`.  Nothing else in the chain needed changing:
  `Plank.exists_bandCount_uniform` and `Plank.exists_typicalIntersectionAngle_of_stableFibres`
  already carry their stability constant free.
* `Plank.localAngleConcentration_of_saturated_free` is the saturated form.  The absorption
  constant `Ceta` moves from an internal choice to a *parameter*, alongside `Cang`.  Instantiating
  `Cstab := Kakeya.plankAngleScaleB a` and discharging the absorption hypothesis with
  `Plank.exists_combined_absorption` recovers `Plank.localAngleConcentration_of_saturated` verbatim.
  The Item 2 endpoint that used to sit on top of this with `Cstab` free was retired with the rest of
  the fixed-threshold layer; the live consumer is
  `Plank.localAngleConcentration_trimmed_of_slabLocal_poly`, which discharges the absorption
  hypothesis at the polynomial stability constant the witness actually supplies.

**What the generalisation costs.**  Not a constant.  The absorption hypothesis
`(8 Cstab).toNNReal · 2(N+1) ≤ Ceta · a ^ (-η)` is what makes the whole dense-box layer work, and at
`Cstab = Cθ · a ^ (-ε)` it needs `η` to exceed `ε`, which the two independently quantified exponents
do not give in general.  The honest fix is not to relax the constant but to let the
`Plank.LocalAngleConcentration` budget carry its own power of `a`, which would then appear as a
dense-box entry in the Item 2 exponent budget.  That is a statement-level decision about
`Plank.LocalAngleConcentration` and is deliberately not taken here.

`Plank.exists_delta_absorption_fails` below is the sharper obstruction for a *second* scale
`δ ≤ a`, which the paper's `δ` was mistakenly read as; since `δ` is `a` throughout, that theorem is
retained only as the record of why a free second scale would be fatal.  See
`Plank.exists_combined_absorption_poly` for the route that is actually taken.
-/

/-! ### The unsatisfiability of a `δ`-free absorption budget -/

/-- **A `δ`-free absorption budget cannot dominate `Cθ · δ ^ (-ε)`.**  For any budget `B` there is a
scale `δ ∈ (0, a]` with `B < Cθ · δ ^ (-ε)`.  Applied at `B = Ceta · a ^ (-η)`, this is the precise
obstruction to discharging the absorption hypothesis of
`Plank.exists_localTypicalIntersectionAngle_of_localStability_free` at the witness's stability
constant `Cstab = Cθ · δ ^ (-ε)`: no uniform `Ceta`, and no power of `a` alone, is large enough for
every admissible `δ`. -/
theorem exists_delta_absorption_fails (Cθ B a : ℝ≥0) (hCθ : 0 < Cθ) (ha : 0 < a) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ a ∧ B < Cθ * δ ^ (-ε) := by
  have hCθ_pos : (0 : ℝ) < (Cθ : ℝ) := by exact_mod_cast hCθ
  have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hCθ_ne_zero : (Cθ : ℝ) ≠ 0 := by linarith
  have hε_ne_zero : ε ≠ 0 := by linarith
  have hneg_ε_nonpos : -(ε : ℝ) ≤ 0 := by linarith
  have hneg_ε_inv_nonpos : -(ε : ℝ)⁻¹ ≤ 0 := by
    have hε_inv_pos : 0 < (ε : ℝ)⁻¹ := inv_pos.mpr hε
    linarith
  set t_real : ℝ := max (1 : ℝ) ((B : ℝ) / (Cθ : ℝ) + 1) with ht_real_def
  have hB_lt_Cθ_mul_t_real : (B : ℝ) < (Cθ : ℝ) * t_real := by
    have hsum : (B : ℝ) / (Cθ : ℝ) + 1 ≤ t_real := le_max_right _ _
    have h_eq : (Cθ : ℝ) * ((B : ℝ) / (Cθ : ℝ) + 1) = (B : ℝ) + (Cθ : ℝ) := by
      field_simp [hCθ_ne_zero]
    calc
      (B : ℝ) < (B : ℝ) + (Cθ : ℝ) := by nlinarith
      _ = (Cθ : ℝ) * ((B : ℝ) / (Cθ : ℝ) + 1) := by
        field_simp [hCθ_ne_zero]
      _ ≤ (Cθ : ℝ) * t_real := mul_le_mul_of_nonneg_left hsum (by positivity)
  have ht_real_one_le : (1 : ℝ) ≤ t_real := le_max_left _ _
  have ht_real_pos : 0 < t_real := by linarith
  set δ₀_real : ℝ := t_real ^ (-(ε : ℝ)⁻¹) with hδ₀_real_def
  have hδ₀_real_pos : 0 < δ₀_real := by
    rw [hδ₀_real_def]
    exact Real.rpow_pos_of_pos ht_real_pos _
  have hδ₀_real_le_one : δ₀_real ≤ 1 := by
    calc
      δ₀_real = t_real ^ (-(ε : ℝ)⁻¹) := rfl
      _ ≤ (1 : ℝ) ^ (-(ε : ℝ)⁻¹) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) ht_real_one_le hneg_ε_inv_nonpos
      _ = (1 : ℝ) := by norm_num
  set δ_real : ℝ := min (a : ℝ) δ₀_real with hδ_real_def
  have hδ_real_pos : 0 < δ_real := by
    refine lt_min_iff.mpr ⟨ha_pos, hδ₀_real_pos⟩
  have hδ_real_le_a : δ_real ≤ (a : ℝ) := by
    exact min_le_left _ _
  have hδ_real_le_δ₀_real : δ_real ≤ δ₀_real := by
    exact min_le_right _ _
  have hδ₀_rpow_neg_ε_le_δ_rpow_neg_ε : δ₀_real ^ (-(ε : ℝ)) ≤ δ_real ^ (-(ε : ℝ)) := by
    refine Real.rpow_le_rpow_of_nonpos hδ_real_pos hδ_real_le_δ₀_real hneg_ε_nonpos
  have hδ₀_rpow_neg_ε_eq_t_real : δ₀_real ^ (-(ε : ℝ)) = t_real := by
    calc
      δ₀_real ^ (-(ε : ℝ)) = (t_real ^ (-(ε : ℝ)⁻¹)) ^ (-(ε : ℝ)) := by rfl
      _ = t_real ^ ((-(ε : ℝ)⁻¹) * (-(ε : ℝ))) := by
        rw [Real.rpow_mul (by positivity : 0 ≤ t_real) (-(ε : ℝ)⁻¹) (-(ε : ℝ))]
      _ = t_real ^ ((1 : ℝ) : ℝ) := by
        congr 1
        field_simp [hε_ne_zero]
      _ = t_real := by norm_num
  have hB_lt_Cθ_mul_δ_rpow_neg_ε : (B : ℝ) < (Cθ : ℝ) * (δ_real ^ (-(ε : ℝ))) := by
    calc
      (B : ℝ) < (Cθ : ℝ) * t_real := hB_lt_Cθ_mul_t_real
      _ = (Cθ : ℝ) * (δ₀_real ^ (-(ε : ℝ))) := by rw [hδ₀_rpow_neg_ε_eq_t_real]
      _ ≤ (Cθ : ℝ) * (δ_real ^ (-(ε : ℝ))) :=
        mul_le_mul_of_nonneg_left hδ₀_rpow_neg_ε_le_δ_rpow_neg_ε (by positivity)
      _ = (Cθ : ℝ) * (δ_real ^ (-(ε : ℝ))) := rfl
  have hδ_nonneg : 0 ≤ δ_real := by linarith
  let δ : ℝ≥0 := ⟨δ_real, hδ_nonneg⟩
  have hδ_eq : (δ : ℝ) = δ_real := rfl
  have hδ_pos : 0 < δ := by
    exact_mod_cast hδ_real_pos
  have hδ_le_a : δ ≤ a := by
    exact_mod_cast hδ_real_le_a
  have hB_lt_Cθ_mul_δ_rpow : B < Cθ * δ ^ (-ε) := by
    have h_real : (B : ℝ) < (Cθ : ℝ) * ((δ : ℝ) ^ (-(ε : ℝ))) := by
      simpa [hδ_eq] using hB_lt_Cθ_mul_δ_rpow_neg_ε
    exact_mod_cast h_real
  exact ⟨δ, hδ_pos, hδ_le_a, hB_lt_Cθ_mul_δ_rpow⟩

/-! ### Hypothesis (5) from local stability, at a free stability constant -/

open scoped Classical in
/-- **Hypothesis (5) from local stability, with the stability constant free.**  Exactly
`Plank.exists_localTypicalIntersectionAngle_of_localStability_scaled` with
`K · Kakeya.plankAngleScaleB a` replaced by an arbitrary `Cstab ≥ 1` and with the absorption budget
supplied as the hypothesis `habs` instead of being produced by
`Plank.exists_combined_absorption_scaled`.

The two inputs that were already free of the stability scale are used unchanged:
`Plank.exists_bandCount_uniform` produces the ladder length `N` at any `Cstab ≥ 1`, and
`Plank.exists_typicalIntersectionAngle_of_stableFibres` takes `Cstab` as a bare real.  So the whole
dependence on `Kakeya.plankAngleScaleB` was concentrated in the absorption step, which is now the
caller's obligation.

`habs` is quantified over every `N` obeying the ladder bound because `N` is chosen inside; this is
the exact shape of the conclusion of `Plank.exists_combined_absorption`, so instantiating
`Cstab := Kakeya.plankAngleScaleB a` discharges it. -/
theorem exists_localTypicalIntersectionAngle_of_localStability_free
    (Cang : ℝ≥0) (hCang : 1 ≤ Cang) {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι σ : Type*}
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (𝒯' : Finset σ) (D : σ → Finset (Fin 3 → ℤ))
    (Tq : σ → (Fin 3 → ℤ) → Finset ι)
    (Z : σ → (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (A Cstab : ℝ) (Ceta : ℝ≥0) (η : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hA : 2 ≤ A) (hCstab : 1 ≤ Cstab)
    (habs : ∀ N : ℕ, (N : ℝ) ≤ Real.logb 2 (16 * (Cang : ℝ) * Cstab) + 1 →
      (((8 * Cstab).toNNReal : ℝ≥0) : ENNReal) * (((2 * (N + 1 : ℕ) : ℕ) : ℝ≥0) : ENNReal)
        ≤ (Ceta : ENNReal) * (a : ENNReal) ^ (-η))
    (hang_global : Kakeya.HasMaxPlankAngleBound s Y V θ Cang)
    (hTs : ∀ u ∈ 𝒯', ∀ q ∈ D u, Tq u q ⊆ s)
    (hZsub : ∀ u ∈ 𝒯', ∀ q ∈ D u, ∀ i ∈ Tq u q, (Z u q i).shade ⊆ (Y i).shade)
    (hstab : ∀ u ∈ 𝒯', ∀ q ∈ D u, LocalShadeFibreStable V (Tq u q) (Z u q) θ Cstab A) :
    LocalAngleConcentration V θ 𝒯' D Tq Z Ceta η := by
  -- Step 1: obtain N from exists_bandCount_uniform
  obtain ⟨N, hN, hNlog⟩ := Plank.exists_bandCount_uniform (a := a) (b := b) (θ := θ) (Cang := Cang)
    Cstab ha hb hθ hCang hCstab
  -- Step 2: define Cstar and Mtyp
  set Cstar := (8 * Cstab).toNNReal with hCstar_def
  set Mtyp := ((2 * (N + 1 : ℕ) : ℕ) : ℝ≥0) with hMtyp_def
  have hCstar_nonneg : 0 ≤ 8 * Cstab := by
    have hCstab_nonneg : 0 ≤ Cstab := by linarith
    nlinarith
  have h_Cstar_real : (Cstar : ℝ) = 8 * Cstab := by
    rw [hCstar_def]
    simpa using Real.coe_toNNReal (8 * Cstab) hCstar_nonneg
  have h_product_bound : (Cstar : ENNReal) * (Mtyp : ENNReal)
      ≤ (Ceta : ENNReal) * (a : ENNReal) ^ (-η) := by
    have htemp := habs N hNlog
    simpa [hCstar_def, hMtyp_def] using htemp
  -- Step 3: for each u ∈ 𝒯', q ∈ D u, apply exists_typicalIntersectionAngle_of_stableFibres
  have h_ex : ∀ (u : σ), u ∈ 𝒯' → ∀ (q : (Fin 3 → ℤ)), q ∈ D u →
      ∃ (θ0 : ℝ), ((a / b : ℝ≥0) : ℝ) ≤ θ0 ∧ θ0 ≤ 1 ∧ (θ : ℝ) ≤ (Cstar : ℝ) * θ0 ∧
        (∑ i ∈ Tq u q, ∑ j ∈ Tq u q, volume ((Z u q i).shade ∩ (Z u q j).shade))
          ≤ (Mtyp : ENNReal) * (∑ i ∈ Tq u q, ∑ j ∈ Tq u q with
              (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
                Prism3D.angle (V i) (V j) ≤ 2 * θ0),
            volume ((Z u q i).shade ∩ (Z u q j).shade)) := by
    intro u hu q hq
    have hTsub : Tq u q ⊆ s := hTs u hu q hq
    have hZsub' : ∀ i ∈ Tq u q, (Z u q i).shade ⊆ (Y i).shade := hZsub u hu q hq
    have hang_local : Kakeya.HasMaxPlankAngleBound (Tq u q) (Z u q) V θ Cang :=
      hang_global.mono hTsub hZsub'
    have hstab_local : LocalShadeFibreStable V (Tq u q) (Z u q) θ Cstab A := hstab u hu q hq
    obtain ⟨θ0, hθ0_ab, hθ0_1, hθ0_cmp, hθ0_conc⟩ :=
      exists_typicalIntersectionAngle_of_stableFibres (V := V) (T := Tq u q) (Z := Z u q)
        (θ := θ) (Cang := Cang) (Cstab := Cstab) (A := A) (N := N)
        ha hb hθ1 hA hCstab hang_local hstab_local hN
    have hθ0_cmp' : (θ : ℝ) ≤ (Cstar : ℝ) * θ0 := by
      calc
        (θ : ℝ) ≤ 8 * Cstab * θ0 := hθ0_cmp
        _ = (8 * Cstab) * θ0 := by ring
        _ = (Cstar : ℝ) * θ0 := by rw [h_Cstar_real]
    refine ⟨θ0, hθ0_ab, hθ0_1, hθ0_cmp', ?_⟩
    simpa [hMtyp_def] using hθ0_conc
  -- Step 4: Choose θ0 function via classical choice
  let θ0 : σ → (Fin 3 → ℤ) → ℝ := fun u q =>
    if hu : u ∈ 𝒯' then
      if hq : q ∈ D u then
        Classical.choose (h_ex u hu q hq)
      else 1
    else 1
  have hθ0_props : ∀ u ∈ 𝒯', ∀ q ∈ D u,
      ((a / b : ℝ≥0) : ℝ) ≤ θ0 u q ∧ θ0 u q ≤ 1 ∧ (θ : ℝ) ≤ (Cstar : ℝ) * θ0 u q ∧
        (∑ i ∈ Tq u q, ∑ j ∈ Tq u q, volume ((Z u q i).shade ∩ (Z u q j).shade))
          ≤ (Mtyp : ENNReal) * (∑ i ∈ Tq u q, ∑ j ∈ Tq u q with
              (θ0 u q - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
                Prism3D.angle (V i) (V j) ≤ 2 * θ0 u q),
            volume ((Z u q i).shade ∩ (Z u q j).shade)) := by
    intro u hu q hq
    have hθ0_eq : θ0 u q = Classical.choose (h_ex u hu q hq) := by
      simp [θ0, hu, hq]
    have hspec := Classical.choose_spec (h_ex u hu q hq)
    simpa [hθ0_eq] using hspec
  -- Step 5: Assemble the LocalAngleConcentration
  refine ⟨θ0, Cstar, Mtyp, h_product_bound, ?_⟩
  exact hθ0_props

open scoped Classical in
/-- **Hypothesis (5) for saturated families, with the stability constant free.**  The saturated
counterpart of `Plank.exists_localTypicalIntersectionAngle_of_localStability_free`: the local
stability clause is replaced by a *global* one at the same free `Cstab`, transferred box by box
through `Plank.shadeFibre_subset_of_saturated` and `Plank.localShadeFibreStable_of_fibreEq`, which
lose nothing.

This is the form the assembly of GWZ Lemma 6.13 can actually feed, since
`Kakeya.representativeWitness_strong_uniform` returns a global stability clause at
`Cstab = Cθ · δ ^ (-ε)` — subject to `habs`, which
`Plank.exists_delta_absorption_fails` shows is not free. -/
theorem localAngleConcentration_of_saturated_free
    (Cang : ℝ≥0) (hCang : 1 ≤ Cang) {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι σ : Type*}
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (𝒯' : Finset σ) (D : σ → Finset (Fin 3 → ℤ))
    (R : σ → (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3)))
    (Tq : σ → (Fin 3 → ℤ) → Finset ι)
    (Z : σ → (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (A Cstab : ℝ) (Ceta : ℝ≥0) (η : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hA : 2 ≤ A) (hCstab : 1 ≤ Cstab)
    (habs : ∀ N : ℕ, (N : ℝ) ≤ Real.logb 2 (16 * (Cang : ℝ) * Cstab) + 1 →
      (((8 * Cstab).toNNReal : ℝ≥0) : ENNReal) * (((2 * (N + 1 : ℕ) : ℕ) : ℝ≥0) : ENNReal)
        ≤ (Ceta : ENNReal) * (a : ENNReal) ^ (-η))
    (hang_global : Kakeya.HasMaxPlankAngleBound s Y V θ Cang)
    (hTs : ∀ u ∈ 𝒯', ∀ q ∈ D u, Tq u q ⊆ s)
    (hZeq : ∀ u ∈ 𝒯', ∀ q ∈ D u, ∀ i ∈ Tq u q, (Z u q i).shade = (Y i).shade ∩ R u q)
    (hsat : ∀ u ∈ 𝒯', ∀ q ∈ D u, ∀ i ∈ s, ∀ x ∈ (Y i).shade, x ∈ R u q → i ∈ Tq u q)
    (hglob_stab : ∀ x ∈ ⋃ i ∈ s, (Y i).shade, ∀ t ⊆ Kakeya.shadeFibre s Y x,
      A⁻¹ * ((Kakeya.shadeFibre s Y x).card : ℝ) ≤ (t.card : ℝ) →
        (θ : ℝ) / Cstab ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)) :
    LocalAngleConcentration V θ 𝒯' D Tq Z Ceta η := by
  -- From hZeq we get the ⊆ condition that
  -- exists_localTypicalIntersectionAngle_of_localStability_free needs
  have hZsub : ∀ u ∈ 𝒯', ∀ q ∈ D u, ∀ i ∈ Tq u q, (Z u q i).shade ⊆ (Y i).shade := by
    intro u hu q hq i hi
    rw [hZeq u hu q hq i hi]
    exact Set.inter_subset_left
  have hApos : 0 < A := by linarith
  -- For each u ∈ 𝒯', q ∈ D u, use shadeFibre_subset_of_saturated +
  -- localShadeFibreStable_of_fibreEq
  -- to turn the global stability hypothesis into local stability
  have hstab_local : ∀ u ∈ 𝒯', ∀ q ∈ D u,
    LocalShadeFibreStable V (Tq u q) (Z u q) θ Cstab A := by
    intro u hu q hq
    have hTs_q : Tq u q ⊆ s := hTs u hu q hq
    have hZsub_q : ∀ i ∈ Tq u q, (Z u q i).shade ⊆ (Y i).shade := hZsub u hu q hq
    have hfib : ∀ x ∈ ⋃ i ∈ Tq u q, (Z u q i).shade,
      Kakeya.shadeFibre s Y x ⊆ Kakeya.shadeFibre (Tq u q) (Z u q) x := by
      intro x hx
      exact shadeFibre_subset_of_saturated (R u q) (hZeq u hu q hq) (hsat u hu q hq) hx
    have hglob_q : ∀ x ∈ ⋃ i ∈ s, (Y i).shade, ∀ t ⊆ Kakeya.shadeFibre s Y x,
      A⁻¹ * ((Kakeya.shadeFibre s Y x).card : ℝ) ≤ (t.card : ℝ) →
        (θ : ℝ) / Cstab ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ) :=
      hglob_stab
    exact localShadeFibreStable_of_fibreEq hApos hTs_q hZsub_q hfib hglob_q
  -- Now exists_localTypicalIntersectionAngle_of_localStability_free gives us the
  -- LocalAngleConcentration
  exact exists_localTypicalIntersectionAngle_of_localStability_free Cang hCang s V Y 𝒯' D Tq Z
      A Cstab Ceta η
    ha hb hθ hθ1 hA hCstab habs hang_global hTs hZsub hstab_local

end Plank

namespace Plank

variable {ι : Type*}

/-! ## The polynomial absorption budget -/

/-- **A single logarithm is absorbed by any positive power.**  For `0 < a` and `0 < d`,
`Real.log a⁻¹ ≤ d⁻¹ * (a : ℝ) ^ (-d)`. -/
theorem log_inv_le_rpow_neg {a : ℝ≥0} (ha : 0 < a) {d : ℝ} (hd : 0 < d) :
    Real.log (a : ℝ)⁻¹ ≤ d⁻¹ * (a : ℝ) ^ (-d) := by
  have haR : (0 : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast ha.le
  calc
    Real.log (a : ℝ)⁻¹ ≤ ((a : ℝ)⁻¹) ^ d / d :=
      Real.log_le_rpow_div (inv_nonneg.mpr haR) hd
    _ = d⁻¹ * (a : ℝ) ^ (-d) := by
      rw [Real.inv_rpow haR, Real.rpow_neg haR]
      rw [div_eq_inv_mul]

/-- `logb₂ (x·y) ≤ logb₂ ((x+1)·y)` for `0 ≤ x`, `0 < y`, `1 ≤ y`. -/
private lemma logb_le_logb_mul_add_one {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hyb : 1 ≤ y) :
    Real.logb 2 (x * y) ≤ Real.logb 2 ((x + 1) * y) := by
  have hxy : x * y ≤ (x + 1) * y :=
    mul_le_mul_of_nonneg_right (by linarith) hy.le
  by_cases h : 0 < x * y
  · exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) h hxy
  · have hxyeq : x * y = 0 := by
      have hxy0 : 0 ≤ x * y := mul_nonneg hx hy.le
      linarith
    rw [hxyeq]
    have h1 : (1 : ℝ) ≤ (x + 1) * y := by
      calc
        (1 : ℝ) ≤ x + 1 := by linarith
        _ ≤ (x + 1) * y := le_mul_of_one_le_right (by linarith : 0 ≤ x + 1) hyb
    have hnn : 0 ≤ Real.logb 2 ((x + 1) * y) :=
      Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) h1
    simpa [Real.logb] using hnn

/-- `logb₂ (a ^ (-s)) = s · log a⁻¹ / log 2` for `0 < a`. -/
private lemma logb_rpow_neg_eq {a : ℝ} (ha : 0 < a) (s : ℝ) :
    Real.logb 2 (a ^ (-s)) = s * Real.log (a⁻¹) / Real.log 2 := by
  rw [Real.logb_rpow_eq_mul_logb_of_pos ha, Real.logb]
  have hlog : Real.log a = -Real.log (a⁻¹) := by linarith [Real.log_inv a]
  rw [hlog]
  ring

/-- **The combined absorption at a polynomial stability constant, real-valued form.**  The scalar
content of `Plank.exists_combined_absorption_poly`: for `0 < ε_s < η` there is a uniform
`Ceta ≥ 1`, depending only on `Cang`, `Cstab0`, `ε_s` and `η`, with

`8 · (Cstab0 · a^{-ε_s}) · 2(N+1) ≤ Ceta · a^{-η}`

for every `0 < a < 1` and every `N` obeying the ladder bound.  The gap `η - ε_s > 0` is what pays
for the ladder length `N ≈ ε_s · log₂ a⁻¹`. -/
theorem exists_combined_absorption_poly_real (Cang Cstab0 : ℝ≥0) (hCstab0 : 1 ≤ Cstab0)
    {εs η : ℝ} (hεs : 0 < εs) (hlt : εs < η) :
    ∃ Ceta : ℝ, 1 ≤ Ceta ∧ ∀ {a : ℝ≥0}, 0 < a → a < 1 → ∀ N : ℕ,
      (N : ℝ) ≤ Real.logb 2 (16 * (Cang : ℝ) * ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs))) + 1 →
      (8 * ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs))) * (2 * ((N : ℝ) + 1)) ≤ Ceta * (a : ℝ) ^ (-η) := by
  let d : ℝ := η - εs
  have hd : 0 < d := by dsimp [d]; linarith
  let Ac : ℝ := (16 : ℝ) * (Cang : ℝ) * (Cstab0 : ℝ) + 1
  have hAcpos : 0 < Ac := by dsimp [Ac]; positivity
  have hAc_ge1 : (1 : ℝ) ≤ Ac := by
    dsimp [Ac]
    have h0 : 0 ≤ (16 : ℝ) * (Cang : ℝ) * (Cstab0 : ℝ) := by positivity
    linarith
  let K1 : ℝ := Real.logb 2 Ac
  have hK1ge0 : 0 ≤ K1 := by
    dsimp [K1]
    rw [Real.logb]
    exact div_nonneg (Real.log_nonneg hAc_ge1) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  let Ceta0 : ℝ := (2 * K1 + 4) + (2 * εs / Real.log 2) * d⁻¹
  let Ceta : ℝ := max 1 (8 * (Cstab0 : ℝ) * Ceta0)
  refine ⟨Ceta, ?_, ?_⟩
  · dsimp [Ceta]
    exact le_max_left _ _
  · intro a ha ha1 N hN
    have haRpos : 0 < (a : ℝ) := by exact_mod_cast ha
    have haR_lt_one : (a : ℝ) < 1 := by exact_mod_cast ha1
    have hCstab0R_pos : (0 : ℝ) < (Cstab0 : ℝ) :=
      lt_of_lt_of_le zero_lt_one (by exact_mod_cast hCstab0)
    let B : ℝ := (a : ℝ) ^ (-εs)
    have hBpos : 0 < B := by dsimp [B]; exact Real.rpow_pos_of_pos haRpos _
    have hB_ge1 : (1 : ℝ) ≤ B := one_le_rpow_neg_of_lt_one ha ha1 hεs
    let A : ℝ := (16 : ℝ) * (Cang : ℝ) * (Cstab0 : ℝ)
    have hAnonneg : 0 ≤ A := by dsimp [A]; positivity
    have hArg : 16 * (Cang : ℝ) * ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs)) = A * B := by
      dsimp [A, B]
      ring
    have hNm : (N : ℝ) ≤ Real.logb 2 (A * B) + 1 := by
      rw [hArg] at hN
      exact hN
    have hlogb_le : Real.logb 2 (A * B) ≤ Real.logb 2 (Ac * B) :=
      logb_le_logb_mul_add_one hAnonneg hBpos hB_ge1
    have h2B : 2 * Real.logb 2 B ≤ (2 * εs / Real.log 2) * (d⁻¹ * (a : ℝ) ^ (-d)) := by
      have hfac : 0 ≤ (2 * εs / Real.log 2) := by positivity
      calc
        2 * Real.logb 2 B = 2 * (εs * Real.log (a : ℝ)⁻¹ / Real.log 2) := by
          dsimp [B]
          rw [logb_rpow_neg_eq haRpos εs]
        _ = (2 * εs / Real.log 2) * Real.log (a : ℝ)⁻¹ := by ring
        _ ≤ (2 * εs / Real.log 2) * (d⁻¹ * (a : ℝ) ^ (-d)) := by
          exact mul_le_mul_of_nonneg_left (log_inv_le_rpow_neg ha hd) hfac
    have hK14 : 0 ≤ 2 * K1 + 4 := by linarith [hK1ge0]
    have hconst_le : (2 * K1 + 4) ≤ (2 * K1 + 4) * (a : ℝ) ^ (-d) := by
      have hpw : (1 : ℝ) ≤ (a : ℝ) ^ (-d) := one_le_rpow_neg_of_lt_one ha ha1 hd
      calc
        (2 * K1 + 4) = (2 * K1 + 4) * 1 := by ring
        _ ≤ (2 * K1 + 4) * (a : ℝ) ^ (-d) :=
          mul_le_mul_of_nonneg_left hpw hK14
    have hMain : 2 * ((N : ℝ) + 1) ≤ Ceta0 * (a : ℝ) ^ (-d) := by
      calc
        2 * ((N : ℝ) + 1) ≤ 2 * Real.logb 2 (A * B) + 4 := by nlinarith [hNm]
        _ ≤ 2 * Real.logb 2 (Ac * B) + 4 := by nlinarith [hlogb_le]
        _ = 2 * (Real.logb 2 Ac + Real.logb 2 B) + 4 := by
          rw [Real.logb_mul (ne_of_gt hAcpos) (ne_of_gt hBpos)]
        _ = (2 * K1 + 4) + 2 * Real.logb 2 B := by dsimp [K1]; ring
        _ ≤ (2 * K1 + 4) + (2 * εs / Real.log 2) * (d⁻¹ * (a : ℝ) ^ (-d)) := by
          nlinarith [h2B]
        _ ≤ Ceta0 * (a : ℝ) ^ (-d) := by
          dsimp [Ceta0]
          nlinarith [hconst_le]
    calc
      (8 * ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs))) * (2 * ((N : ℝ) + 1))
          = (8 * ((Cstab0 : ℝ) * B)) * (2 * ((N : ℝ) + 1)) := by rfl
      _ ≤ (8 * ((Cstab0 : ℝ) * B)) * (Ceta0 * (a : ℝ) ^ (-d)) := by
            exact mul_le_mul_of_nonneg_left hMain (by positivity)
      _ = (8 * (Cstab0 : ℝ) * Ceta0) * (B * (a : ℝ) ^ (-d)) := by ring
      _ = (8 * (Cstab0 : ℝ) * Ceta0) * (a : ℝ) ^ (-(εs + d)) := by
            congr 1
            dsimp [B]
            rw [← Real.rpow_add haRpos]
            congr 1
            ring
      _ = (8 * (Cstab0 : ℝ) * Ceta0) * (a : ℝ) ^ (-η) := by
            congr 1
            congr 1
            ring
      _ ≤ Ceta * (a : ℝ) ^ (-η) := by
            exact mul_le_mul_of_nonneg_right (by dsimp [Ceta]; exact le_max_right _ _)
              (by positivity)

/-- **The combined absorption at a polynomial stability constant.**
`Plank.exists_combined_absorption_poly_real` pushed through the `ℝ≥0` / `ENNReal` coercions, in
exactly the shape of the `habs` hypothesis of
`Plank.localAngleConcentration_of_saturated_free`. -/
theorem exists_combined_absorption_poly (Cang Cstab0 : ℝ≥0) (hCstab0 : 1 ≤ Cstab0)
    {εs η : ℝ} (hεs : 0 < εs) (hlt : εs < η) :
    ∃ Ceta : ℝ≥0, 0 < Ceta ∧ ∀ {a : ℝ≥0}, 0 < a → a < 1 → ∀ N : ℕ,
      (N : ℝ) ≤ Real.logb 2 (16 * (Cang : ℝ) * ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs))) + 1 →
      (((8 * ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs))).toNNReal : ℝ≥0) : ENNReal) *
          (((2 * (N + 1 : ℕ) : ℕ) : ℝ≥0) : ENNReal)
        ≤ (Ceta : ENNReal) * (a : ENNReal) ^ (-η) := by
  obtain ⟨CetaR, hCetaR1, hreal⟩ := exists_combined_absorption_poly_real Cang Cstab0 hCstab0 hεs hlt
  have hCetaRpos : (0 : ℝ) < CetaR := by linarith
  refine ⟨CetaR.toNNReal, Real.toNNReal_pos.mpr hCetaRpos, ?_⟩
  intro a ha ha1 N hN
  let x : ℝ≥0 := (8 * ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs))).toNNReal
  let y : ℝ≥0 := (2 * (N + 1 : ℕ) : ℕ)
  have h_ne_zero : (a : ℝ≥0) ≠ 0 := by exact_mod_cast ha.ne'
  have hx : (x : ℝ) = 8 * ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs)) := by
    have hnonneg : 0 ≤ 8 * ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs)) := by positivity
    exact Real.coe_toNNReal _ hnonneg
  have hy : (y : ℝ) = 2 * ((N : ℝ) + 1) := by
    dsimp [y, x]
    push_cast
    ring
  have hC : ((CetaR.toNNReal : ℝ≥0) : ℝ) = CetaR :=
    Real.coe_toNNReal CetaR (by linarith)
  have hreal' : (8 * ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs))) * (2 * ((N : ℝ) + 1))
      ≤ CetaR * (a : ℝ) ^ (-η) := hreal ha ha1 N hN
  have h_nn : x * y ≤ CetaR.toNNReal * (a ^ (-η : ℝ) : ℝ≥0) := by
    have hℝ : (x : ℝ) * (y : ℝ) ≤ ((CetaR.toNNReal * (a ^ (-η : ℝ) : ℝ≥0) : ℝ≥0) : ℝ) := by
      calc
        (x : ℝ) * (y : ℝ) = (8 * ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs))) * (2 * ((N : ℝ) + 1)) := by
          rw [hx, hy]
        _ ≤ CetaR * (a : ℝ) ^ (-η) := hreal'
        _ = ((CetaR.toNNReal : ℝ≥0) : ℝ) * (((a ^ (-η : ℝ) : ℝ≥0) : ℝ)) := by simp [hC]
        _ = ((CetaR.toNNReal * (a ^ (-η : ℝ) : ℝ≥0) : ℝ≥0) : ℝ) := by simp
    exact NNReal.coe_le_coe.mpr hℝ
  change (x : ENNReal) * (y : ENNReal) ≤ (CetaR.toNNReal : ENNReal) * (a : ENNReal) ^ (-η)
  calc
    (x : ENNReal) * (y : ENNReal) = (x * y : ENNReal) := by simp
    _ ≤ ((CetaR.toNNReal * (a ^ (-η : ℝ) : ℝ≥0) : ℝ≥0) : ENNReal) := ENNReal.coe_le_coe.mpr h_nn
    _ = ((CetaR.toNNReal : ℝ≥0) : ENNReal) * ((a ^ (-η : ℝ) : ℝ≥0) : ENNReal) := by simp
    _ = (CetaR.toNNReal : ENNReal) * (a : ENNReal) ^ (-η) := by
      simp [ENNReal.coe_rpow_of_ne_zero h_ne_zero (-η)]

/-! ## The stability clause of a two-sided typical angle -/

/-- **The lower half of a typical plank angle is the angular-stability clause.**  Unfolding
`Kakeya.IsTypicalPlankAngle` at a point of the shading union and at a sub-fibre retaining an
`A⁻¹`-fraction gives `θ ≤ C · M(V, t)`, i.e. `θ / C ≤ M(V, t)`.  This is the exact hypothesis shape
of `Plank.localAngleConcentration_of_saturated_free` and of
`Plank.localStability_trimmed_inSlabFamilyC`, at `Cstab := C`. -/
theorem localStability_of_isTypicalPlankAngle {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {V : ι → Plank a b hab hb1} {θ C A : ℝ≥0} (hC : 0 < C)
    (h : Kakeya.IsTypicalPlankAngle s Y V θ C A) :
    ∀ x ∈ ⋃ i ∈ s, (Y i).shade, ∀ t ⊆ Kakeya.shadeFibre s Y x,
      (A : ℝ)⁻¹ * ((Kakeya.shadeFibre s Y x).card : ℝ) ≤ (t.card : ℝ) →
        (θ : ℝ) / (C : ℝ) ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ) := by
  intro x hx t ht hcard
  let F : Finset ι := Kakeya.shadeFibre s Y x
  have hF : A⁻¹ * (F.card : ℝ≥0) ≤ (t.card : ℝ≥0) := by
    have hR : ((A⁻¹ * (F.card : ℝ≥0) : ℝ≥0) : ℝ) ≤ ((t.card : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_mul, NNReal.coe_inv]
      simpa [F] using hcard
    exact_mod_cast hR
  have hle : θ ≤ C * (Kakeya.maxPlankAngle V t : ℝ≥0) :=
    (h x hx).2 t ht hF |>.1
  have hleR : (θ : ℝ) ≤ (C : ℝ) * ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ) := by
    exact_mod_cast hle
  rw [div_le_iff₀ (by exact_mod_cast hC)]
  simpa [mul_comm] using hleR

/-! ## Slab-local concentration at a polynomial stability constant -/

open scoped Classical in
/-- **Hypothesis (5) on the selected boxes of one slab, at a polynomial stability constant.**

`Plank.localAngleConcentration_trimmed_of_slabLocal` with the stop-scale stability clause replaced
by the polynomial one that `Kakeya.plankReduction_preassembly` supplies, the absorption being
discharged by `Plank.exists_combined_absorption_poly`.  Everything else is unchanged: the max-angle
bound and the stability clause transfer to the trimmed enlarged family at retention `1`
(`Plank.hasMaxPlankAngleBound_trimmed_inSlabFamilyC`,
`Plank.localStability_trimmed_inSlabFamilyC`), so the same `θ` is used throughout and GWZ Lemma
6.11 is not rerun per slab.

`Ceta` depends only on `C`, `Cstab0`, `ε_s` and `η`, and is fixed before `a`, `b`, `θ`, the slab,
the shift and the box. -/
theorem localAngleConcentration_trimmed_of_slabLocal_poly (C Cstab0 : ℝ≥0) (hC : 1 ≤ C)
    (hCstab0 : 1 ≤ Cstab0) {εs η : ℝ} (hεs : 0 < εs) (hlt : εs < η) :
    ∃ Ceta : ℝ≥0, 0 < Ceta ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι : Type*}
        (Cset Cang Cset' Cang' : ℝ≥0) (S : Slab θ hθ1)
        (s' : Finset ι) (V : ι → Plank a b hab hb1)
        (Y' YS : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (T : (Fin 3 → ℝ) → (Fin 3 → ℤ) → Finset ι)
        (Z : (Fin 3 → ℝ) → (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (Dg : (Fin 3 → ℝ) → Finset (Fin 3 → ℤ)) (A : ℝ),
        0 < a → a < 1 → 0 < b → 0 < θ → a ≤ θ * b → 2 ≤ A →
        Cset + 4 * (2 * Cang + 4 * C) + 8 ≤ Cset' →
        2 * Cang + 4 * C ≤ Cang' →
        (∀ i ∈ s', (Y' i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        Kakeya.HasMaxPlankAngleBound s' Y' V θ C →
        (∀ x ∈ ⋃ i ∈ s', (Y' i).shade, ∀ t ⊆ Kakeya.shadeFibre s' Y' x,
          A⁻¹ * ((Kakeya.shadeFibre s' Y' x).card : ℝ) ≤ (t.card : ℝ) →
            (θ : ℝ) / ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs))
              ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)) →
        (∀ i, (YS i).shade
          = (Y' i).shade ∩ ⋃ i' ∈ inSlabFamilyC Cset Cang s' V S, (Y' i').shade) →
        (∀ sh q, T sh q = (inSlabFamilyC Cset' Cang' s' V S).filter
          (fun i => ((YS i).shade ∩ halfSlabBox S b sh q).Nonempty)) →
        (∀ sh q, ∀ i ∈ T sh q, (Z sh q i).shade = (YS i).shade ∩ halfSlabBox S b sh q) →
        LocalAngleConcentration V θ gridShiftSet Dg T Z Ceta η := by
  classical
  obtain ⟨Ceta, hCetapos, habs⟩ := exists_combined_absorption_poly C Cstab0 hCstab0 hεs hlt
  refine ⟨Ceta, hCetapos, ?_⟩
  intro a b θ hab hb1 hθ1 ι Cset Cang Cset' Cang' S s' V Y' YS T Z Dg A
    ha ha1 hb hθ haθb hA hCset' hCang' hshV hmax hstab hYS hT hZsh
  have hCstab : 1 ≤ (Cstab0 : ℝ) * (a : ℝ) ^ (-εs) := by
    have h1 : (1 : ℝ) ≤ Cstab0 := by exact_mod_cast hCstab0
    have h2 : (1 : ℝ) ≤ (a : ℝ) ^ (-εs) := one_le_rpow_neg_of_lt_one ha ha1 hεs
    have hpow_nonneg : 0 ≤ (a : ℝ) ^ (-εs) := by positivity
    simpa [mul_comm] using mul_le_mul h2 h1 (by norm_num) hpow_nonneg
  have hbudget : ∀ N : ℕ,
    (N : ℝ) ≤ Real.logb 2 (16 * (C : ℝ) * ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs))) + 1 →
    (((8 * ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs))).toNNReal : ℝ≥0) : ENNReal) *
      (((2 * (N + 1 : ℕ) : ℕ) : ℝ≥0) : ENNReal) ≤
    (Ceta : ENNReal) * (a : ENNReal) ^ (-η) :=
    fun N hN => habs ha ha1 N hN
  exact localAngleConcentration_of_saturated_free C hC (inSlabFamilyC Cset' Cang' s' V S) V YS
    gridShiftSet Dg (fun sh q => halfSlabBox S b sh q) T Z A ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs))
    Ceta η ha hb hθ hθ1 hA hCstab hbudget
    (hasMaxPlankAngleBound_trimmed_inSlabFamilyC s' V Y' YS S Cset Cang C Cset' Cang'
       haθb hCset' hCang' hshV hmax hYS)
    (by
      intro sh _ q _
      rw [hT sh q]
      exact Finset.filter_subset _ _)
    (by
      intro sh _ q _ i hi
      exact hZsh sh q i hi)
    (by
      intro sh _ q _ i hi x hx hxR
      rw [hT sh q]
      exact Finset.mem_filter.mpr ⟨hi, ⟨x, hx, hxR⟩⟩)
    (localStability_trimmed_inSlabFamilyC s' V Y' YS S Cset Cang C Cset' Cang' A
       ((Cstab0 : ℝ) * (a : ℝ) ^ (-εs)) haθb hCset' hCang' hshV hmax hYS hstab)

end Plank

end
