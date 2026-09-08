/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.Multiplicity
public import Mathlib.Algebra.Order.Floor.Extended

/-!
# Lean-facing geometric transport for GWZ Lemma 6.13 refinements

Split off from the (over-long) `Kakeya.DimensionThree.Plank.DenseBox`, which keeps the dense-box
*estimate* (`denseBoxEstimate` and its machinery). This companion file collects everything
downstream of that estimate: the shade-restriction operation `ShadedBody.restrictShade`, the
arbitrary-centre ball fullness (`denseBall_arbitraryCentre_fullness`), the shared slab-union
thickened shading with its per-slab union identity, and (in `namespace Kakeya`) the aggregate
multiplicity pigeonhole `multiplicityReductionAlgebra_of_sum`. It is independent of the dense-box
estimates and depends only on the slab geometry.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real

noncomputable section

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*} {τ : Type*}

/-- **Arbitrary-centre fullness from a retained dense grid ball** (G5,
`lem:denseBallArbitraryCentre`).  Let `U` be the ball-refined shading union, every point of which
lies in a retained dense grid ball `B(c, r)` capturing at least a `cdb·a^{4η}` fraction of its own
volume (`hcover`).  Then for every centre `x` whose radius-`r` ball meets `U`, the dilated
radius-`3r` ball at `x` captures the same fraction of `U`.  The dilation factor `3` (`K = 3`) comes
from the triangle inequality `B(c, r) ⊆ B(x, 3r)`, and `|B(x, r)| = |B(c, r)|` is translation
invariance of Lebesgue measure; no ball geometry beyond these is used.  This is exactly item 1 of
Lemma 6.13 for an arbitrary centre, reduced to the lattice-ball density supplied by the dense-ball
refinement. -/
theorem denseBall_arbitraryCentre_fullness {a : ℝ≥0} (cdb : ℝ≥0) (η : ℝ) (r : ℝ)
    (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hcover : ∀ y ∈ U, ∃ c : EuclideanSpace ℝ (Fin 3),
      y ∈ Metric.closedBall c r ∧
      (cdb : ENNReal) * (a : ENNReal) ^ (4 * η) * volume (Metric.closedBall c r)
        ≤ volume (U ∩ Metric.closedBall c r))
    (x : EuclideanSpace ℝ (Fin 3))
    (hmeet : (U ∩ Metric.closedBall x r).Nonempty) :
    (cdb : ENNReal) * (a : ENNReal) ^ (4 * η) * volume (Metric.closedBall x r)
      ≤ volume (U ∩ Metric.closedBall x (3 * r)) := by
  -- Choose a point y in the intersection
  obtain ⟨y, hyU, hyx⟩ := hmeet
  -- y is in the closed ball of radius r around x
  have hyx_dist : dist y x ≤ r := hyx
  -- By hcover, y is in some retained dense ball B(c, r)
  obtain ⟨c, hyc, hdens⟩ := hcover y hyU
  -- hyc: y ∈ Metric.closedBall c r, so dist y c ≤ r
  have hyc_dist : dist y c ≤ r := hyc
  -- Show B(c, r) ⊆ B(x, 3*r) using the triangle inequality
  have hball_sub : Metric.closedBall c r ⊆ Metric.closedBall x (3 * r) := by
    intro z hz
    -- hz: dist z c ≤ r
    have hz_dist : dist z c ≤ r := hz
    -- dist c x ≤ dist c y + dist y x = dist y c + dist y x ≤ r + r = 2*r
    have hcx_dist : dist c x ≤ r + r := by
      calc
        dist c x ≤ dist c y + dist y x := dist_triangle _ _ _
        _ = dist y c + dist y x := by rw [dist_comm c y]
        _ ≤ r + r := add_le_add hyc_dist hyx_dist
    -- dist z x ≤ dist z c + dist c x ≤ r + 2*r = 3*r
    calc
      dist z x ≤ dist z c + dist c x := dist_triangle _ _ _
      _ ≤ r + (r + r) := add_le_add hz_dist hcx_dist
      _ = 3 * r := by ring
  -- Translation invariance: volume (closedBall x r) = volume (closedBall c r)
  have h_vol_eq : volume (Metric.closedBall x r) = volume (Metric.closedBall c r) := by
    calc
      volume (Metric.closedBall x r) = volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3))
          r) := by
        rw [MeasureTheory.Measure.addHaar_closedBall_center]
      _ = volume (Metric.closedBall c r) := by
        rw [← MeasureTheory.Measure.addHaar_closedBall_center]
  -- Chain the inequalities
  calc
    (cdb : ENNReal) * (a : ENNReal) ^ (4 * η) * volume (Metric.closedBall x r)
        = (cdb : ENNReal) * (a : ENNReal) ^ (4 * η) * volume (Metric.closedBall c r) := by
      rw [h_vol_eq]
    _ ≤ volume (U ∩ Metric.closedBall c r) := hdens
    _ ≤ volume (U ∩ Metric.closedBall x (3 * r)) := by
      -- apply measure_mono to the inclusion (U ∩ B(c,r)) ⊆ (U ∩ B(x,3r))
      apply measure_mono
      exact Set.inter_subset_inter_right U hball_sub

/-! ## Shared slab-union thickened shading (`def:sharedSlabThickenedShadingDilation`) -/

open Classical in
/-- The shared slab thickened shading on a fixed dilation of the representative.  This is the
paper-facing carrier used by Lemma 6.13; the dilation records the harmless fixed comparability
loss of the Lean plank model.

The active representative index type `τ` is arbitrary: only the slab assignment `slabOf` and the
plank-to-representative map `repr` are used combinatorially, while the geometry enters solely
through the realization map `anchor : τ → EnsemblePrism`.  Lemma 6.13 instantiates
`τ := Plank.ThickenedPlank θ b hθ1 hb1` and `anchor := fun Q => Q.toPrismNDim`, which keeps the
active family typed instead of erased to `EnsemblePrism`. -/
noncomputable def sharedSlabThickenedShadingDilation {τ σ : Type*} (Cbox : ℝ≥0)
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (anchor : τ → EnsemblePrism)
    (repr : ι → τ) (slabOf : τ → σ)
    (Q : τ) : ShadedBody (EuclideanSpace ℝ (Fin 3)) where
  toConvexSpaceBody := ((anchor Q).dilation Cbox).toConvexSpaceBody
  shade := (((anchor Q).dilation Cbox).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
    ⋃ i ∈ s'.filter (fun i => slabOf (repr i) = slabOf Q), (Y' i).shade
  measurableSet_shade := ((anchor Q).dilation Cbox).toConvexSpaceBody.isCompact.measurableSet.inter
    (MeasurableSet.biUnion (s'.filter (fun i => slabOf (repr i) = slabOf Q)).countable_toSet
      fun i _ => (Y' i).measurableSet_shade)
  shade_subset := Set.inter_subset_left

open Classical in
@[simp] theorem sharedSlabThickenedShadingDilation_carrier {τ σ : Type*} (Cbox : ℝ≥0)
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (anchor : τ → EnsemblePrism) (repr : ι → τ) (slabOf : τ → σ) (Q : τ) :
    ((sharedSlabThickenedShadingDilation Cbox s' Y' anchor repr slabOf Q).carrier :
      Set (EuclideanSpace ℝ (Fin 3))) = ((anchor Q).dilation Cbox).carrier := rfl

open Classical in
@[simp] theorem sharedSlabThickenedShadingDilation_shade {τ σ : Type*} (Cbox : ℝ≥0)
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (anchor : τ → EnsemblePrism) (repr : ι → τ) (slabOf : τ → σ) (Q : τ) :
    (sharedSlabThickenedShadingDilation Cbox s' Y' anchor repr slabOf Q).shade =
      (((anchor Q).dilation Cbox).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        ⋃ i ∈ s'.filter (fun i => slabOf (repr i) = slabOf Q), (Y' i).shade := rfl

/-! ## Shading transport (`def:plankReductionAssemblyAPI`) -/

end Plank

namespace Kakeya

open MeasureTheory
open scoped NNReal

/-- Abstract finite-sum ratio pigeonhole in `ENNReal`, the arithmetic core of
`multiplicityReductionAlgebra_of_sum`.  Given a finite nonempty index set `𝒮`, nonnegative
"masses" `MS` and "denominators" `uS` with `∑ MS = M`, `c · ∑ uS ≤ u`, all quantities finite, and
the degeneracy compatibility `uS S = 0 → MS S = 0`, some `S` satisfies
`M / u ≤ c⁻¹ · (MS S / uS S)`.
Isolated from the measure-theoretic wrapper so the ENNReal manipulation elaborates cleanly. -/
private theorem ennreal_ratio_pigeonhole {σ : Type*} (𝒮 : Finset σ) (h𝒮 : 𝒮.Nonempty)
    (c : ℝ≥0) (hc : 0 < c) (M u : ENNReal) (MS uS : σ → ENNReal)
    (_hMtop : M ≠ ⊤) (hutop : u ≠ ⊤) (hStop : ∀ S ∈ 𝒮, uS S ≠ ⊤)
    (hM : ∑ S ∈ 𝒮, MS S = M) (hu : (c : ENNReal) * (∑ S ∈ 𝒮, uS S) ≤ u)
    (hdeg : ∀ S ∈ 𝒮, uS S = 0 → MS S = 0) :
    ∃ S ∈ 𝒮, M / u ≤ (c : ENNReal)⁻¹ * (MS S / uS S) := by
  have hc0 : (c : ENNReal) ≠ 0 := by exact_mod_cast hc.ne'
  have hctop : (c : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  by_cases hu0 : u = 0
  · -- case u = 0
    have hsum0 : (c : ENNReal) * (∑ S ∈ 𝒮, uS S) = 0 := by
      rw [hu0] at hu
      have hpos : 0 ≤ (c : ENNReal) * (∑ S ∈ 𝒮, uS S) := by positivity
      simpa using le_antisymm hu hpos
    have hsumuS0 : ∑ S ∈ 𝒮, uS S = 0 := by
      rcases mul_eq_zero.mp hsum0 with (hc0' | hsumuS0)
      · exact absurd hc0' hc0
      · exact hsumuS0
    have h_all_uS0 : ∀ S ∈ 𝒮, uS S = 0 := by
      simpa [Finset.sum_eq_zero_iff] using hsumuS0
    have h_all_MS0 : ∀ S ∈ 𝒮, MS S = 0 := fun S hS => hdeg S hS (h_all_uS0 S hS)
    have hM0 : M = 0 := by
      calc
        M = ∑ S ∈ 𝒮, MS S := by symm; exact hM
        _ = 0 := Finset.sum_eq_zero h_all_MS0
    rw [hM0, hu0]
    obtain ⟨S, hS⟩ := h𝒮
    refine ⟨S, hS, ?_⟩
    simp
  · -- u ≠ 0
    by_cases hM0 : M = 0
    · rw [hM0]
      obtain ⟨S, hS⟩ := h𝒮
      refine ⟨S, hS, ?_⟩
      simp
    · -- both u ≠ 0 and M ≠ 0
      by_contra hcon
      push Not at hcon
      set 𝒮plus := 𝒮.filter (fun S => 0 < uS S) with h𝒮plusdef
      have h𝒮plusne : 𝒮plus.Nonempty := by
        by_contra h𝒮plusempty
        have h𝒮plusempty' : ∀ S, S ∉ 𝒮plus := fun S hS => h𝒮plusempty ⟨S, hS⟩
        have h_all_uS0 : ∀ S ∈ 𝒮, uS S = 0 := by
          intro S hS
          have h_notpos : ¬ 0 < uS S := by
            intro hpos
            apply h𝒮plusempty' S
            exact Finset.mem_filter.mpr ⟨hS, hpos⟩
          exact le_antisymm (le_of_not_gt h_notpos) (by positivity : 0 ≤ uS S)
        have h_all_MS0 : ∀ S ∈ 𝒮, MS S = 0 := fun S hS => hdeg S hS (h_all_uS0 S hS)
        have hM0' : M = 0 := by
          calc
            M = ∑ S ∈ 𝒮, MS S := by symm; exact hM
            _ = 0 := Finset.sum_eq_zero h_all_MS0
        exact hM0 hM0'
      have hlt : ∀ S ∈ 𝒮plus, MS S * u < (c : ENNReal) * M * uS S := by
        intro S hS
        obtain ⟨hSmem, hyS⟩ := Finset.mem_filter.mp hS
        have hyStop : uS S ≠ ⊤ := hStop S hSmem
        have h1 : (c : ENNReal)⁻¹ * (MS S / uS S) < M / u := hcon S hSmem
        -- Step 1: apply ENNReal.lt_div_iff_mul_lt to get ((c⁻¹*(MS S / uS S))*u < M)
        have h1mul : ((c : ENNReal)⁻¹ * (MS S / uS S)) * u < M := by
          rw [ENNReal.lt_div_iff_mul_lt (Or.inl hu0) (Or.inl hutop)] at h1
          exact h1
        -- Step 2: multiply by c on the left
        have h2 : (c : ENNReal) * (((c : ENNReal)⁻¹ * (MS S / uS S)) * u) < (c : ENNReal) * M :=
          ENNReal.mul_lt_mul_right hc0 hctop h1mul
        -- Step 3: simplify LHS
        have h3 : (c : ENNReal) * (((c : ENNReal)⁻¹ * (MS S / uS S)) * u) = (MS S / uS S) * u := by
          calc
            (c : ENNReal) * (((c : ENNReal)⁻¹ * (MS S / uS S)) * u)
                = ((c : ENNReal) * (c : ENNReal)⁻¹) * ((MS S / uS S) * u) := by
                  simp [mul_assoc, mul_comm, mul_left_comm]
            _ = 1 * ((MS S / uS S) * u) := by rw [ENNReal.mul_inv_cancel hc0 hctop]
            _ = (MS S / uS S) * u := by simp
        rw [h3] at h2
        -- h2: (MS S / uS S) * u < (c : ENNReal) * M
        -- Step 4: rewrite (MS S / uS S) * u = (MS S * u) / uS S
        have h4 : (MS S / uS S) * u = (MS S * u) / uS S := by
          simp [ENNReal.div_eq_inv_mul, mul_assoc, mul_comm]
        rw [h4] at h2
        -- h2: (MS S * u) / uS S < (c : ENNReal) * M
        -- Step 5: apply ENNReal.div_lt_iff
        rw [ENNReal.div_lt_iff (Or.inl hyS.ne') (Or.inl hyStop)] at h2
        -- h2: MS S * u < ((c : ENNReal) * M) * uS S
        simpa [mul_assoc] using h2
      have hsum_raw : ∑ S ∈ 𝒮plus, (MS S * u) < ∑ S ∈ 𝒮plus, ((c : ENNReal) * M * uS S) :=
        ENNReal.sum_lt_sum_of_nonempty h𝒮plusne hlt
      have hsum_lt : (∑ S ∈ 𝒮plus, MS S) * u < (c : ENNReal) * M * (∑ S ∈ 𝒮plus, uS S) := by
        simpa [Finset.sum_mul, Finset.mul_sum, mul_assoc] using hsum_raw
      have h_sumMS : ∑ S ∈ 𝒮plus, MS S = M := by
        calc
          ∑ S ∈ 𝒮plus, MS S = ∑ S ∈ 𝒮, MS S :=
            Finset.sum_subset (Finset.filter_subset (fun S => 0 < uS S) 𝒮) (by
              intro S hS hSnot
              have h_notpos : ¬ 0 < uS S := by
                intro hpos; apply hSnot; exact Finset.mem_filter.mpr ⟨hS, hpos⟩
              have h_uS0 : uS S = 0 := le_antisymm (le_of_not_gt h_notpos) (by positivity : 0 ≤
                  uS S)
              exact hdeg S hS h_uS0)
          _ = M := hM
      have h_sumuS : ∑ S ∈ 𝒮plus, uS S = ∑ S ∈ 𝒮, uS S :=
        Finset.sum_subset (Finset.filter_subset (fun S => 0 < uS S) 𝒮) (by
          intro S hS hSnot
          have h_notpos : ¬ 0 < uS S := by
            intro hpos; apply hSnot; exact Finset.mem_filter.mpr ⟨hS, hpos⟩
          exact le_antisymm (le_of_not_gt h_notpos) (by positivity : 0 ≤ uS S))
      have hcontra : M * u < M * u := by
        calc
          M * u = (∑ S ∈ 𝒮plus, MS S) * u := by rw [h_sumMS]
          _ < (c : ENNReal) * M * (∑ S ∈ 𝒮plus, uS S) := hsum_lt
          _ = (c : ENNReal) * M * (∑ S ∈ 𝒮, uS S) := by rw [h_sumuS]
          _ = M * ((c : ENNReal) * (∑ S ∈ 𝒮, uS S)) := by
            simp [mul_comm, mul_left_comm]
          _ ≤ M * u := mul_le_mul_right hu M
      exact lt_irrefl _ hcontra

/-- **Aggregate multiplicity reduction** (G10, `lem:geometryAggregateMultiplicity`).  From the
aggregate slab mass comparison `c_ov · ∑_S |U(P^ass_S, Y')| ≤ |U(s', Y')|` and the fact that the
assigned families partition the total shading mass (`∑_S ∑_{i∈P^ass_S} |Y'_i| = ∑_{i∈s'} |Y'_i|`),
a finite-sum pigeonhole selects one slab index `S ∈ 𝒮` whose assigned family controls the
multiplicity:
`μ(s', Y') ≤ c_ov⁻¹ · μ(P^ass_S, Y')`.
No pointwise per-slab overlap inequality is assumed for every slab. -/
theorem multiplicityReductionAlgebra_of_sum {ι σ : Type*}
    (c_ov : ℝ≥0) (hc_ov : 0 < c_ov)
    (𝒮 : Finset σ) (h𝒮 : 𝒮.Nonempty)
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Pass : σ → Finset ι)
    (hpart : ∑ S ∈ 𝒮, (∑ i ∈ Pass S, volume (Y' i).shade) = ∑ i ∈ s', volume (Y' i).shade)
    (hov : (c_ov : ENNReal) * (∑ S ∈ 𝒮, volume (⋃ i ∈ Pass S, (Y' i).shade))
              ≤ volume (⋃ i ∈ s', (Y' i).shade)) :
    ∃ S ∈ 𝒮, ShadedBody.multiplicity s' Y'
        ≤ (c_ov : ENNReal)⁻¹ * ShadedBody.multiplicity (Pass S) Y' := by
  set M := ∑ i ∈ s', volume (Y' i).shade with hM
  set u := volume (⋃ i ∈ s', (Y' i).shade) with hu
  set MS := fun S : σ => ∑ i ∈ Pass S, volume (Y' i).shade with hMS
  set uS := fun S : σ => volume (⋃ i ∈ Pass S, (Y' i).shade) with huS
  have hMtop : M ≠ ⊤ := by
    dsimp [M]
    apply (ENNReal.sum_ne_top.mpr ?_)
    intro i hi
    have hfin : volume ((Y' i).carrier) ≠ ⊤ := (Y' i).isCompact.measure_ne_top
    have hvol : volume ((Y' i).shade) ≤ volume ((Y' i).carrier) :=
      measure_mono ((Y' i).shade_subset)
    exact ne_top_of_le_ne_top hfin hvol
  have hutop : u ≠ ⊤ := ShadedBody.volume_iUnion_shade_ne_top s' Y'
  have hStop : ∀ S ∈ 𝒮, uS S ≠ ⊤ := fun S hS =>
    ShadedBody.volume_iUnion_shade_ne_top (Pass S) Y'
  have hdeg : ∀ S ∈ 𝒮, uS S = 0 → MS S = 0 := by
    intro S hS hzero
    have hzero' : ∀ i ∈ Pass S, volume ((Y' i).shade) = 0 := by
      intro i hi
      have hzero_uS : volume (⋃ i ∈ Pass S, (Y' i).shade) = 0 := by
        simpa [uS] using hzero
      have hsub : (Y' i).shade ⊆ ⋃ i ∈ Pass S, (Y' i).shade :=
        Finset.subset_set_biUnion_of_mem (f := fun j => (Y' j).shade) hi
      have hvol : volume ((Y' i).shade) ≤ volume (⋃ i ∈ Pass S, (Y' i).shade) :=
        measure_mono hsub
      rw [hzero_uS] at hvol
      exact hvol.antisymm (by positivity)
    simp [hMS, Finset.sum_eq_zero hzero']
  have hM : ∑ S ∈ 𝒮, MS S = M := by
    dsimp [M, MS]
    simpa using hpart
  have hu : (c_ov : ENNReal) * (∑ S ∈ 𝒮, uS S) ≤ u := by
    dsimp [uS, u]
    simpa using hov
  have h_pigeonhole := ennreal_ratio_pigeonhole 𝒮 h𝒮 c_ov hc_ov M u MS uS hMtop hutop hStop hM
      hu hdeg
  rcases h_pigeonhole with ⟨S, hS, hineq⟩
  refine ⟨S, hS, ?_⟩
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div]
  simpa [M, u, MS, uS] using hineq

end Kakeya

end
